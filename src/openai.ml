let api_key =
  lazy
    ( match Sys.getenv_opt "OPENAI_API_KEY" with
    | Some key -> key
    | None -> failwith "Environment variable OPENAI_API_KEY not found" )

let model =
  Option.default "gpt-4o-mini-2024-07-18" (Sys.getenv_opt "LCOQ_MODEL")

module Types = struct
  type chat_message = {role : string; content : string}
  [@@deriving yojson] [@@yojson.allow_extra_fields]

  type chat_request =
    { model : string
    ; messages : chat_message list
    ; logprobs : bool
    ; frequency_penalty : float option [@yojson.option]
    ; n : int }
  [@@deriving yojson]

  type response_choice =
    { index : int
    ; message : chat_message
    ; finish_reason : string
    ; logprobs : chat_logprobs }
  [@@deriving yojson] [@@yojson.allow_extra_fields]

  and chat_logprobs = {content : token_logprob list}
  [@@deriving yojson] [@@yojson.allow_extra_fields]

  and token_logprob = {token : string; logprob : float}
  [@@deriving yojson] [@@yojson.allow_extra_fields]

  type chat_usage =
    { prompt_tokens : int
    ; completion_tokens : int
    ; total_tokens : int
    ; prompt_tokens_details : prompt_tokens_details }
  [@@deriving yojson] [@@yojson.allow_extra_fields]

  and prompt_tokens_details = {cached_tokens : int}
  [@@deriving yojson] [@@yojson.allow_extra_fields]

  type chat_response = {choices : response_choice list; usage : chat_usage}
  [@@deriving yojson] [@@yojson.allow_extra_fields]
end

open Types

let ctx_log_f = ref None

let ctx_log s =
  match !ctx_log_f with
  | None -> ()
  | Some f -> f s

let log_usage resp =
  yojson_of_chat_usage resp.usage |> Yojson.Safe.to_string |> ctx_log

let buffered_handle () =
  Utils.curl_global_init () ;
  let handle = Utils.curl_make_handle () in
  let resp_buf = Buffer.create 4096 in
  Curl.set_writefunction handle (fun resp ->
      Buffer.add_string resp_buf resp ;
      String.length resp ) ;
  Curl.set_url handle "https://api.openai.com/v1/chat/completions" ;
  Curl.set_httpheader handle
    [ "Content-Type: application/json"
    ; "Authorization: Bearer " ^ Lazy.force api_key ] ;
  (handle, resp_buf)

let chat_complete_raw =
  let handle = Lazy.from_fun buffered_handle in
  fun n_choices messages ->
    assert (n_choices > 0) ;
    let handle, buf = Lazy.force handle in
    let body =
      { model
      ; messages
      ; logprobs = true
      ; frequency_penalty = Some 0.1
      ; n = n_choices }
      |> yojson_of_chat_request |> Yojson.Safe.to_string
    in
    Curl.set_postfields handle body ;
    let rec try_post () =
      try
        Curl.perform handle ;
        let s = Buffer.contents buf in
        Buffer.clear buf ; s
      with Curl.CurlException (code, errno, info) ->
        ctx_log
          ( "WARNING: CURL EXCEPTION " ^ Curl.strerror code ^ " "
          ^ string_of_int errno ^ " " ^ info ) ;
        Buffer.clear buf ;
        try_post ()
    in
    try_post ()

exception UnexpectedResponse of string

let system_message =
  "You are a helpful assistant that completes a Coq proof. The context given \
   will have accessible definitions, theorems and other Coq sentences that \
   might be useful in the proof. The proof obligation shown at the end of the \
   context will have multiple goals separated by \'#\'s. Hypothesis are shown \
   before \'=\'s within each goal. You will be DIRECTLY interacting with Coq, \
   so ONLY output the corresponding tactics to complete the proof. Also try \
   ONLY output one tactic each time."

let system_tokens = lazy (Utils.count_tokens system_message)

let goal_message ?(short = false) goals =
  let string_of_goal Serutils.{hyps; goal} =
    hyps ^ "\n" ^ String.make 16 '=' ^ "\n" ^ goal
  in
  if short
  then string_of_goal (List.hd goals)
  else
    goals |> List.map string_of_goal
    |> String.concat ("\n" ^ String.make 16 '#' ^ "\n")

let gptf_messages cache_context context goals =
  (* gpt-4o variants: 128k tokens (1k for tolerance) *)
  let token_limit = 127_000 - Lazy.force system_tokens in
  let context = Option.default "" cache_context ^ context in
  let context_tokens = Utils.count_tokens context in
  let goal_msg = goal_message goals in
  let goal_msg_short = goal_message ~short:true goals in
  let goal_tokens = Utils.count_tokens goal_msg in
  let user_tokens_short = Utils.count_tokens goal_msg_short in
  if context_tokens + goal_tokens <= token_limit
  then
    Some
      [ {role = "system"; content = system_message}
      ; {role = "user"; content = context}
      ; {role = "user"; content = goal_msg} ]
  else if context_tokens + user_tokens_short <= token_limit
  then
    Some
      [ {role = "system"; content = system_message}
      ; {role = "user"; content = context}
      ; {role = "user"; content = goal_msg_short} ]
  else
    let diff = context_tokens + user_tokens_short - token_limit in
    if diff <= context_tokens
    then
      let context_len = String.length context in
      let offset = min context_len (diff * 4) in
      Some
        [ {role = "system"; content = system_message}
        ; { role = "user"
          ; content = String.sub context offset (context_len - offset) }
        ; {role = "user"; content = goal_msg_short} ]
    else None (* even first goal is too long *)

let chat_complete n_choices messages =
  let resp = chat_complete_raw n_choices messages in
  try
    let json = Yojson.Safe.from_string resp in
    let resp = chat_response_of_yojson json in
    log_usage resp ; resp
  with _ -> raise (UnexpectedResponse resp)

let chat_complete_choices n_choices messages =
  let {choices; _} = chat_complete n_choices messages in
  List.map
    (fun c ->
      ( c.message.content
      , List.fold_left (fun s l -> s +. l.logprob) 0. c.logprobs.content ) )
    choices

let chat_complete_str messages =
  let {choices; _} = chat_complete 1 messages in
  match choices with
  | [c] -> c.message.content
  | _ -> failwith "Unexpected number of assistant responses"

module Reasoning = struct
  let system_message =
    "You are a helpful assistant that completes a Coq proof. The context given \
     will have accessible definitions, theorems and other Coq sentences that \
     might be useful in the proof. The proof obligation shown at the end of \
     the context will have multiple goals separated by \'#\'s. Hypothesis are \
     shown before \'=\'s within each goal. You will be DIRECTLY interacting \
     with Coq, so ONLY output the corresponding tactics to complete the proof."

  let system_tokens = lazy (Utils.count_tokens system_message)

  let truncate_messages user_msgs =
    (* o1-mini: 128k tokens (1k for tolerance) *)
    let token_limit = 127_000 - Lazy.force system_tokens in
    let msgs_acc_len =
      snd
      @@ List.fold_right
           (fun (msg : chat_message) (acc, l) ->
             let acc = acc + Utils.count_tokens msg.content in
             (acc, (acc, msg) :: l) )
           user_msgs (0, [])
    in
    let msgs =
      Utils.drop_until (fun (acc, _) -> acc <= token_limit) msgs_acc_len
      |> List.map snd
    in
    match msgs with
    | [] -> None
    | _ -> Some ({role = "system"; content = system_message} :: msgs)
end
