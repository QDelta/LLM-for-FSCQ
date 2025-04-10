let google_api_key =
  lazy
    ( match Sys.getenv_opt "GOOGLE_API_KEY" with
    | Some key -> key
    | None -> failwith "Environment variable GOOGLE_API_KEY not found" )

let lcoq_model_name =
  "models/"
  ^ Option.default "gemini-1.5-flash-002" (Sys.getenv_opt "LCOQ_MODEL")

module Types = struct
  type part = {text : string} [@@deriving yojson]

  type system_instruction = {parts : part list} [@@deriving yojson]

  type content = {parts : part list; role : string}
  [@@deriving yojson] [@@yojson.allow_extra_fields]

  type request =
    { cached_content : string option [@key "cachedContent"] [@yojson.option]
    ; system_instruction : system_instruction option
          [@key "systemInstruction"] [@yojson.option]
    ; contents : content list
    ; generation_config : generation_config [@key "generationConfig"] }
  [@@deriving yojson]

  and generation_config =
    { candidate_count : int [@key "candidateCount"]
    ; frequency_penalty : float [@key "frequencyPenalty"] }
  [@@deriving yojson]

  type candidate =
    { content : content option [@yojson.option]
    ; finish_reason : string [@key "finishReason"]
    ; logprob : float option [@key "avgLogprobs"] [@yojson.option] }
  [@@deriving yojson] [@@yojson.allow_extra_fields]

  type usage =
    { input_tokens : int [@key "promptTokenCount"]
    ; output_tokens : int [@key "candidatesTokenCount"]
    ; total_tokens : int [@key "totalTokenCount"]
    ; cached_tokens : int [@default 0] [@key "cachedContentTokenCount"] }
  [@@deriving yojson] [@@yojson.allow_extra_fields]

  type response =
    {candidates : candidate list; usage : usage [@key "usageMetadata"]}
  [@@deriving yojson] [@@yojson.allow_extra_fields]

  type cache_request =
    { model : string
    ; system_instruction : system_instruction [@key "systemInstruction"]
    ; contents : content list [@default []] [@yojson_drop_default ( = )]
    ; ttl : string }
  [@@deriving yojson]

  type cache_response =
    {name : string; usage : cache_usage [@key "usageMetadata"]}
  [@@deriving yojson] [@@yojson.allow_extra_fields]

  and cache_usage = {tokens : int [@key "totalTokenCount"]}
  [@@deriving yojson] [@@yojson.allow_extra_fields]
end

open Types

let buffered_handle url_param =
  Utils.curl_global_init () ;
  let handle = Utils.curl_make_handle () in
  let resp_buf = Buffer.create 4096 in
  Curl.set_writefunction handle (fun resp ->
      Buffer.add_string resp_buf resp ;
      String.length resp ) ;
  Curl.set_url handle
    ( "https://generativelanguage.googleapis.com/v1beta/" ^ url_param ^ "?key="
    ^ Lazy.force google_api_key ) ;
  Curl.set_httpheader handle ["Content-Type: application/json"] ;
  (handle, resp_buf)

let ctx_log_f = ref None

let ctx_log s =
  match !ctx_log_f with
  | None -> ()
  | Some f -> f s

let wait_time =
  lazy
    (let re = Re.(compile @@ seq [rep any; str "flash"]) in
     let is_flash =
       match Re.exec_opt re lcoq_model_name with
       | None -> false
       | Some _ -> true
     in
     (* 2000 RPM for flash and 1000 RPM for pro *)
     if is_flash then 0.03 else 0.06 )

let rec rate_limited_perform handle buf =
  try
    Curl.perform handle ;
    if Curl.get_responsecode handle = 429
    then (
      let wait_time = Lazy.force wait_time in
      Buffer.clear buf ;
      Unix.sleepf wait_time ;
      ctx_log @@ "RATE LIMITED, WAIT FOR " ^ string_of_float wait_time
      ^ " SECONDS" ;
      rate_limited_perform handle buf )
    else
      let s = Buffer.contents buf in
      Buffer.clear buf ; s
  with Curl.CurlException (code, errno, info) ->
    ctx_log
      ( "WARNING: CURL EXCEPTION " ^ Curl.strerror code ^ " "
      ^ string_of_int errno ^ " " ^ info ) ;
    Buffer.clear buf ;
    rate_limited_perform handle buf

let log_usage (resp : response) =
  yojson_of_usage resp.usage |> Yojson.Safe.to_string |> ctx_log

let log_cache_usage (resp : cache_response) =
  yojson_of_cache_usage resp.usage |> Yojson.Safe.to_string |> ctx_log

let log_cache_storage tokens create_at expire_at delete_at =
  `Assoc
    [ ("tokenCount", `Int tokens)
    ; ("createTime", `Float create_at)
    ; ("expireTime", `Float expire_at)
    ; ("deleteTime", `Float delete_at) ]
  |> Yojson.Basic.to_string |> ctx_log

type cache_handle =
  { model : string
  ; name : string
  ; text : string
  ; tokens : int
  ; create_at : float
  ; expire_at : float }

let create_cache =
  let handle = lazy (buffered_handle "cachedContents") in
  fun ~model ~text ->
    let handle, buf = Lazy.force handle in
    let req =
      { model
      ; system_instruction = {parts = [{text = Openai.system_message}]}
      ; contents =
          (if text = "" then [] else [{parts = [{text}]; role = "user"}])
      ; ttl = "120s" }
    in
    let body = Yojson.Safe.to_string @@ yojson_of_cache_request req in
    Curl.set_postfields handle body ;
    let post_time = Unix.gettimeofday () in
    (* Curl.perform handle ; *)
    let resp = rate_limited_perform handle buf in
    let resp = cache_response_of_yojson @@ Yojson.Safe.from_string resp in
    let cache_handle =
      { model
      ; name = resp.name
      ; text
      ; tokens = resp.usage.tokens
      ; create_at = post_time
      ; expire_at = post_time +. 120. }
    in
    log_cache_usage resp ; cache_handle

let auto_refresh cache_handle =
  let curr_time = Unix.gettimeofday () in
  if curr_time +. 30. < cache_handle.expire_at
  then (* we are safe *) cache_handle
  else begin
    if curr_time +. 5. < cache_handle.expire_at
    then (
      (* update current cache *)
      let handle, buf = buffered_handle cache_handle.name in
      Curl.set_postfields handle "{\"ttl\":\"120s\"}" ;
      Curl.set_customrequest handle "PATCH" ;
      let post_time = Unix.gettimeofday () in
      (* Curl.perform handle ; *)
      let resp = rate_limited_perform handle buf in
      let resp = cache_response_of_yojson @@ Yojson.Safe.from_string resp in
      {cache_handle with name = resp.name; expire_at = post_time +. 120.} )
    else begin
      (* create a new cache *)
      log_cache_storage cache_handle.tokens cache_handle.create_at
        cache_handle.expire_at cache_handle.expire_at ;
      create_cache ~model:cache_handle.model ~text:cache_handle.text
    end
  end

let delete_cache cache_handle =
  let curr_time = Unix.gettimeofday () in
  if curr_time +. 5. < cache_handle.expire_at
  then (
    let handle, buf = buffered_handle cache_handle.name in
    Curl.set_customrequest handle "DELETE" ;
    let post_time = Unix.gettimeofday () in
    rate_limited_perform handle buf |> String.trim |> ctx_log ;
    log_cache_storage cache_handle.tokens cache_handle.create_at
      cache_handle.expire_at post_time )
  else
    log_cache_storage cache_handle.tokens cache_handle.create_at
      cache_handle.expire_at cache_handle.expire_at

let complete_raw =
  let handle = lazy (buffered_handle @@ lcoq_model_name ^ ":generateContent") in
  fun n cached_content system_instruction contents ->
    assert (n > 0) ;
    let handle, buf = Lazy.force handle in
    let body =
      { cached_content
      ; system_instruction
      ; contents
      ; generation_config = {candidate_count = n; frequency_penalty = 0.1} }
      |> yojson_of_request |> Yojson.Safe.to_string
    in
    Curl.set_postfields handle body ;
    rate_limited_perform handle buf

let global_cache_handle = ref None

let cleanup () =
  match !global_cache_handle with
  | None -> ()
  | Some handle -> delete_cache handle

type message =
  { cache_handle : cache_handle option
  ; system_instruction : system_instruction option
  ; contents : content list }

let message_no_cache context token_limit goal_msg goal_msg_short goal_tokens
    goal_tokens_short : message option =
  let token_limit = token_limit - Lazy.force Openai.system_tokens in
  let context_tokens = Utils.count_tokens context in
  if context_tokens + goal_tokens <= token_limit
  then
    Some
      { cache_handle = None
      ; system_instruction = Some {parts = [{text = Openai.system_message}]}
      ; contents =
          [ {parts = [{text = context}]; role = "user"}
          ; {parts = [{text = goal_msg}]; role = "user"} ] }
  else if context_tokens + goal_tokens_short <= token_limit
  then
    Some
      { cache_handle = None
      ; system_instruction = Some {parts = [{text = Openai.system_message}]}
      ; contents =
          [ {parts = [{text = context}]; role = "user"}
          ; {parts = [{text = goal_msg_short}]; role = "user"} ] }
  else
    let diff = context_tokens + goal_tokens_short - token_limit in
    if diff <= context_tokens
    then
      let context_len = String.length context in
      let offset = min context_len (diff * 4) in
      Some
        { cache_handle = None
        ; system_instruction = Some {parts = [{text = Openai.system_message}]}
        ; contents =
            [ { parts =
                  [{text = String.sub context offset (context_len - offset)}]
              ; role = "user" }
            ; {parts = [{text = goal_msg_short}]; role = "user"} ] }
    else None

(* assume `cache_context` is append-only *)
let message cache_context context goals : message option =
  (* 1m tokens (1k for tolerance) *)
  let token_limit = 999_000 in
  (* let token_limit = 127_000 in *)
  let cache_handle =
    match (cache_context, !global_cache_handle) with
    | None, None ->
        let handle = create_cache ~model:lcoq_model_name ~text:"" in
        global_cache_handle := Some handle ;
        handle
    | Some text, None ->
        let handle =
          let tokens = Utils.count_tokens text in
          create_cache ~model:lcoq_model_name
            ~text:(if tokens <= token_limit then text else "")
        in
        global_cache_handle := Some handle ;
        handle
    | None, Some cache_handle ->
        cache_handle (* the cache only has system prompt *)
    | Some text, Some cache_handle ->
        if text = cache_handle.text
        then cache_handle
        else begin
          if Utils.count_tokens text <= token_limit
          then (
            delete_cache cache_handle ;
            let handle = create_cache ~model:lcoq_model_name ~text in
            global_cache_handle := Some handle ;
            handle )
          else cache_handle (* the cache only has system prompt *)
        end
  in
  let goal_msg = Openai.goal_message goals in
  let goal_msg_short = Openai.goal_message ~short:true goals in
  let goal_tokens = Utils.count_tokens goal_msg in
  let goal_tokens_short = Utils.count_tokens goal_msg_short in
  let context_tokens = Utils.count_tokens context in
  let system_tokens = cache_handle.tokens in
  if system_tokens + context_tokens + goal_tokens <= token_limit
  then
    Some
      { cache_handle = Some cache_handle
      ; system_instruction = None
      ; contents =
          [ {parts = [{text = context}]; role = "user"}
          ; {parts = [{text = goal_msg}]; role = "user"} ] }
  else if system_tokens + context_tokens + goal_tokens_short <= token_limit
  then
    Some
      { cache_handle = Some cache_handle
      ; system_instruction = None
      ; contents =
          [ {parts = [{text = context}]; role = "user"}
          ; {parts = [{text = goal_msg_short}]; role = "user"} ] }
  else
    message_no_cache context token_limit goal_msg goal_msg_short goal_tokens
      goal_tokens_short

exception UnexpectedResponse of string

let complete_choices n_choices {cache_handle; system_instruction; contents} =
  let merge_parts parts =
    List.fold_right (fun (p : part) s -> p.text ^ s) parts ""
  in
  let cache_name =
    match cache_handle with
    | None -> None
    | Some cache_handle ->
        let new_handle = auto_refresh cache_handle in
        global_cache_handle := Some new_handle ;
        Some new_handle.name
  in
  let resp = complete_raw n_choices cache_name system_instruction contents in
  try
    let json = Yojson.Safe.from_string resp in
    let resp = response_of_yojson json in
    log_usage resp ;
    List.filter_map
      (function
        | {content = Some content; logprob = Some logprob; _} ->
            Some (merge_parts content.parts, logprob)
        | _ -> None )
      resp.candidates
  with _ -> raise (UnexpectedResponse resp)
