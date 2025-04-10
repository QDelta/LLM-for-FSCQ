open Utils
open Serutils

module type MODEL = sig
  type message

  exception UnexpectedResponse of string

  val register_log : (string -> unit) -> unit

  val generate_message :
    string option -> string -> proof_ctx list -> message option

  val generate_choices : int -> message -> (string * float) list

  val cleanup : unit -> unit
end

module OPENAI_MODEL : MODEL = struct
  type message = Openai.Types.chat_message list

  exception UnexpectedResponse = Openai.UnexpectedResponse

  let register_log logf = Openai.ctx_log_f := Some logf

  let generate_message = Openai.gptf_messages

  let generate_choices = Openai.chat_complete_choices

  let cleanup () = ()
end

module GEMINI_MODEL : MODEL = struct
  type message = Gemini.message

  exception UnexpectedResponse = Gemini.UnexpectedResponse

  let register_log logf = Gemini.ctx_log_f := Some logf

  let generate_message = Gemini.message

  let generate_choices = Gemini.complete_choices

  let cleanup = Gemini.cleanup
end

type goal_node =
  { goal : proof_ctx list
  ; parent_tactic : tactic_node option
  ; mutable tactic_choices : tactic_node list
  ; state : State.t }

and tactic_node =
  { tactic : string
  ; depth : int
  ; logprob : float (* cumulative logprob *)
  ; parent_goal : goal_node
  ; subgoal : goal_node }

let cursor : tactic_node option ref = ref None

let appeared_goals = Hashtbl.create 32

let string_of_tree goal =
  let rec pp_goal goal =
    let s_ctx =
      goal.goal
      |> List.map (fun {hyps; goal} ->
             hyps ^ "\n" ^ String.make 16 '=' ^ "\n" ^ goal )
      |> String.concat ("\n" ^ String.make 16 '#' ^ "\n")
    in
    let s_tacs =
      List.map (fun t -> "+ " ^ indent 2 (pp_tactic t)) goal.tactic_choices
    in
    s_ctx ^ "\n" ^ String.concat "\n" s_tacs
  and pp_tactic tac =
    tac.tactic ^ "\n\n" ^ String.make 16 '-' ^ "\n\n" ^ pp_goal tac.subgoal
  in
  pp_goal goal

let goal_logprob goal =
  match goal.parent_tactic with
  | None -> 0.
  | Some t -> t.logprob

let goal_depth goal =
  match goal.parent_tactic with
  | None -> 0
  | Some t -> t.depth

let goal_tactics goal =
  let rec aux acc = function
    | None -> acc
    | Some t -> aux (t.tactic :: acc) t.parent_goal.parent_tactic
  in
  aux [] goal.parent_tactic

type context_functions =
  { input_file : unit -> string
  ; log : string -> unit
  ; add_context : string -> unit
  ; get_cached_context : unit -> string option
  ; get_context : unit -> string
  ; add_proof : string -> unit }

type try_result =
  | Finished of string
  | Progress of string * proof_ctx list * State.t
  | Failed

let tactic_timeout_seconds = 5.0

let try_tactic ctx tac =
  let warning msg = ctx.log ("WARNING: " ^ tac ^ " TACTICS " ^ msg) in
  let rec try_aux tried curr_tac =
    try
      add_exec_sentences curr_tac |> ignore ;
      let tried = tried ^ curr_tac in
      match current_proof_state () with
      | NeedNextBullet bullet ->
          let bullet = String.trim bullet in
          if bullet = ""
          then begin
            ctx.log "WARNING: empty bullet" ;
            Failed
          end
          else try_aux tried ("\n" ^ bullet)
      | Other -> try_aux tried "\nQed."
      | InCtx ctx -> Progress (tried, ctx, State.backup ())
      | Aborted | Admitted -> Failed
      | Qed -> Finished tried
    with
    | CoqExn _ -> Failed
    | exn ->
        let info = Printexc.to_string exn |> trim_backtrace in
        warning ("RAISED EXCEPTION " ^ info) ;
        Failed
  in
  let backup = State.backup () in
  let res = Control.timeout tactic_timeout_seconds (try_aux "") tac in
  ( match res with
  | Some (Finished _) -> ()
  | _ -> State.restore backup ) ;
  match res with
  | Some res -> res
  | None ->
      warning
        ( "CAN NOT COMPLETE IN "
        ^ string_of_float tactic_timeout_seconds
        ^ " SECONDS" ) ;
      Failed

type expand_result = OneFinished of string | SomeProgress of tactic_node list

module PrioQueue = Heap.Functional (struct
  type t = tactic_node

  let compare n1 n2 = compare n1.logprob n2.logprob
end)

(* let log_search_tree =
   let log_chan = lazy (open_out "gptf.log") in
   fun goal ->
     let log_chan = Lazy.force log_chan in
     let tree_str = string_of_tree goal in
     output_string log_chan "CURRENT SEARCH TREE:\n" ;
     output_string log_chan tree_str ;
     output_char log_chan '\n' ;
     flush log_chan *)

let current_script () =
  let rec aux acc = function
    | None -> acc
    | Some t -> aux (t.tactic :: acc) t.parent_goal.parent_tactic
  in
  aux [] !cursor |> String.concat "\n"

let gptf_search (module M : MODEL) ctx proof_ctx =
  cursor := None ;
  Hashtbl.reset appeared_goals ;
  Hashtbl.replace appeared_goals proof_ctx () ;
  let root_goal =
    { goal = proof_ctx
    ; parent_tactic = None
    ; tactic_choices = []
    ; state = State.backup () }
  in
  let complete_choices =
    (* model calls <= 128 for each proof *)
    (* 8 samples per model call *)
    fuel_guard 128 (M.generate_choices 8)
  in
  let complete msg =
    let rec get () =
      try complete_choices msg
      with M.UnexpectedResponse resp ->
        ctx.log ("WARNING: UNEXPECTED RESPONSE FROM MODEL\n" ^ resp) ;
        get ()
    in
    get ()
    |> List.filter_map (fun (tac, logprob) ->
           match parse_coqblock tac with
           | "" -> None
           | tac ->
               let len = String.length tac in
               let tac =
                 match String.get tac (len - 1) with
                 | '.' | '-' | '+' | '*' | '{' | '}' -> tac
                 | _ -> tac ^ "."
               in
               Some (tac, logprob) )
    |> List.sort_uniq (fun (tac1, _) (tac2, _) -> compare tac1 tac2)
  in
  let expand_goal ctx goal =
    State.restore goal.state ;
    let g_logprob = goal_logprob goal in
    let g_depth = goal_depth goal in
    let g_tactics = String.concat "\n" (goal_tactics goal) ^ "\n" in
    let choices =
      match
        M.generate_message
          (ctx.get_cached_context ())
          (ctx.get_context () ^ g_tactics)
          goal.goal
      with
      | None ->
          let {hyps; goal} = List.hd goal.goal in
          ctx.log
            ( "WARNING: CURRENT GOAL TOO LONG\n" ^ hyps ^ "\n"
            ^ String.make 16 '=' ^ "\n" ^ goal ) ;
          []
      | Some msg -> complete msg
    in
    match
      choices
      |> List.find_map (fun (tac, logprob) ->
             match try_tactic ctx tac with
             | Finished tac -> Some tac
             | Progress (tac, p_ctx, state) ->
                 if not (Hashtbl.mem appeared_goals p_ctx)
                 then begin
                   Hashtbl.replace appeared_goals p_ctx () ;
                   let rec tac_node =
                     { tactic = tac
                     ; depth = g_depth + 1
                     ; logprob = g_logprob +. logprob
                     ; parent_goal = goal
                     ; subgoal =
                         { goal = p_ctx
                         ; parent_tactic = Some tac_node
                         ; tactic_choices = []
                         ; state } }
                   in
                   goal.tactic_choices <- tac_node :: goal.tactic_choices
                 end ;
                 None
             | Failed -> None )
    with
    | Some tac -> OneFinished (g_tactics ^ tac)
    | None ->
        goal.tactic_choices <- List.rev goal.tactic_choices ;
        SomeProgress goal.tactic_choices
  in
  let close_with_qed tac =
    let plength = count_tokens ("Proof. " ^ tac) in
    ctx.add_proof @@ "(* generated proof tokens: " ^ string_of_int plength
    ^ " *)\n" ^ tac ^ "\n" ;
    ctx.log "Closed with Qed."
  in
  let close_with_admitted info =
    add_exec_sentences " Admitted. " |> ignore ;
    ctx.add_proof @@ current_script () ^ "\n(* " ^ info ^ " *)\nAdmitted.\n" ;
    ctx.log (info ^ ". Closed with Admitted.")
  in
  let pq = ref PrioQueue.empty in
  let pq_pop () =
    let t = PrioQueue.maximum !pq in
    pq := PrioQueue.remove !pq ;
    t
  in
  try
    match expand_goal ctx root_goal with
    | OneFinished tac -> close_with_qed tac
    | SomeProgress tacs -> begin
      List.iter (fun t -> pq := PrioQueue.add t !pq) tacs ;
      let rec search_step () =
        try
          let best_tactic = pq_pop () in
          cursor := Some best_tactic ;
          match expand_goal ctx best_tactic.subgoal with
          | OneFinished tac -> close_with_qed tac
          | SomeProgress tacs ->
              List.iter (fun t -> pq := PrioQueue.add t !pq) tacs ;
              search_step ()
        with Heap.EmptyHeap -> close_with_admitted "No more tactics to try"
      in
      search_step ()
    end
  with Fuelout -> close_with_admitted "Reached max number of model calls"

let estimated_cache_rate = 0.85

let hint_rate =
  Option.default 0.0
    (Option.map float_of_string (Sys.getenv_opt "LCOQ_HINT_RATE"))

let sample_rate =
  Option.default 1.0
    (Option.map float_of_string (Sys.getenv_opt "LCOQ_SAMPLE_RATE"))

let _ =
  assert (hint_rate >= 0.) ;
  assert (sample_rate >= 0.) ;
  assert (hint_rate +. sample_rate <= 1.)

let read_actions =
  match Sys.getenv_opt "LCOQ_READ_ACTIONS" with
  | Some "1" -> true
  | _ -> false

type proof_action = HINT | SKIP | SEARCH

let gen_actions_by_shuffle n =
  (* make # of samples only depends on `n` and `sample_rate` *)
  let rest_rate = 1.0 -. sample_rate in
  let parts = int_partition [|rest_rate; sample_rate|] n in
  let sample_cnt = parts.(1) in
  let rest_cnt = parts.(0) in
  let parts = int_partition [|hint_rate; rest_rate -. hint_rate|] rest_cnt in
  let hint_cnt = parts.(0) in
  let skip_cnt = parts.(1) in
  assert (hint_cnt + skip_cnt + sample_cnt = n) ;
  let actions =
    Array.concat
      [ Array.make hint_cnt HINT
      ; Array.make skip_cnt SKIP
      ; Array.make sample_cnt SEARCH ]
  in
  shuffle (Random.State.make [|42|]) actions ;
  actions

let gen_actions ctx n =
  if not read_actions
  then gen_actions_by_shuffle n
  else
    let action_file =
      Filename.remove_extension (ctx.input_file ()) ^ ".actions"
    in
    ctx.log ("TRY READING ACTIONS FROM " ^ action_file) ;
    let ic = open_in action_file in
    let content = In_channel.input_all ic in
    close_in ic ;
    let action_strs = String.split_on_char '\n' @@ String.trim content in
    let actions =
      List.map
        (function
          | "HINT" -> HINT
          | "SKIP" -> SKIP
          | "SEARCH" -> SEARCH
          | s -> failwith ("unknown action " ^ s) )
        action_strs
      |> Array.of_list
    in
    assert (Array.length actions = n) ;
    actions

let complete_loop (module M : MODEL) ctx sentences =
  let actions =
    let n =
      List.fold_left
        (fun acc -> function
          | Coq_sentence.PROOF_HOLE _ -> acc + 1
          | _ -> acc )
        0 sentences
    in
    if n > 0 then gen_actions ctx n else [||]
  in
  (* let parts =
    int_partition [|hint_rate; 1.0 -. hint_rate -. sample_rate; sample_rate|] n
  in
  let hint_cnt = parts.(0) in
  let skip_cnt = parts.(1) in
  let sample_cnt = parts.(2) in
  assert (hint_cnt + skip_cnt + sample_cnt = n) ;
  let actions =
    Array.concat
      [ Array.make hint_cnt HINT
      ; Array.make skip_cnt SKIP
      ; Array.make sample_cnt SEARCH ]
  in
  shuffle actions ; *)
  ctx.log
    ( "ACTIONS: "
    ^ String.concat " "
        (List.map
           (function
             | HINT -> "HINT"
             | SKIP -> "SKIP"
             | SEARCH -> "SEARCH" )
           (Array.to_list actions) ) ) ;
  let action_cnt = ref 0 in
  let process = function
    | Coq_sentence.(OTHER s | REQUIRE (s, _, _)) ->
        ( try add_exec_sentences s |> ignore
          with exn ->
            print_endline ("ERROR " ^ s) ;
            raise exn ) ;
        ctx.add_context @@ s ^ "\n"
    | Coq_sentence.PROOF_HOLE original_proof -> (
        let plength = count_tokens original_proof in
        incr action_cnt ;
        match actions.(!action_cnt - 1) with
        | HINT ->
            (* hint this proof *)
            add_exec_sentences "Proof. Admitted. " |> ignore ;
            ctx.add_proof @@ "(* hint proof tokens: " ^ string_of_int plength
            ^ " *)\n" ;
            ctx.add_context @@ original_proof ^ "\n"
        | SKIP ->
            add_exec_sentences "Proof. Admitted. " |> ignore ;
            ctx.add_proof @@ "Proof.\n(* skipped proof tokens: "
            ^ string_of_int plength ^ " *)\nAdmitted.\n"
        | SEARCH -> (
            add_exec_sentences "Proof. " |> ignore ;
            match current_proof_state () with
            | InCtx proof_ctx ->
                ctx.add_proof "Proof.\n" ;
                ctx.add_proof @@ "(* original proof tokens: "
                ^ string_of_int plength ^ " *)\n" ;
                gptf_search (module M) ctx proof_ctx ;
                ctx.add_proof "\n"
            | _ -> ctx.log "WARNING: NO GOALS" ) )
  in
  List.iter process sentences

let complete (module M : MODEL) ?(include_external_modules = true)
    (config : Cli.config) =
  Sys.catch_break true ;
  if config.mode <> Cli.Vok then failwith "only support -vok" ;
  Flags.load_vos_libraries := true ;
  let source = ser_init config.input_file config.ml_include config.vo_load in
  let sentences = Coq_sentence.split_sentences source in
  let file_base = Filename.remove_extension config.input_file in
  let dirname = Filename.dirname config.input_file in
  let log_chan = open_out (file_base ^ ".log") in
  let ctx_log s =
    output_string log_chan s ; output_char log_chan '\n' ; flush log_chan
  in
  let external_modules =
    if include_external_modules
    then
      sentences
      |> List.filter_map (function
           | Coq_sentence.REQUIRE (_, _, modules) -> (
               split_by_space modules
               |> List.filter_map (fun m ->
                      let path = Filename.concat dirname (m ^ "_context.v") in
                      try
                        let ic = open_in path in
                        let source = In_channel.input_all ic in
                        close_in ic ;
                        ctx_log ("EXTERNAL MODULE " ^ m) ;
                        Some
                          ("Module " ^ m ^ ".\n" ^ source ^ "\nEnd " ^ m ^ ".")
                      with Sys_error _ -> None )
               |> function
               | [] -> None
               | l -> Some (String.concat "\n\n" l) )
           | _ -> None )
      |> function
      | [] -> None
      | l -> Some (String.concat "\n\n" l ^ "\n\n")
    else None
  in
  let output_chan = open_out (file_base ^ "_generated.v") in
  let finalized_script = ref "" in
  let context_cached = ref external_modules in
  let context = ref "" in
  let cache_current_context () =
    ( match (!context_cached, !context) with
    | _, "" -> ()
    | None, c -> context_cached := Some c
    | Some cc, c -> context_cached := Some (cc ^ c) ) ;
    context := ""
  in
  let ctx =
    { input_file = (fun () -> config.input_file)
    ; log = ctx_log
    ; add_context =
        (fun s ->
          finalized_script := !finalized_script ^ s ;
          context := !context ^ s ;
          output_string output_chan s ;
          flush output_chan ;
          let cached_len = Option.cata String.length 0 !context_cached in
          let noncached_len = String.length !context in
          if
            float_of_int cached_len /. float_of_int (cached_len + noncached_len)
            < estimated_cache_rate
          then cache_current_context () )
    ; get_cached_context = (fun () -> !context_cached)
    ; get_context = (fun () -> !context)
    ; add_proof =
        (fun s ->
          finalized_script := !finalized_script ^ s ;
          output_string output_chan s ;
          flush output_chan ) }
  in
  M.register_log ctx.log ;
  complete_loop (module M) ctx sentences ;
  List.iter check_exn (ser_exec Ser.Join) ;
  M.cleanup () ;
  close_out output_chan ;
  close_out log_chan ;
  let vok = open_out (file_base ^ ".vok") in
  close_out vok

let complete_openai = complete (module OPENAI_MODEL)

let complete_gemini = complete (module GEMINI_MODEL)
