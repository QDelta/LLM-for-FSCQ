open Utils
open Serapi
module Ser = Serapi_protocol

(* Serapi_protocol.exec_cmd actually does not change this state *)
let sp_state = ref (Ser.State.make ())

module State : sig
  type t

  val backup : unit -> t

  val restore : t -> unit
end = struct
  type t = Ser.State.t * Ser.ControlUtil.doc * Stm.document

  let backup () = (!sp_state, Ser.ControlUtil.backup (), Stm.backup ())

  let restore (sp_st, ser_ctrl_st, stm_st) =
    sp_state := sp_st ;
    Ser.ControlUtil.restore ser_ctrl_st ;
    Stm.restore stm_st
end

let ser_exec_raw cmd =
  let ans, new_st = Ser.exec_cmd !sp_state cmd in
  sp_state := new_st ;
  ans

let ser_exec =
  if Option.is_empty (Sys.getenv_opt "LCOQ_SER_LOG")
  then ser_exec_raw
  else
    let log_chan = lazy (open_out "ser_exec.log") in
    fun cmd ->
      let log_chan = Lazy.force log_chan in
      let ans = ser_exec_raw cmd in
      Sertop.Sertop_ser.sexp_of_cmd cmd
      |> Sexplib0.Sexp.to_string |> output_string log_chan ;
      output_char log_chan '\n' ;
      ans
      |> List.iter (fun a ->
             Sertop.Sertop_ser.sexp_of_answer_kind a
             |> Sexplib0.Sexp.to_string |> output_string log_chan ;
             output_char log_chan '\n' ) ;
      flush log_chan ;
      ans

type sentence = {id : Stateid.t; text : string; loc : int * int}

exception CoqExn of int * string

let raise_info (info : Ser.ExnInfo.t) =
  raise
    (CoqExn
       ( ( match info.loc with
         | None -> 0
         | Some loc -> loc.line_nb )
       , trim_backtrace info.str ) )

let check_exn = function
  | Ser.CoqExn info -> raise_info info
  | _ -> ()

let add_sentences src =
  let ans =
    ser_exec
      Ser.(Add ({lim = None; ontop = None; newtip = None; verb = false}, src))
  in
  let sentences =
    ans
    |> List.filter_map (function
         | Ser.Added (sid, loc, _) ->
             Some
               { id = sid
               ; text = substring_in src loc.bp loc.ep
               ; loc = (loc.bp, loc.ep) }
         | _ -> None )
  in
  List.iter
    (function
      | Ser.CoqExn info ->
          ser_exec (Ser.Cancel (List.map (fun s -> s.id) sentences)) |> ignore ;
          raise_info info
      | _ -> () )
    ans ;
  sentences

let add_exec_sentences src =
  let sentences = add_sentences src in
  let sids = List.map (fun s -> s.id) sentences in
  List.concat_map (fun id -> ser_exec (Ser.Exec id)) sids
  |> List.iter (function
       | Ser.CoqExn info ->
           ser_exec (Ser.Cancel sids) |> ignore ;
           raise_info info
       | _ -> () ) ;
  sentences

let current_sid () = Stm.get_current_state ~doc:(Stm.get_doc 0)

let ser_init input_file ml_path vo_path =
  (* make sexp print less verbose *)
  Serlib.Serlib_init.(
    init
      ~options:
        { omit_loc = true
        ; omit_att = true
        ; omit_env = true
        ; exn_on_opaque = false } ) ;
  let default_ml_path, default_vo_path =
    Serapi_paths.coq_loadpath_default ~implicit:true
      ~coq_path:
        ( match Sys.getenv_opt "COQLIB" with
        | Some coqlib -> coqlib
        | None -> Coq_config.coqlib )
  in
  Sertop.Sertop_init.(
    coq_init
      { fb_handler = (fun _ _ -> ())
      ; plugin_load = None
      ; debug = false
      ; set_impredicative_set = false
      ; allow_sprop = false
      ; indices_matter = false
      ; ml_path = default_ml_path @ ml_path
      ; vo_path = default_vo_path @ vo_path }
      Format.std_formatter ) ;
  let injections =
    [Coqargs.RequireInjection ("Coq.Init.Prelude", None, Some Lib.Import)]
  in
  let stm_options = Stm.AsyncOpts.default_opts in
  let doc_type =
    Stm.Interactive (Coqargs.TopPhysical input_file)
    (* Stm.Interactive (TopLogical Names.(DirPath.make [ Id.of_string "SerApiTest" ])) *)
  in
  Stm.(new_doc {doc_type; injections; stm_options}) |> ignore ;
  sp_state :=
    Ser.State.make ~in_file:input_file
      ~ldir:(Serapi_paths.dirpath_of_file input_file)
      () ;
  let in_chan = open_in input_file in
  let content = In_channel.input_all in_chan in
  close_in in_chan ; content

let exec_exn sid = ser_exec (Ser.Exec sid) |> List.iter check_exn

let get_ctx sid =
  sid |> Stm.state_of_id ~doc:(Stm.get_doc 0) |> Extcoq.context_of_st

let format_ser =
  Ser.{pp_format = PpSer; pp_depth = 0; pp_elide = "..."; pp_margin = 0}

let unexpected_answer hint ans =
  ans
  |> Sexplib0.Sexp_conv.sexp_of_list Sertop.Sertop_ser.sexp_of_answer_kind
  |> Sexplib0.Sexp.to_string
  |> fun s -> failwith ("unexpected_answer " ^ hint ^ " " ^ s)

let query_sentence_ast sid =
  let query =
    Ser.(
      Query ({preds = []; limit = None; sid; pp = format_ser; route = 0}, Ast) )
  in
  let ans = ser_exec query in
  match ans with
  | Ser.[ObjList [CoqAst vernac]; Completed] -> vernac
  | _ -> unexpected_answer "query_sentence_ast" ans

type proof_ctx = {hyps : string; goal : string} [@@deriving yojson]

type proof_state =
  | Qed
  | Admitted
  | Aborted
  | NeedNextBullet of string
  | InCtx of proof_ctx list
  | Other

(* When no goals are focused, there are two possible suggestions:
   - Try unfocusing with }.
   - Focus next goal with bullet SOME_BULLET. *)
let extract_bullet_from_suggest =
  with_re
    Re.(
      seq
        [ alt [str "Focus next goal with bullet"; str "Try unfocusing with"]
        ; group (rep any)
        ; str "." ] )
  @@ fun re s -> Re.Group.get (Re.exec re s) 1

(* The state AFTER sentence sid is executed *)
let query_proof_state sid =
  let query =
    Ser.(
      Query ({preds = []; limit = None; sid; pp = format_ser; route = 0}, Goals) )
  in
  let ans = ser_exec query in
  let sigma, env = get_ctx sid in
  let just_ended_or_other () =
    let ast = query_sentence_ast sid in
    match ast.v.expr with
    | Vernacexpr.(VernacEndProof (Proved _)) -> Qed
    | Vernacexpr.(VernacEndProof Admitted) -> Admitted
    | Vernacexpr.(VernacAbort | VernacAbortAll) -> Aborted
    | _ -> Other
  in
  match ans with
  | Ser.[ObjList [CoqGoal g]; Completed] -> (
    match g.goals with
    | [] -> (
      match g.bullet with
      | None -> just_ended_or_other ()
      | Some pp ->
          let suggest =
            Format.fprintf Format.str_formatter "@[%a@]" Pp.pp_with pp ;
            Format.flush_str_formatter ()
          in
          NeedNextBullet (extract_bullet_from_suggest suggest) )
    | goals ->
        InCtx
          (List.map
             (fun g ->
               let hyps, goal = Serpp.pp_coq_goal_str env sigma format_ser g in
               {hyps; goal} )
             goals ) )
  | _ -> just_ended_or_other ()

let current_proof_state () = query_proof_state (current_sid ())

let current_sentence_ast () = query_sentence_ast (current_sid ())

module Cli = struct
  type mode = Vo | Vos | Vok

  type config =
    { input_file : string
    ; mode : mode
    ; ml_include : string list
    ; vo_load : Loadpath.vo_path list }

  let coq_lp_conv ~implicit unix_path lp =
    Loadpath.
      { coq_path = Libnames.dirpath_of_string lp
      ; unix_path
      ; has_ml = true
      ; recursive = true
      ; implicit }

  let check_dir dir =
    if Sys.file_exists dir && Sys.is_directory dir
    then dir
    else failwith (dir ^ "is not a directory")

  let parse args =
    let input_file =
      match List.rev args with
      | input_file :: _ ->
          if Sys.file_exists input_file && not (Sys.is_directory input_file)
          then input_file
          else failwith (input_file ^ " is not a file")
      | [] -> failwith "missing input file"
    in
    let rec skip_opt = function
      | [] -> []
      | a :: args -> if String.get a 0 = '-' then a :: args else skip_opt args
    in
    let mode = ref Vo in
    let ml_include = ref [] in
    let vo_load = ref [] in
    let rec aux = function
      | [] | [_] -> ()
      | "-vos" :: args ->
          mode := Vos ;
          aux args
      | "-vok" :: args ->
          mode := Vok ;
          aux args
      | "-I" :: path :: args ->
          ml_include := check_dir path :: !ml_include ;
          aux args
      | "-Q" :: path :: lp :: args ->
          vo_load := coq_lp_conv ~implicit:false (check_dir path) lp :: !vo_load ;
          aux args
      | "-R" :: path :: lp :: args ->
          vo_load := coq_lp_conv ~implicit:true (check_dir path) lp :: !vo_load ;
          aux args
      | a :: args ->
          if String.get a 0 = '-' then aux (skip_opt args) else aux args
    in
    aux args ;
    {input_file; mode = !mode; ml_include = !ml_include; vo_load = !vo_load}
end
