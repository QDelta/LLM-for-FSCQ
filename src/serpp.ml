open Serapi

let pr_vlist pr =
  let open Pp in
  function
  | [] -> mt ()
  | l -> hov 0 (prlist_with_sep fnl pr l) ++ fnl ()

let pp_goal_gen pr_c Serapi_goals.{ty; hyp; _} =
  let open Pp in
  let pr_idl idl = prlist_with_sep (fun () -> str ", ") Names.Id.print idl in
  let pr_lconstr_opt c = str " := " ++ pr_c c in
  let pr_hdef = Option.cata pr_lconstr_opt (mt ()) in
  let pr_hyp (idl, hdef, htyp) =
    pr_idl idl ++ pr_hdef hdef ++ str " : " ++ pr_c htyp
  in
  (pr_vlist pr_hyp hyp, pr_c ty)

let pp_coq_goal_str env sigma (pr_opt : Serapi_protocol.format_opt) g =
  let open Format in
  let mb = pp_get_max_boxes str_formatter () in
  let et = pp_get_ellipsis_text str_formatter () in
  let mg = pp_get_margin str_formatter () in
  pp_set_max_boxes str_formatter pr_opt.pp_depth ;
  pp_set_ellipsis_text str_formatter pr_opt.pp_elide ;
  pp_set_margin str_formatter pr_opt.pp_margin ;
  let pr fmt =
    Format.fprintf Format.str_formatter "@[%a@]" Pp.pp_with fmt ;
    Format.flush_str_formatter ()
  in
  let pp_hyp, pp_goal = pp_goal_gen (Printer.pr_lconstr_env env sigma) g in
  (* let pp_hyp, pp_goal = pp_goal_gen (Ppconstr.pr_lconstr_expr env sigma) g in *)
  let result = (pr pp_hyp, pr pp_goal) in
  pp_set_max_boxes str_formatter mb ;
  pp_set_ellipsis_text str_formatter et ;
  pp_set_margin str_formatter mg ;
  result
