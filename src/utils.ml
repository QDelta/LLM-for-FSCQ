let split_by_end f l =
  let rec loop acc cur = function
    | [] ->
        ( match cur with
        | [] -> acc
        | _ -> List.rev cur :: acc )
        |> List.rev
    | x :: xs ->
        if f x
        then loop (List.rev (x :: cur) :: acc) [] xs
        else loop acc (x :: cur) xs
  in
  loop [] [] l

let rec drop_until f l =
  match l with
  | [] -> l
  | x :: xs -> if f x then l else drop_until f xs

let substring_in s bp ep = String.sub s bp (ep - bp)

let int_partition ratios n =
  assert (Array.for_all (fun x -> x >= 0.) ratios) ;
  let positioned_parts =
    let sum_r = Array.fold_left ( +. ) 0. ratios in
    Array.mapi
      (fun i r ->
        let part = r /. sum_r *. float_of_int n in
        let base = int_of_float part in
        let diff = part -. float_of_int base in
        (i, base, diff) )
      ratios
  in
  let remaining =
    n - Array.fold_left (fun acc (_, x, _) -> acc + x) 0 positioned_parts
  in
  (* distribute remaining to entries with maximum difference (1 each) *)
  Array.stable_sort (fun (_, _, x) (_, _, y) -> -compare x y) positioned_parts ;
  for i = 0 to remaining - 1 do
    let idx, base, diff = positioned_parts.(i) in
    positioned_parts.(i) <- (idx, base + 1, diff)
  done ;
  Array.sort (fun (i, _, _) (j, _, _) -> compare i j) positioned_parts ;
  Array.map (fun (_, x, _) -> x) positioned_parts

let shuffle st arr =
  for i = Array.length arr - 1 downto 1 do
    let j = Random.State.int st (i + 1) in
    let tmp = arr.(i) in
    arr.(i) <- arr.(j) ;
    arr.(j) <- tmp
  done

let print_flush s = print_string s ; flush stdout

let with_re re f =
  let re = lazy (Re.compile re) in
  f (Lazy.force re)

let trim_backtrace =
  with_re (Re.str "Raised") @@ fun re err_msg -> Re.split re err_msg |> List.hd

let indent =
  with_re (Re.char '\n')
  @@ fun re n s ->
  Re.replace_string re ~all:true ~by:("\n" ^ String.make n ' ') s

let parse_coqblock =
  with_re
    Re.(
      seq
        [ bos
        ; rep blank
        ; str "```coq"
        ; group (rep any)
        ; str "```"
        ; rep blank
        ; eos ] )
  @@ fun re s ->
  ( match Re.exec_opt re s with
  | None -> s
  | Some grp -> (
    match Re.Group.get_opt grp 1 with
    | None -> s
    | Some s -> s ) )
  |> String.trim

let split_by_space =
  with_re (Re.rep1 @@ Re.set " \t\011\012\r\n") (fun re s -> Re.split re s)

exception Fuelout

(* limit total calling time of f *)
let fuel_guard fuel f =
  let cnt = ref 0 in
  fun x -> if !cnt >= fuel then raise Fuelout else (incr cnt ; f x)

let curl_global_init =
  let dummy = lazy (Curl.global_init Curl.CURLINIT_GLOBALALL) in
  fun () ->
    Lazy.force dummy ;
    Stdlib.at_exit Curl.global_cleanup

let curl_make_handle () =
  let handle = Curl.init () in
  Gc.finalise Curl.cleanup handle ;
  handle

let count_tokens =
  let chans =
    lazy
      (let count_exe =
         match Sys.getenv_opt "LCOQ_COUNT_TOKEN" with
         | Some path -> path
         | None -> failwith "Environment variable LCOQ_COUNT_TOKEN not found"
       in
       let rx, tx = Unix.open_process_args count_exe [||] in
       at_exit (fun () -> Unix.close_process (rx, tx) |> ignore) ;
       (rx, tx) )
  in
  fun s ->
    let rx, tx = Lazy.force chans in
    output_string tx s ;
    output_byte tx 0 ;
    flush tx ;
    int_of_string (input_line rx)
