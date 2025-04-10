{
exception CoqSentence of string

let pack_rev acc =
  let len = List.length acc in
  let s = Bytes.create len in
  List.iteri (fun i c -> Bytes.unsafe_set s (len - 1 - i) c) acc;
  Bytes.to_string s

(* let not_space = function
    | ' ' | '\t' | '\011' | '\012' | '\r' | '\n' -> false
    | _ -> true

  let warn_if_not_all_space l =
    if List.exists not_space l
    then print_endline ("WARNING: SKIPPED " ^ pack_rev l) *)

type sentence = REQUIRE of string * string option * string | PROOF_HOLE of string | OTHER of string
}

let space = [' ' '\t' '\011' '\012' '\r' '\n']

let ident = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '_' '0'-'9' '\'']* (* TODO: unicode *)
let qualid = ident ('.' ident)*

rule sentences acc = parse
  | space+
      { sentences acc lexbuf }
  | (".." [^ '.']) as s
      { sentences (`OTHER s :: acc) lexbuf }
  | '.' (space+ | eof)
      { sentences (`OTHER "." :: acc) lexbuf }
  | "..." (space+ | eof)
      { sentences (`OTHER "..." :: acc) lexbuf }
  | "(*"
      { skip_comment 0 lexbuf; sentences acc lexbuf }
  | '"'
      { let s = sentence_rest (strlit ['"'] lexbuf) lexbuf in
        sentences (`OTHER s :: acc) lexbuf }
  | "Proof" ((space | '.') as c)
      { let s = proof [c; 'f'; 'o'; 'o'; 'r'; 'P'] lexbuf in
        sentences (s :: acc) lexbuf }
    (* TODO: complete syntax with import_categories and filtered_import *)
  | (("From" space+ (qualid as path) space+)? "Require" space+ ("Import" | "Export")? ((space+ qualid)+ as modules) space* '.') as s
      { sentences (`REQUIRE (s, path, modules) :: acc) lexbuf }
  | _ as c
      { let s = sentence_rest [c] lexbuf in
        sentences (`OTHER s :: acc) lexbuf }
  | eof
      { List.rev acc }

and sentence_rest acc = parse
  | space as c           { sentence_rest (c :: acc) lexbuf }
  | '.' (space+ | eof)   { pack_rev ('.' :: acc) }
  | ".." ([^ '.'] as c)  { sentence_rest (c :: '.' :: '.' :: acc) lexbuf }
  | "..." (space+ | eof) { pack_rev ('.' :: '.' :: '.' :: acc) }
  | '"'                  { let acc = strlit ('"' :: acc) lexbuf in
                           sentence_rest acc lexbuf }
  | "(*"                 { skip_comment 0 lexbuf; sentence_rest (' ' :: acc) lexbuf }
  | _ as c               { sentence_rest (c :: acc) lexbuf }
  | eof                  { raise (CoqSentence "unclosed sentence") }

and strlit acc = parse
  | "\"\"" { strlit ('"' :: '"' :: acc) lexbuf }
  | '"'    { '"' :: acc }
  | _ as c { strlit (c :: acc) lexbuf }
  | eof    { raise (CoqSentence ("unclosed string " ^ pack_rev acc)) }

and skip_comment depth = parse
  | "*)" { if depth > 0 then skip_comment (depth - 1) lexbuf }
  | "(*" { skip_comment (depth + 1) lexbuf }
  | _    { skip_comment depth lexbuf }
  | eof  { raise (CoqSentence "unclosed comment") }

and proof acc = parse
  | '"'                                  { let acc = strlit ('"' :: acc) lexbuf in
                                           proof acc lexbuf }
  | "(*"                                 { skip_comment 0 lexbuf; proof (' ' :: acc) lexbuf }
  | "Qed" space* '.' (space+ | eof)      { `OPAQUE (pack_rev @@ '.' :: 'd' :: 'e' :: 'Q' :: acc) }
  | "Defined" space* '.' (space+ | eof)  { `TRANSPARENT (pack_rev @@ '.' :: 'd' :: 'e' :: 'Q' :: acc) }
  | "Admitted" space* '.' (space+ | eof) { `OPAQUE (pack_rev @@ '.' :: 'd' :: 'e' :: 't' :: 't' :: 'i' :: 'm' :: 'd' :: 'A' :: acc) }
  | "Abort" space* '.' (space+ | eof)    { `ABORT }
  | _ as c                               { proof (c :: acc) lexbuf }
  | eof                                  { raise (CoqSentence "unclosed proof") }

{
let split_sentences source =
  let rec remove_abort acc = function
    | `OTHER _ :: `ABORT :: rest -> remove_abort acc rest
    | (`OTHER s | `TRANSPARENT s) :: rest -> remove_abort (OTHER s :: acc) rest
    | `OPAQUE s :: rest -> remove_abort (PROOF_HOLE s :: acc) rest
    | `REQUIRE (s, p, m) :: rest -> remove_abort (REQUIRE (s, p, m) :: acc) rest
    | `ABORT :: rest -> remove_abort acc rest
    | [] -> List.rev acc
  in
  Lexing.from_string source
  |> sentences []
  |> remove_abort []
}
