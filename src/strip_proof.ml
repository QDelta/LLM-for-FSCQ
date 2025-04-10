let strip_proof (config : Serutils.Cli.config) =
  Random.init 0 ;
  let input_chan = open_in config.input_file in
  let source = In_channel.input_all input_chan in
  close_in input_chan ;
  let sentences = Coq_sentence.split_sentences source in
  let output_chan =
    open_out (Filename.remove_extension config.input_file ^ "_context.v")
  in
  let emit s =
    output_string output_chan s ;
    output_char output_chan '\n'
  in
  let hint_flags =
    let n =
      List.fold_left
        (fun acc -> function
          | Coq_sentence.PROOF_HOLE _ -> acc + 1
          | _ -> acc )
        0 sentences
    in
    if n > 0
    then (
      let hint_cnt =
        int_of_float @@ Float.round (float_of_int n *. Gptf.hint_rate)
      in
      let hint_flags =
        Array.append (Array.make hint_cnt true)
          (Array.make (n - hint_cnt) false)
      in
      Utils.shuffle (Random.State.make [|42|]) hint_flags ;
      hint_flags )
    else [||]
  in
  let proof_cnt = ref 0 in
  List.iter
    (function
      | Coq_sentence.PROOF_HOLE p ->
          incr proof_cnt ;
          if hint_flags.(!proof_cnt - 1) then emit p else emit ""
      | Coq_sentence.REQUIRE (s, _, _) -> emit s
      | Coq_sentence.OTHER s -> emit s )
    sentences ;
  close_out output_chan
