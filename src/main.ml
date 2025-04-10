open LCoq

let _ =
  if !Sys.interactive
  then ()
  else if Array.exists (( = ) "--print-version") Sys.argv
  then print_endline "8.16.1+lsp 4.14.2"
  else
    match List.tl (Array.to_list Sys.argv) with
    | [] -> failwith "no arguments"
    | subc :: args -> (
        let config = Serutils.Cli.parse args in
        match subc with
        | "gptf-openai" -> Gptf.complete_openai config
        | "gptf-gemini" -> Gptf.complete_gemini config
        | "strip-proof" -> Strip_proof.strip_proof config
        | _ -> failwith ("unknown subcommand " ^ subc) )
