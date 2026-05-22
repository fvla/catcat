let split_words line =
  line
  |> String.split_on_char ' '
  |> List.filter (fun token -> token <> "")

let eval_token machine token =
  match Catcat_Core.read_word token with
  | Some word ->
      Catcat_Core.eval_word machine word;
      Ok ()
  | None -> Error ("unknown word: " ^ token)

let eval_line machine line =
  let rec loop = function
    | [] -> Ok ()
    | token :: rest ->
        match eval_token machine token with
        | Ok () -> loop rest
        | Error _ as error -> error
  in
  loop (split_words line)

let rec repl machine =
  print_string "catcat> ";
  flush stdout;
  match read_line () with
  | line ->
      begin
        match eval_line machine line with
        | Ok () -> print_endline (Catcat_Core.print_stack machine)
        | Error message -> prerr_endline message
      end;
      repl machine
  | exception End_of_file ->
      print_endline ""

let () =
  let machine = Catcat_Core.make_machine () in
  repl machine