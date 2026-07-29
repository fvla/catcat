(* The catcat REPL.

   Each line goes through the whole pipeline: lex (E01) -> parse (E03) ->
   elaborate (E04) -> typecheck (M06) -> evaluate (R02/R05). A parse or type
   error leaves the session untouched, so a bad line costs nothing.

   Everything of substance lives in E06_Repl; this file is a terminal loop.
   With arguments, it runs them as lines and exits — which is how the
   regression script drives it. *)

let banner () =
  print_endline "catcat — type catcat, or :q to quit, :s to show the stack";
  print_endline "  e.g.  2 3 add 4 mul";
  print_endline "        define square ( $x:i64 -- i64 ) { $x $x mul }";
  print_endline ""

let step session line =
  let session, out = E06_Repl.eval_line session line in
  if out <> "" then print_endline out;
  session

let rec loop session =
  print_string "catcat> ";
  flush stdout;
  match read_line () with
  | exception End_of_file -> print_newline ()
  | ":q" -> ()
  | ":s" ->
      print_endline (E06_Repl.show_stack session);
      loop session
  | line -> loop (step session line)

let () =
  let args = List.tl (Array.to_list Sys.argv) in
  if args = [] then begin
    banner ();
    loop E06_Repl.init_session
  end
  else
    (* Non-interactive: run each argument as a line. *)
    ignore
      (List.fold_left
         (fun session line ->
           print_endline ("catcat> " ^ line);
           step session line)
         E06_Repl.init_session args)
