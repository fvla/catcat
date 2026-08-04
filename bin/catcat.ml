(* The catcat REPL.

   Each line goes through the whole pipeline: lex (E01) -> parse (E03) ->
   elaborate (E04) -> typecheck (M06) -> evaluate (R02/R05). The line is lexed
   whole and then parsed ONE DECLARATION AT A TIME, evaluating as it goes,
   because a `macro` declaration changes the grammar the rest of the line is
   read with (D-54). A lexing error therefore costs nothing, while a parse or
   type error costs whatever ran before it on that line.

   THIS FILE IS THE OUTERMOST HANDLER. `E06_Repl.eval_line` returns `LEffect`
   when an operation escapes every handler in the program, and for the built-in
   `IO` effect this loop performs it and calls `resume_line`. That is the whole
   of "effects only the compiler or interpreter can supply": `print` and `read`
   are ordinary operations of an ordinary effect, and the only thing special
   about them is that nothing inside the language owns effect id 0.

   The continuation `resume_line` takes is the INTERPRETER's machine state, not
   a catcat value — see the note in R05_Driver.fsti about why that distinction
   matters and must not erode. A compiled program calls the runtime directly and
   has no such object.

   Everything else of substance lives in E06_Repl; this file is a terminal loop.
   With arguments, it runs them as lines and exits — which is how the regression
   script drives it. *)

let banner () =
  print_endline "catcat — type catcat, or :q to quit, :s to show the stack";
  print_endline "  e.g.  2 3 +";
  print_endline "        define square ( $x:i64 -- i64 ) { $x $x * }";
  print_endline "        42 print";
  print_endline ""

(* Perform one IO operation, or decline it. Returns the stack to resume with:
   the operation's arguments removed and its results pushed. *)
let perform op stk =
  if op = R03_Prelude.w_print then
    match stk with
    | R01_Runtime.RInt n :: rest ->
        print_endline (Z.to_string n);
        Some rest
    | _ -> None
  else if op = R03_Prelude.w_read then begin
    print_string "? ";
    flush stdout;
    match read_line () with
    | exception End_of_file -> Some (R01_Runtime.RInt Z.zero :: stk)
    | line ->
        let n = try Z.of_string (String.trim line) with _ -> Z.zero in
        Some (R01_Runtime.RInt n :: stk)
  end
  else None

(* Drive one line to completion, servicing whatever the host can service. *)
let rec drive = function
  | E06_Repl.LDone (session, out) ->
      if out <> "" then print_endline out;
      session
  | E06_Repl.LEffect (op, stk, k, susp) -> (
      match perform op stk with
      | Some stk' -> drive (E06_Repl.resume_line susp k stk')
      (* Not an IO operation: nobody handled it and the host has no
         implementation either. Report, and run the rest of the line. *)
      | None -> drive (E06_Repl.abandon_line susp op))

let step session line = drive (E06_Repl.eval_line session line)

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
