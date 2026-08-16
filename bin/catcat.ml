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
   about them is that nothing inside the language owns effect ids 0 (Dict) or 1 (IO).

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
(* The C boundary. See bin/catcat_c.c for why this is a fixed table rather than
   dlsym + libffi, and E06_Repl.install_extern for the catcat-visible side. *)
external c_strlen : string -> int = "catcat_c_strlen"
external c_puts   : string -> int = "catcat_c_puts"
external c_abs    : int -> int    = "catcat_c_abs"
external c_time   : unit -> int   = "catcat_c_time"
external c_getpid : unit -> int   = "catcat_c_getpid"
external c_getenv : string -> string = "catcat_c_getenv"

(* Perform a foreign call, or decline it. `name` is the C symbol, which is the
   catcat word's own name — there is no aliasing form.

   The arity and types were checked when the `extern` was declared
   (E06.c_marshalable), so a shape mismatch here means the table below and the
   declaration disagree, and returning None reports that as "no handler" rather
   than crashing the session. *)
let perform_c name stk =
  let i n = R01_Runtime.RInt (Z.of_int n) in
  match name, stk with
  | "strlen", R01_Runtime.RStr s :: rest -> Some (i (c_strlen s) :: rest)
  | "puts",   R01_Runtime.RStr s :: rest -> Some (i (c_puts s) :: rest)
  | "abs",    R01_Runtime.RInt n :: rest -> Some (i (c_abs (Z.to_int n)) :: rest)
  | "getenv", R01_Runtime.RStr s :: rest ->
      Some (R01_Runtime.RStr (c_getenv s) :: rest)
  | "time",   _ -> Some (i (c_time ()) :: stk)
  | "getpid", _ -> Some (i (c_getpid ()) :: stk)
  | _ -> None

let perform op stk =
  if op = R03_Prelude.w_print then
    (* `print_string`, not `print_endline`: the string is emitted as itself, so
       a trailing newline is the program's to write with "\n". The i64 version
       this replaced had no choice, since a number has no room for one. *)
    match stk with
    | R01_Runtime.RStr s :: rest ->
        print_string s;
        flush stdout;
        Some rest
    | _ -> None
  else if op = R03_Prelude.w_read then begin
    print_string "? ";
    flush stdout;
    (* EOF reads as the empty string. There is no `option` in the signature to
       report it with, and inventing a sentinel line would be worse; a program
       that needs to tell them apart wants a `read` returning a sum, which is a
       signature change and not a host-loop decision. *)
    match read_line () with
    | exception End_of_file -> Some (R01_Runtime.RStr "" :: stk)
    | line -> Some (R01_Runtime.RStr line :: stk)
  end
  else None

(* Drive one line to completion, servicing whatever the host can service. *)
let rec drive = function
  | E06_Repl.LDone (session, out) ->
      if out <> "" then print_endline out;
      session
  | E06_Repl.LEffect (op, stk, k, susp) -> (
      (* Which host effect is this? IO and C are the two the host services;
         anything else escaped with nobody to handle it. Dispatching on the
         EFFECT rather than on the word id is what makes `extern` work at all,
         since each declaration allocates a fresh id the host cannot know. *)
      let eff = E06_Repl.susp_op_eff susp op in
      let result =
        if Z.equal eff R03_Prelude.eff_c
        then perform_c (E06_Repl.susp_op_name susp op) stk
        else perform op stk
      in
      match result with
      | Some stk' -> drive (E06_Repl.resume_line susp k stk')
      (* Nobody handled it and the host has no implementation either. Report,
         and run the rest of the line. *)
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

(* Script mode: `-f FILE` turns a file into a list of lines.

   A file is split on BLANK LINES and each paragraph is run as one line. Not
   line by line, because a declaration may span lines; and not whole-file as a
   single line, because `eval_line` streams whatever IO the line performs but
   batches its own results (`defined …`, `ok …`) to the end — so a one-line file
   would print every result after every effect, which is the wrong transcript.

   Blank-line splitting needs no knowledge of catcat syntax, which is the point:
   the granularity is the file author's, and the host stays out of the parser's
   business (D-54 — only E06 knows where a declaration ends). The one input it
   reads wrongly is a string literal spanning a blank line, which U01 §2 permits;
   that fails loudly as an unterminated string rather than quietly. *)
let paragraphs text =
  let is_blank s = String.trim s = "" in
  let flush acc cur =
    if cur = [] then acc else String.concat "\n" (List.rev cur) :: acc
  in
  let rec go acc cur = function
    | [] -> List.rev (flush acc cur)
    | l :: rest ->
        if is_blank l then go (flush acc cur) [] rest else go acc (l :: cur) rest
  in
  go [] [] (String.split_on_char '\n' text)

let read_file path =
  match open_in_bin path with
  | exception Sys_error msg ->
      prerr_endline ("catcat: " ^ msg);
      exit 2
  | ic ->
      let s = really_input_string ic (in_channel_length ic) in
      close_in ic;
      s

let () =
  let args = List.tl (Array.to_list Sys.argv) in
  if args = [] then begin
    banner ();
    loop E06_Repl.init_session
  end
  else
    (* Non-interactive: run each argument as a line, and each `-f FILE` as the
       paragraphs of that file. One session throughout, so a file may set up
       definitions that a later argument uses. *)
    let rec expand = function
      | [] -> []
      | ("-f" | "--file") :: path :: rest -> paragraphs (read_file path) @ expand rest
      | [ ("-f" | "--file") ] ->
          prerr_endline "catcat: -f needs a file";
          exit 2
      | line :: rest -> line :: expand rest
    in
    ignore
      (List.fold_left
         (fun session line ->
           print_endline ("catcat> " ^ line);
           step session line)
         E06_Repl.init_session (expand args))
