module E01_Lexer

open FStar.List.Tot
open FStar.Mul
module S = FStar.String
module C = FStar.Char

let is_space (c:C.char) : Tot bool =
  c = ' ' || c = '\t' || c = '\n' || c = '\r'

let is_delim (c:C.char) : Tot bool =
  c = '{' || c = '}' || c = '(' || c = ')' || c = '[' || c = ']' || c = ':'
  || c = '"'

let is_word_char (c:C.char) : Tot bool =
  not (is_space c) && not (is_delim c)

/// Digit value, or `-1` for a non-digit. Enumerated rather than range-checked
/// so this needs no arithmetic on character codes.
let digit_val (c:C.char) : Tot int =
  if c = '0' then 0 else if c = '1' then 1 else if c = '2' then 2
  else if c = '3' then 3 else if c = '4' then 4 else if c = '5' then 5
  else if c = '6' then 6 else if c = '7' then 7 else if c = '8' then 8
  else if c = '9' then 9 else (-1)

let rec digits_val (acc:int) (cs:list C.char) : Tot (option int) (decreases cs) =
  match cs with
  | []     -> Some acc
  | c :: r -> let d = digit_val c in
              if d < 0 then None else digits_val (acc * 10 + d) r

/// A word run is an integer literal when it is all digits, optionally with a
/// leading `-`. `-` alone, and `--`, are not integers.
let int_of_run (cs:list C.char) : Tot (option int) =
  match cs with
  | []          -> None
  | '-' :: rest -> (match rest with
                    | [] -> None
                    | _  -> (match digits_val 0 rest with
                             | None   -> None
                             | Some n -> Some (0 - n)))
  | _           -> digits_val 0 cs

(* ------------------------------------------------------------------------ *)
(* Scanning helpers                                                         *)
(* ------------------------------------------------------------------------ *)

/// Consume a maximal run of word characters. The length refinement is what
/// lets the main loop prove termination: the caller only enters here with a
/// word character in hand, so the remainder is strictly shorter.
///
/// Note the test is a predicate on ONE character. That is the whole lookahead
/// budget of this lexer: no state, no second character, no backtracking (D-30).
let rec take_run (acc:list C.char) (cs:list C.char)
  : Tot (r:(list C.char & list C.char) { length (snd r) <= length cs })
        (decreases cs) =
  match cs with
  | []     -> (rev acc, [])
  | c :: r -> if is_word_char c
              then take_run (c :: acc) r
              else (rev acc, cs)

let rec skip_line (cs:list C.char)
  : Tot (r:list C.char { length r <= length cs }) (decreases cs) =
  match cs with
  | []        -> []
  | c :: r    -> if c = '\n' then r else skip_line r

(* ------------------------------------------------------------------------ *)
(* Strings                                                                  *)
(* ------------------------------------------------------------------------ *)

/// The character an escape denotes, or `None` if the escape is not one we have.
///
/// Enumerated rather than defaulting to the character itself: `"\q"` is a typo
/// far more often than it is an intent, and a lexer that silently accepts it
/// makes the escape set unknowable to a reader.
let escape_char (c:C.char) : Tot (option C.char) =
  if c = 'n'  then Some '\n'
  else if c = 't'  then Some '\t'
  else if c = 'r'  then Some '\r'
  else if c = '"'  then Some '"'
  else if c = '\\' then Some '\\'
  else None

/// Scan a double-quoted literal, the opening quote already consumed.
///
/// NEWLINES ARE ORDINARY CONTENT (D-65). A string runs to its closing quote
/// however many lines that takes, as in Perl, so a multi-line literal needs no
/// heredoc and no continuation character. The cost is that an unclosed quote
/// swallows the rest of the input and is reported at EOF rather than at the end
/// of the line — the same trade the `{` … `}` bracket rule already makes.
///
/// STILL ZERO LOOKAHEAD (D-30). Two states — in-string and after-backslash —
/// and every decision is a predicate on the one character in hand. A DFA with
/// two states is still a DFA, which is what the planned CFG-to-recursive-descent
/// generator needs; what would break the rule is deciding on the NEXT
/// character, and nothing here does.
let rec take_string (acc:list C.char) (cs:list C.char)
  : Tot (either string (r:(list C.char & list C.char) { length (snd r) <= length cs }))
        (decreases cs) =
  match cs with
  | [] -> Inl "unterminated string: no closing '\"' before end of input"
  | c :: r ->
    if c = '"' then Inr (rev acc, r)
    else if c = '\\'
    then (match r with
          | []      -> Inl "unterminated string: input ends in a backslash escape"
          | e :: r' ->
            (match escape_char e with
             | None    -> Inl ("unknown string escape '\\"
                               ^ S.string_of_list [e]
                               ^ "'; the escapes are \\n \\t \\r \\\" \\\\")
             | Some ch -> (match take_string (ch :: acc) r' with
                           | Inl m  -> Inl m
                           | Inr (str, rest) -> Inr (str, rest))))
    else (match take_string (c :: acc) r with
          | Inl m           -> Inl m
          | Inr (str, rest) -> Inr (str, rest))

(* ------------------------------------------------------------------------ *)
(* The main loop                                                            *)
(* ------------------------------------------------------------------------ *)

/// Classify a completed word run. Sigils are stripped here; `--` becomes its
/// own token; anything numeric becomes a literal.
let classify_run (cs:list C.char) : Tot (either string token) =
  match cs with
  | [] -> Inl "empty token"
  | c :: rest ->
    if cs = ['-'; '-'] then Inr TkArrow
    else if c = '$' then
      (match rest with
       | [] -> Inl "bare '$' with no name"
       | _  -> Inr (TkDollar (S.string_of_list rest)))
    else if c = '#' then
      (match rest with
       | [] -> Inl "bare '#' with no name"
       | _  -> Inr (TkHash (S.string_of_list rest)))
    else if c = '!' then
      (match rest with
       | [] -> Inl "bare '!' with no name"
       | _  -> Inr (TkBang (S.string_of_list rest)))
    else
      (match int_of_run cs with
       | Some n -> Inr (TkInt n)
       | None   -> Inr (TkWord (S.string_of_list cs)))

let rec lex_go (acc:list token) (cs:list C.char)
  : Tot (either string (list token)) (decreases (length cs)) =
  match cs with
  | [] -> Inr (rev acc)
  | c :: r ->
    if is_space c then lex_go acc r
    else if c = '\\' then lex_go acc (skip_line r)
    else if c = '{' then lex_go (TkLBrace :: acc) r
    else if c = '}' then lex_go (TkRBrace :: acc) r
    else if c = '(' then lex_go (TkLParen :: acc) r
    else if c = ')' then lex_go (TkRParen :: acc) r
    else if c = '[' then lex_go (TkLBrack :: acc) r
    else if c = ']' then lex_go (TkRBrack :: acc) r
    else if c = ':' then lex_go (TkColon :: acc) r
    else if c = '"'
    then (match take_string [] r with
          | Inl e            -> Inl e
          | Inr (str, rest)  -> lex_go (TkStr (S.string_of_list str) :: acc) rest)
    else
      let (run, rest) = take_run [c] r in
      (match classify_run run with
       | Inl e  -> Inl e
       | Inr tk -> lex_go (tk :: acc) rest)

let lex (src:string) : Tot (either string (list token)) =
  lex_go [] (S.list_of_string src)

(* ------------------------------------------------------------------------ *)
(* Rendering (diagnostics)                                                  *)
(* ------------------------------------------------------------------------ *)

let render_token (t:token) : Tot string =
  match t with
  | TkWord w   -> w
  | TkInt n    -> string_of_int n
  | TkStr s    -> "\"" ^ s ^ "\""
  | TkArrow    -> "--"
  | TkLBrace   -> "{"
  | TkRBrace   -> "}"
  | TkLParen   -> "("
  | TkRParen   -> ")"
  | TkLBrack   -> "["
  | TkRBrack   -> "]"
  | TkColon    -> ":"
  | TkDollar n -> "$" ^ n
  | TkHash n   -> "#" ^ n
  | TkBang n   -> "!" ^ n
