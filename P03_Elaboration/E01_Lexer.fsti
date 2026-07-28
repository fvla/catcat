module E01_Lexer

/// P03, module 01: the lexer.
///
/// SUMMARY
///   Source text to a flat token list. No nesting, no lookahead — bracket
///   matching is the parser's job (E03).
///
/// The vocabulary is fixed by D05 and deliberately small. Two properties of
/// that design show up directly here:
///
///   * **Brackets are self-delimiting.** `{hypot dup *}` and `{ hypot dup * }`
///     lex identically, because `{ } ( ) [ ] :` terminate a word run without
///     needing surrounding space. This is the divergence from Forth that buys
///     precise tooling.
///   * **Sigils are lexical.** `$x`, `#T`, `!IO` are recognised by their first
///     character, so the parser never needs lookahead to know which region of
///     a signature it is in.
///
/// EXTRACTION DISCIPLINE
///   P03 follows the same first-order subset as P02 (see `R01_Runtime.fsti`):
///   no closures, no higher-order functions, no function-typed record fields.
///   The elaborator is a compiler pass, and compiler passes must be able to
///   extract to catcat as well as OCaml.

open FStar.List.Tot

(* ------------------------------------------------------------------------ *)
(* Tokens                                                                   *)
(* ------------------------------------------------------------------------ *)

type token =
  | TkWord   : string -> token
  | TkInt    : int -> token
  /// `--`, the input/output separator inside a signature. Lexed as its own
  /// token rather than a word so the parser cannot confuse it with a
  /// user-defined word that happens to be named `--`.
  | TkArrow  : token
  | TkLBrace : token
  | TkRBrace : token
  | TkLParen : token
  | TkRParen : token
  | TkLBrack : token
  | TkRBrack : token
  | TkColon  : token
  /// Sigil tokens carry the name with the sigil stripped.
  | TkDollar : string -> token   // $x   local
  | TkHash   : string -> token   // #T   parametric type
  | TkBang   : string -> token   // !IO  effect

(* ------------------------------------------------------------------------ *)
(* Character classes                                                        *)
(* ------------------------------------------------------------------------ *)

val is_space (c:FStar.Char.char) : Tot bool

/// The self-delimiting punctuation. A word run ends here without whitespace.
val is_delim (c:FStar.Char.char) : Tot bool

(* ------------------------------------------------------------------------ *)
(* Lexing                                                                   *)
(* ------------------------------------------------------------------------ *)

/// `Inl` carries an error message; `Inr` the tokens.
///
/// A `\` begins a line comment, as in Forth. `(` is NOT a comment here — it
/// opens a type annotation (D05 §1), which is the one place this language
/// reverses a Forth convention rather than dropping it.
val lex (src:string) : Tot (either string (list token))

val render_token (t:token) : Tot string
