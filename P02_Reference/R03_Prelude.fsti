module R03_Prelude

/// P02, module 03: the standard dictionary.
///
/// SUMMARY
///   Word ids for the built-in primitives, the dictionary binding them, and
///   convenience constructors for building `term`s by hand until P03's parser
///   exists.
///
/// The primitives here are exactly those a reference interpreter can implement
/// without deciding an open question. Floating-point arithmetic is absent on
/// purpose: IEEE-754 semantics are unsettled (D06 6), and a reference
/// implementation that guessed would become the de facto specification.

open FStar.List.Tot
open M01_Kinds
open M04_Effects
open M05_Terms
open R01_Runtime

(* ------------------------------------------------------------------------ *)
(* Word ids                                                                 *)
(* ------------------------------------------------------------------------ *)

val w_add : word_id
val w_sub : word_id
val w_mul : word_id
val w_div : word_id
val w_mod : word_id
val w_lt  : word_id
val w_le  : word_id
val w_eq  : word_id
val w_not : word_id
val w_and : word_id
val w_or  : word_id

/// The boolean constants, as ordinary words bound to `WDef (bool_lit _)`
/// rather than as a lexer or elaborator special case.
///
/// Making them words costs nothing — specialization inlines a `WDef` whose
/// body is a literal — and buys two things: they shadow like any other name,
/// and neither the lexer nor `E04` grows a case for them. Until now there was
/// no way to write a `bool` at all, so `and`/`or`/`not` were reachable only
/// through a comparison.
val w_true  : word_id
val w_false : word_id

/// The first id available to user definitions. Kept explicit so P03 can
/// allocate above the primitives without a magic constant.
/// Effect 0 is `IO`, reserved for the host. See the note in the implementation:
/// no catcat program can handle it, because the surface `effect` declaration
/// allocates effect ids from 1 upward, so an `IO` operation always escapes to
/// `R05`'s caller — which is the only place that can actually perform one.
val eff_io  : eff_id
val w_print : word_id
val w_read  : word_id

val w_user_base : word_id

(* ------------------------------------------------------------------------ *)
(* The dictionary                                                           *)
(* ------------------------------------------------------------------------ *)

val prelude : rdict

(* ------------------------------------------------------------------------ *)
(* Term construction helpers                                                *)
(* ------------------------------------------------------------------------ *)

/// `i64` literal.
val int_lit (n:int) : Tot term

/// `bool` literal.
val bool_lit (b:bool) : Tot term

/// Left-associated juxtaposition of a list of terms, matching source reading
/// order: `[a; b; c]` becomes `a b c`.
val cat (ts:list term) : Tot term
