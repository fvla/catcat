module E02_Ast

/// P03, module 02: the surface syntax tree.
///
/// SUMMARY
///   What the parser produces and the elaborator consumes. Deliberately close
///   to the source text: names are still strings, the stack order is still the
///   surface order, and locals are still named.
///
/// The gap between this and `M05_Terms.term` is exactly what E04 closes:
///   * names resolve to `word_id`s,
///   * signature order reverses (surface bottom-to-top, core head-is-top),
///   * `$x` locals become `SPick`/`SRoll` stack access.
///
/// SCOPE OF THIS PASS
///   The subset implemented is literals, words, blocks, signatures with named
///   parameters, and `define`. Deliberately absent, each already specified in
///   D05 and each needing its own pass: macros, modules and `::`, generics
///   `[]`, effect rows and handler syntax, sums and classes, strings, `let`
///   destructuring, and `.` member access. The AST carries `sty_generic` and
///   an effect list so those extensions do not have to reshape it.

open FStar.List.Tot

(* ------------------------------------------------------------------------ *)
/// Surface types                                                           *)
(* ------------------------------------------------------------------------ *)

/// `sty_name` covers both primitives (`i64`) and nominal references; the
/// elaborator decides which by looking the name up. Keeping them one case here
/// means the parser needs no type table.
type sty =
  | StyName : string -> sty
  | StyBox  : sty -> sty
  | StyRc   : sty -> sty
  /// `#T` — a parametric type variable. Parsed and rejected by E04 for now;
  /// present so generics do not require an AST change.
  | StyVar  : string -> sty

let rec sty_size (t:sty) : Tot pos =
  match t with
  | StyName _ -> 1
  | StyVar _  -> 1
  | StyBox u  -> 1 + sty_size u
  | StyRc u   -> 1 + sty_size u

(* ------------------------------------------------------------------------ *)
(* Signatures                                                               *)
(* ------------------------------------------------------------------------ *)

/// One input slot. `sp_name` is `Some` for `$x:i64`, `None` for a bare `i64`.
type sparam = {
  sp_name : option string;
  sp_ty   : sty;
}

/// A surface signature, in SOURCE order: bottom of stack first, top on the
/// right. `( i64 bool -- i64 )` has `bool` on top. E04 reverses this.
type ssig = {
  ss_in   : list sparam;
  ss_out  : list sty;
  ss_eff  : list string;
}

(* ------------------------------------------------------------------------ *)
(* Terms                                                                    *)
(* ------------------------------------------------------------------------ *)

type sterm =
  | StInt   : int -> sterm
  | StWord  : string -> sterm
  /// `$x` — a read of a named local.
  | StVar   : string -> sterm
  /// `{ … }` — a block. Currently a `define` body or a branch of `StCase`;
  /// handler and macro consumers arrive with those features.
  | StBlock : list sterm -> sterm
  /// Case analysis: one branch per variant of the sum on top of the stack.
  ///
  /// This is the surface form macros target, not a form anyone writes directly
  /// yet — surface `if` expands to it (D-33). Branches are listed in TAG
  /// order, so for a `bool` the FALSE branch comes first. Stated here as well
  /// as in `M05.TBoolSum` because a silent reversal would typecheck.
  | StCase  : list (list sterm) -> sterm
  /// `handle E over ( … ) init { … } { op { … } … } { body }`.
  ///
  /// The state segment is in SURFACE order (bottom-to-top); `E04` reverses it,
  /// as it does every signature. Implementations are keyed by operation name,
  /// resolved against the effect named here.
  | StHandle : string -> list sty -> list sterm
             -> list (string & list sterm) -> list sterm -> sterm

let rec sterm_size (t:sterm) : Tot pos =
  match t with
  | StInt _    -> 1
  | StWord _   -> 1
  | StVar _    -> 1
  | StBlock ts -> 1 + sterms_size ts
  | StCase bs  -> 1 + sterm_lists_size bs
  | StHandle _ _ i im b -> 1 + sterms_size i + simpls_size im + sterms_size b

and sterms_size (ts:list sterm) : Tot nat =
  match ts with
  | []     -> 0
  | t :: r -> sterm_size t + sterms_size r

/// One charged per implementation, for the same reason `sterm_lists_size`
/// charges one per branch: an empty implementation block is legitimate
/// (`reset { }` on a unit state) and would otherwise make the measure
/// non-strict on the list-to-list edge.
and simpls_size (im:list (string & list sterm)) : Tot nat =
  match im with
  | []           -> 0
  | (_, ts) :: r -> 1 + sterms_size ts + simpls_size r

/// Note the `1 +` per branch. Without it an EMPTY branch — `else { }`, which
/// is exactly the shape the else-less `if` expands to — makes this measure
/// non-strict on the list-to-list edge, and the rank trick used elsewhere in
/// the project does not rescue it because both sides sit at the same rank.
/// Charging one for each branch restores a strict decrease on the first
/// component, so the ranks below are documentation rather than load-bearing.
and sterm_lists_size (bs:list (list sterm)) : Tot nat =
  match bs with
  | []     -> 0
  | b :: r -> 1 + sterms_size b + sterm_lists_size r

(* ------------------------------------------------------------------------ *)
(* Declarations                                                             *)
(* ------------------------------------------------------------------------ *)

type sdecl =
  /// `define name ( sig ) { body }`
  | SdDefine      : string -> ssig -> list sterm -> sdecl
  /// `define name { body }` — signature inferred from the body (D-31).
  | SdDefineInfer : string -> list sterm -> sdecl
  /// `effect E { declare op ( sig ) … }`.
  ///
  /// Signatures are MANDATORY here, which is where D-31's carve-out finally
  /// gets enforced: an operation has no body to infer from, so a declaration
  /// without a written signature has nothing to mean.
  | SdEffect      : string -> list (string & ssig) -> sdecl
  /// `locate name` — print what `name` is: a macro production, a primitive, or
  /// a definition decompiled back to surface syntax (E05_Locate).
  ///
  /// A declaration rather than a word, for the same reason `define` is one: its
  /// argument is a NAME, not a value, so it has nothing to do with the stack
  /// and cannot be given a signature. Forth reaches the same shape from the
  /// other direction, by making `LOCATE` immediate.
  | SdLocate      : string -> sdecl
  /// A bare sequence of terms, evaluated against the current REPL stack.
  | SdExpr   : list sterm -> sdecl

(* ------------------------------------------------------------------------ *)
(* Occurrence counting                                                      *)
(* ------------------------------------------------------------------------ *)

/// How many times `$x` is read in a body.
///
/// E04 needs this to choose between `SPick` and `SRoll`: a copyable local can
/// be read any number of times (each a pick), while a non-copyable one must be
/// read exactly once (a roll, which consumes it). Counting occurrences up front
/// is what makes that decision without a liveness analysis.
/// Measure follows the M01/M05 pattern: rank orders `list(1) > term(0)`.
let rec count_var (x:string) (t:sterm)
  : Tot nat (decreases %[(sterm_size t <: nat); 0]) =
  match t with
  | StVar y    -> if y = x then 1 else 0
  | StBlock ts -> count_var_list x ts
  /// A read inside a branch is FORCED to count as repeated, whatever the
  /// actual number is. The elaborator compiles a sole read to a `roll`, which
  /// consumes the slot — and a slot consumed in one branch but not the other
  /// leaves the two branches with different stacks, so `if { } then { $x }
  /// endif` would be rejected for a reason that has nothing to do with what
  /// the programmer wrote.
  ///
  /// Forcing `pick` instead costs an end-of-body drop and requires `Copy`,
  /// which is the honest requirement: a value read under a condition cannot be
  /// statically known to be moved exactly once.
  | StCase bs  -> let n = count_var_lists x bs in
                  if n = 0 then 0 else n + 1
  /// Only the BODY is counted. A handler's initialiser and implementations run
  /// on their own stacks — the state segment, plus the operation's arguments —
  /// so an enclosing definition's locals are not in scope there and `E04`
  /// rejects a read of one. Counting them would inflate the count for a read
  /// that cannot occur.
  ///
  /// The body needs no inflation either, unlike a branch: it runs exactly once.
  | StHandle _ _ _ _ b -> count_var_list x b
  | _          -> 0

and count_var_list (x:string) (ts:list sterm)
  : Tot nat (decreases %[sterms_size ts; 1]) =
  match ts with
  | []     -> 0
  | t :: r -> count_var x t + count_var_list x r

/// Counting ACROSS branches, not within one, so a local read in either arm of
/// an `if` counts as read. That is the conservative direction: over-counting
/// costs a `pick` and an end-of-body drop where a `roll` would have done,
/// while under-counting would compile a read to a move in a branch that does
/// not run.
and count_var_lists (x:string) (bs:list (list sterm))
  : Tot nat (decreases %[sterm_lists_size bs; 2]) =
  match bs with
  | []     -> 0
  | b :: r -> count_var_list x b + count_var_lists x r
