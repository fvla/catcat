module R01_Runtime

/// P02, module 01: runtime representation.
///
/// SUMMARY
///   Values with their type indices erased, plus a first-order dictionary.
///   This is what the interpreter actually manipulates; P01's intrinsically
///   typed `vstack` is what the specification reasons about. R04 bridges them.
///
/// WHY ERASED
///   M02's `vstack` makes ill-shaped stacks unrepresentable, which is exactly
///   right for proving and exactly wrong for running: it would force the
///   interpreter to carry type indices at runtime, and neither OCaml nor catcat
///   extraction wants that. Types are erased here and the shape discipline is
///   recovered as a theorem (R04) rather than a representation invariant.
///
/// EXTRACTION DISCIPLINE
///   Everything in P02 is written in a first-order total subset of F* so that
///   it extracts to BOTH OCaml and catcat. The rules, which apply to every
///   module in this phase:
///
///     * No closures, no higher-order functions, no partial application.
///       catcat has no runtime function values (D02 6), so a continuation must
///       be DATA. R02 defunctionalises accordingly.
///     * No function-typed record fields. M04's `sig_env` uses them; the
///       interpreter uses association lists instead.
///     * All recursion structural, with explicit measures where F* needs them.
///     * Plain inductives only: no typeclasses, no indexed families, no
///       implicit arguments that survive erasure.
///
///   Violating any of these is not a style problem; it makes the module
///   un-extractable to catcat and therefore blocks self-hosting.

open FStar.List.Tot
open M01_Kinds
open M04_Effects
open M05_Terms

(* ------------------------------------------------------------------------ *)
(* Values                                                                   *)
(* ------------------------------------------------------------------------ *)

/// A runtime value. All integer primitives collapse to `RInt`: the width lives
/// in the static type, and M06 has already checked it, so the interpreter does
/// not re-derive it.
///
/// `RBits` carries a float as an opaque bit pattern. The reference interpreter
/// deliberately does not implement floating-point arithmetic -- IEEE-754
/// semantics are an open question (D06 6) and a reference implementation
/// should not invent an answer.
/// `RBox`/`RRc` model pointers by direct nesting rather than by a heap and an
/// address. Sound for both, for different reasons:
///
///   * `Box` is uniquely owned, so no sharing is observable and nesting is
///     indistinguishable from indirection.
///   * `Rc` carries no refcount here. The count decides only WHEN a destructor
///     runs, and the reference interpreter has no observable deallocation, so
///     with immutable payloads nesting is again indistinguishable. This
///     reopens if interior mutability or observable destruction is added
///     (N02 Q-04).
///
/// There is no `RName`: rolling and unrolling an incomplete type is a
/// type-level operation with no runtime content, so R04 erases `VName` to its
/// payload.
type rvalue =
  | RInt  : int -> rvalue
  | RBool : bool -> rvalue
  | RUnit : rvalue
  | RBits : int -> rvalue
  | RSeal : nom_id -> list rvalue -> rvalue
  | RSum  : nat -> list rvalue -> rvalue
  | RBox  : rvalue -> rvalue
  | RRc   : rvalue -> rvalue

/// Head is top of stack, matching M02's convention exactly. Any divergence
/// here would silently invalidate R04's simulation argument.
type rstack = list rvalue

(* ------------------------------------------------------------------------ *)
(* Primitive operations                                                     *)
(* ------------------------------------------------------------------------ *)

type prim_op =
  | OAddI | OSubI | OMulI | ODivI | OModI
  | OLtI  | OLeI  | OEqI
  | ONot  | OAnd  | OOr

(* ------------------------------------------------------------------------ *)
(* The dictionary                                                           *)
(* ------------------------------------------------------------------------ *)

/// What a word resolves to. The three cases are the runtime residue of D03's
/// unification: a user definition, an interface operation awaiting a handler,
/// or a compiler-known primitive.
/// `noeq`: `term` carries literals whose representation may be an abstract
/// float type (M01), so `rword` cannot support decidable equality. Nothing
/// compares words structurally, only their ids.
noeq type rword =
  | WDef  : term -> rword
  | WOp   : eff_id -> rword
  | WPrim : prim_op -> rword

/// An association list, not a map and not a function. A function-typed field
/// would be unextractable to catcat; a balanced map would be premature.
type rdict = list (word_id & rword)

val dict_lookup (d:rdict) (w:word_id) : Tot (option rword)

val dict_extend (d:rdict) (w:word_id) (rw:rword) : Tot rdict

(* ------------------------------------------------------------------------ *)
(* Stack helpers                                                            *)
(* ------------------------------------------------------------------------ *)

/// Split the top `n` values off, top-first, or fail if the stack is too short.
/// The runtime counterpart of `M02.vsplit`; the failure case is unreachable
/// for well-typed programs, which is precisely R04's obligation E2.
val take (n:nat) (s:rstack) : Tot (option (list rvalue & rstack))

/// Push a segment back, top-first. Counterpart of `M02.vappend`.
///
/// Defined here rather than declared, deliberately: R04's simulation argument
/// needs it to reduce, and an opaque `give` would force a lemma for every step
/// of an argument that is otherwise definitional.
let give (vs:list rvalue) (s:rstack) : Tot rstack = vs @ s

val lemma_take_give (n:nat) (s:rstack)
  : Lemma (match take n s with
           | Some (vs, rest) -> give vs rest == s
           | None            -> True)
