module R06_SelfHost

/// P02, module 06: extracting the interpreter to catcat itself.
///
/// SUMMARY
///   The second extraction target. R01-R05 extract to OCaml today; this module
///   works out what it takes to extract the same code to catcat, which is what
///   self-hosting means under D06 2 (F* is the source of truth, and the catcat
///   compiler is emitted from it rather than hand-written).
///
///   It also records a blocker found by attempting exactly that, and its
///   resolution -- see 3.
///
/// ============================================================
/// 1. What "extract to catcat" means
/// ============================================================
///
///   A catcat program IS a value of `M05_Terms.term`. So extraction to catcat
///   is a total function
///
///       emit : <F* first-order subset> -> term
///
///   and its correctness statement is that the emitted term, run on the
///   machine of R02, computes what the original F* function computes.
///
///   This is a strictly easier target than a textual backend: there is no
///   pretty-printer to trust and no parser round-trip, because the AST is the
///   artifact. A textual form is a convenience for humans, produced from the
///   term, and never on the trusted path.
///
/// ============================================================
/// 2. The construct mapping
/// ============================================================
///
///   The subset discipline in R01's header exists to make this table total.
///   Each F* construct on the left has exactly one catcat image:
///
///     F* (first-order subset)        catcat
///     ---------------------------    -------------------------------------
///     top-level function             a defined word (`TWord` + dictionary)
///     function parameters            input segment of the signature
///     structural recursion           self-reference by `word_id`
///     inductive constructor          `PInj` at the right tag
///     `match` on an inductive        `TCase` with one block per variant
///     tuple / record                 stack segment, sealed by `PPack`
///     field projection               `PUnpack` then shuffle
///     `let x = e in ...`             elaborated to shuffles (D05 3)
///     `if`                           `TCase` on the `bool` encoding
///
///   Nothing in R01-R05 falls outside this table, by construction. That is the
///   whole reason for banning closures, higher-order functions and
///   function-typed record fields: each would need a catcat image that does
///   not exist.
///
/// ============================================================
/// 3. RESOLVED: recursive types
/// ============================================================
///
///   Attempting the encoding surfaced a genuine gap in the specification, not
///   a gap in this module.
///
///   `M01_Kinds.dtype` used to be
///
///       TPrim prim | TSeal nom_id (list cap) (list dtype) | TSum (list (list dtype))
///
///   Every case was structural and finite. `TSeal` carried its representation
///   INLINE rather than referring to a declaration, so there was no way to
///   write a type that mentions itself. catcat as specified therefore could
///   not express
///
///       List[#T] = Nil | Cons #T List[#T]
///
///   and could not express `rvalue`, `term`, `kframe` or `kont` -- every data
///   type the interpreter actually manipulates.
///
///   This was not an oversight in M01 so much as a cost that had not been
///   priced. Carrying the representation inline is what kept M01-M07
///   environment-free, which in turn kept M07's denotation a plain function
///   rather than one parameterised by a signature context. That was a real
///   simplification for the proofs; it just also foreclosed self-hosting.
///
///   THE FIX (D-25 in NOTES/N01_Decisions.md): `dtype` gained three cases --
///
///       TName : nom_id -> dtype     -- an incomplete type: an explicit forward reference
///       TBox  : dtype -> dtype      -- owning unique pointer   (Rust Box)
///       TRc   : dtype -> dtype      -- shared refcounted ptr   (Rust Rc)
///
///   -- and recursion is legal only THROUGH A POINTER, exactly as in Rust and
///   C++:
///
///       List = TSum [ [] ; [TPrim PI64; TBox (TName list_id)] ]
///
///   This sidesteps every cost the fix was originally expected to have:
///
///     * `dtype` VALUES stay finite trees, because `TName` is a leaf. The
///       recursion lives at the declaration level, not in the syntax tree, so
///       there is no positivity obligation and no termination problem --
///       neither a coinductive nor a fuel-bounded `has_cap` was needed.
///     * NO TYPE ENVIRONMENT is needed in M01/M02, because a pointer's
///       capabilities do not depend on its pointee: `has_cap` never looks
///       through `TBox`/`TRc`, so it never reaches a `TName`, so it never has
///       to resolve one. `M02.value`/`vstack` did not need to become
///       environment-indexed either -- `VName` simply wraps a value of the
///       pointee type, unchecked against the name it sits behind, and the
///       mutual family keeps its ordinary structural-subterm justification.
///
///   An environment is needed only to *unfold* a name, which is strictly a
///   typechecking concern (below), not a value-representation one.
///
///   M01 also gained `wf : dtype -> bool`, which rejects a bare `TName` not
///   behind a pointer -- the condition that keeps layout finite, exactly as
///   C++ rejects `struct S { S field; }`.
///
///   `TBox` and `TRc` have neither `Copy` nor `Drop`, so both are linear: a
///   `Box` cannot be duplicated (that would alias unique ownership) or
///   discarded by `pop` (that would leak, since freeing is an operation); an
///   `Rc` likewise, since cloning increments a count and releasing decrements
///   one. Both are consumed through interface words instead
///   (`PBoxNew`/`PBoxOpen`, `PRcNew`/`PRcClone`/`PRcDrop`/`PRcRead` in
///   M05/M06) -- a strong confirmation of D-08 (capabilities-plus-`Clone`-as-
///   an-interface-word is exactly the shape `Box`/`Rc` need, chosen before
///   they existed), and the first instance of the recurring pattern in D-26.
///
///   WHAT REMAINS: `M06_Typing`'s `PRoll`/`PUnroll` rules currently accept
///   `PRoll n d` and `PUnroll n d` for ANY well-formed `d` -- `d` is not
///   checked against what `n` actually names, because the typing environment
///   carries no declaration table yet. Closing this needs a
///   `w_decl : nom_id -> dtype` field and a check that `d = w_decl n`. By
///   construction this is the ONLY place M01-M06 need such an environment --
///   `has_cap` and the value representation never do, as above. This is a
///   soundness gap in M06's typechecker, not a barrier to expressing
///   recursive data: it does not stand in the way of writing catcat-hosted
///   recursive types, only of the typechecker catching a mismatched
///   roll/unroll pair.
///
///   Acknowledged cost, unchanged by the fix: every recursive node is a heap
///   cell. Inefficient, to be optimized later.
///
///   Note also that the reference interpreter does NOT need any of this to
///   run: its own data lives in F*/OCaml, where recursion is available. Only
///   the catcat-hosted version needs it. That is why the gap survived until an
///   actual extraction attempt.
///
/// ============================================================
/// 4. What this module contains
/// ============================================================
///
///   The part of the encoding that works today -- non-recursive types -- so
///   that the mapping is exercised rather than merely described. The
///   recursive types (`rvalue`, `term`, `kont` -- see "Where the encoding
///   stops" below) are, since 3, expressible in principle against the current
///   `dtype`; writing them out is separate work, not done in this module.

open FStar.List.Tot
open M01_Kinds
open M04_Effects
open M05_Terms
open R01_Runtime

(* ------------------------------------------------------------------------ *)
(* Encoding non-recursive data                                              *)
(* ------------------------------------------------------------------------ *)

/// A C-like enum: `n` variants, none carrying a payload.
let rec empty_segs (n:nat) : Tot (list seg) (decreases n) =
  if n = 0 then [] else [] :: empty_segs (n - 1)

let encode_enum (n:nat) : Tot dtype = TSum (empty_segs n)

let lemma_enum_arity (n:nat) : Lemma (length (empty_segs n) == n) =
  let rec aux (m:nat) : Lemma (ensures length (empty_segs m) == m) (decreases m) =
    if m = 0 then () else aux (m - 1)
  in aux n

/// `M01_Kinds.cap` as a catcat type: two nullary variants.
let enc_cap : dtype = encode_enum 2

/// `M04_Effects.stage` as a catcat type.
let enc_stage : dtype = encode_enum 2

/// `R01_Runtime.prim_word` as a catcat type: eleven nullary variants.
let enc_prim_word : dtype = encode_enum 11

/// `bool` is already primitive, but the encoding is worth naming because
/// `if` compiles to `TCase` over it and the branch order matters: variant 0 is
/// `false`, variant 1 is `true`, matching the numeric convention.
let enc_bool : dtype = TSum [[]; []]

/// A product, i.e. a record with named fields erased to positions. This is the
/// one encoding that needs no new machinery at all -- a product is a stack
/// segment (D02 1), and sealing gives it an identity.
let encode_record (n:nom_id) (caps:list cap) (fields:seg) : Tot dtype =
  TSeal n caps fields

(* ------------------------------------------------------------------------ *)
(* Where the encoding stops                                                 *)
(* ------------------------------------------------------------------------ *)

/// Deliberately absent, but no longer for the reason in 3:
///
///     enc_rvalue : dtype     -- needs `RSeal : nom_id -> list rvalue -> ...`
///     enc_term   : dtype     -- needs `TSeq : term -> term -> term`
///     enc_kont   : dtype     -- needs `list kframe`
///
/// Each of these needs a type that mentions itself, which is exactly what
/// `TName`/`TBox` are now for -- the same way `List` in 3 closes its
/// recursion through a pointer. So all three are WRITABLE in principle
/// against the current `dtype`. What remains is writing them out declaration
/// by declaration and discharging H1 for the recursive cases below --
/// separate work, not done in this module. Writing them here with a
/// placeholder would still misrepresent the state of the design, so they stay
/// absent rather than stubbed. `list` itself is the smallest example: it is
/// the type the whole interpreter is built from, and it is exactly what was,
/// until 3, inexpressible.

(* ------------------------------------------------------------------------ *)
(* Obligations                                                              *)
(* ------------------------------------------------------------------------ *)

/// H1  ENCODING FAITHFULNESS.
///     For each encoded type, the catcat value space is in bijection with the
///     F* one. Trivial for enums; the content is in the recursive cases, once
///     `enc_rvalue`/`enc_term`/`enc_kont` (4) are written.
///
/// H2  EMISSION CORRECTNESS.
///     For an F* function `f` in the subset and its emitted word `w`:
///     running `w` on the encoding of `f`'s arguments yields the encoding of
///     `f`'s result. This is the theorem that makes the self-hosted compiler
///     inherit the F* proofs rather than needing its own.
///
/// H3  SUBSET CONFORMANCE.
///     Every definition in R01-R05 lies in the first-order subset. Currently
///     maintained by discipline and review. It should become a checked
///     property -- a syntactic pass over the extracted AST -- because a single
///     accidental closure silently breaks self-hosting and would not be caught
///     by any test that only runs the OCaml build.
