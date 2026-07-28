module M01_Kinds

/// catcat core specification, module 01: types and capabilities.
///
/// This module fixes the universe of data types. Three design decisions from
/// P00_Design/D02_Core_Calculus.md are realised here:
///
///   1. Products are NOT a type former. A product is a stack segment -- a
///      `list dtype` -- and `TSeal` is what turns a segment into a single
///      denotable type with a nominal identity.
///   2. Sums ARE a type former. A stack has a statically known shape, so a
///      construct whose shape differs per branch cannot be encoded as a
///      segment. `TSum` is the primitive tagged union that `option`, `result`
///      and effect-handler dispatch are all built from.
///   3. Linearity is a capability, not a default. `TSeal` carries the
///      capability set of the type it introduces, so a sealed type may drop
///      capabilities its representation happens to have.

open FStar.List.Tot

(* ------------------------------------------------------------------------ *)
(* Primitives                                                               *)
(* ------------------------------------------------------------------------ *)

type prim =
  | PI8  | PI16 | PI32 | PI64
  | PU8  | PU16 | PU32 | PU64
  | PF32 | PF64
  | PBool
  | PUnit

/// Floating point is abstract in the specification. The core calculus never
/// inspects a float, so an abstract type is enough to state and prove every
/// theorem in M02-M11; a compiler phase gives these an IEEE-754 meaning.
assume new type f32 : Type0
assume new type f64 : Type0

let sint (n:pos) = x:int { -(pow2 (n - 1)) <= x /\ x < pow2 (n - 1) }
let uint (n:pos) = x:int { 0 <= x /\ x < pow2 n }

/// The F* type denoted by a primitive. Bounds are mathematical rather than
/// machine words: wrapping is a property of the *operations* (M05), not of the
/// value space, and keeping the value space clean keeps M02 free of arithmetic.
let prim_rep (p:prim) : Type0 =
  match p with
  | PI8   -> sint 8   | PI16  -> sint 16  | PI32  -> sint 32  | PI64  -> sint 64
  | PU8   -> uint 8   | PU16  -> uint 16  | PU32  -> uint 32  | PU64  -> uint 64
  | PF32  -> f32      | PF64  -> f64
  | PBool -> bool
  | PUnit -> unit

(* ------------------------------------------------------------------------ *)
(* Capabilities                                                             *)
(* ------------------------------------------------------------------------ *)

/// `CCopy` licenses `dup`; `CDrop` licenses `pop`. A type carrying neither is
/// linear: it must be consumed exactly once, by a word that explicitly takes
/// it. This is what makes a `delete` word meaningful rather than a synonym for
/// `pop` -- see D03.
///
/// `Clone` is deliberately absent: it is an ordinary interface (a word you
/// call), not a capability the compiler consults, exactly as in Rust.
type cap =
  | CCopy
  | CDrop

/// Nominal identity for a sealed type. Resolution of these to source-level
/// names is an elaboration concern (P03), not a core one.
type nom_id = nat

(* ------------------------------------------------------------------------ *)
(* Types                                                                    *)
(* ------------------------------------------------------------------------ *)

/// `TSeal n caps repr` is a nominal type named `n`, represented by the stack
/// segment `repr`, exposing capability set `caps`.
///
/// Carrying `repr` inside the type rather than in a side table keeps M01-M07
/// entirely environment-free, which in turn keeps the denotation in M07 a
/// plain function rather than something parameterised by a signature context.
/// Name resolution reintroduces an environment in M06, where it belongs.
///
/// `TSum variants` is a tagged union; variant `i` carries the stack segment
/// `index variants i`.
///
/// `TName n` is an INCOMPLETE type: an explicitly annotated forward reference
/// to declaration `n`. `TBox t` is an owning unique pointer, `TRc t` a shared
/// refcounted one -- Rust's `Box` and `Rc`, deliberately named the same.
///
/// Together these are what make recursive types expressible. Recursion is legal
/// only THROUGH A POINTER, exactly as in Rust and C++:
///
///     List = TSum [ [] ; [TPrim PI64; TBox (TName list_id)] ]
///
/// The design pays for itself twice over:
///
///   * `dtype` VALUES stay finite trees, because `TName` is a leaf. So there is
///     no positivity obligation and no termination problem -- the recursion
///     lives at the declaration level, not in the syntax tree.
///   * No type environment is needed here, because A POINTER'S CAPABILITIES DO
///     NOT DEPEND ON ITS POINTEE. `has_cap` never looks through `TBox`/`TRc`,
///     so it never reaches a `TName`, so it never needs to resolve one. An
///     environment is required only to unfold a name, which typechecking a
///     `TUnroll` needs and the runtime does not.
///
/// Nullability needs no new machinery: `TSum [[]; [TBox t]]` is `Option[Box[t]]`,
/// the nullable pointer.
type dtype =
  | TPrim : prim -> dtype
  | TSeal : nom_id -> list cap -> list dtype -> dtype
  | TSum  : list (list dtype) -> dtype
  | TName : nom_id -> dtype
  | TBox  : dtype -> dtype
  | TRc   : dtype -> dtype

/// A stack segment. Also the specification's notion of "tuple".
type seg = list dtype

/// The sum a `bool` coerces to (`M05.TBoolSum`, D-33): two variants, neither
/// carrying a payload. Variant 0 is `false` and variant 1 is `true`.
///
/// Named here rather than written out at each use because the tag order is a
/// convention three modules have to agree on -- the typing rule, the machine,
/// and the elaborator that arranges surface `if` around it. Spelling it once
/// is what keeps them from drifting.
let bool_variants : list seg = [[]; []]

(* ------------------------------------------------------------------------ *)
(* Structural size, used only as a termination measure                      *)
(* ------------------------------------------------------------------------ *)

let rec dtype_size (t:dtype) : Tot pos =
  match t with
  | TPrim _          -> 1
  | TSeal _ _ repr   -> 1 + seg_size repr
  | TSum variants    -> 1 + variants_size variants
  | TName _          -> 1
  | TBox inner       -> 1 + dtype_size inner
  | TRc  inner       -> 1 + dtype_size inner

and seg_size (s:seg) : Tot nat =
  match s with
  | []      -> 0
  | t :: r  -> dtype_size t + seg_size r

and variants_size (vs:list seg) : Tot nat =
  match vs with
  | []      -> 0
  | v :: r  -> seg_size v + variants_size r

(* ------------------------------------------------------------------------ *)
(* Capability inference                                                     *)
(* ------------------------------------------------------------------------ *)

/// Primitives have every capability. A sealed type has exactly the
/// capabilities it declares -- narrowing is the point of sealing, and it is
/// how a `Counter` becomes linear even though `int` is not. A sum has a
/// capability when every variant's payload has it.
///
/// Termination measure. A plain size measure does not work: an empty variant
/// contributes size 0, so `variants_have_cap` -> `variants_have_cap` and
/// `variants_have_cap` -> `seg_has_cap` are only non-strict. The lexicographic
/// measure below adds a rank ordering `variants(2) > seg(1) > dtype(0)`, which
/// is acyclic precisely because the one edge that would close the cycle,
/// `has_cap (TSum vs)` -> `variants_have_cap vs`, always decreases the size
/// component. The final component breaks the remaining tie on
/// `variants_have_cap`; `seg_has_cap` needs no such tiebreak because
/// `dtype_size` is positive.
/// Pointers have NEITHER capability, so both are linear: a `Box` cannot be
/// duplicated (that would alias unique ownership) and cannot be discarded by
/// `pop` (that would leak, since freeing is an operation and not a no-op).
/// `Rc` likewise -- cloning increments a count and releasing decrements one, so
/// neither is a bitwise copy nor a silent discard. Both are therefore consumed
/// through interface words, which is precisely the shape D-08 already had.
///
/// Note what these two cases do NOT do: recurse into the pointee. That is what
/// keeps this function environment-free in the presence of `TName`.
let rec has_cap (c:cap) (t:dtype)
  : Tot bool (decreases %[(dtype_size t <: nat); 0; 0]) =
  match t with
  | TPrim _        -> true
  | TSeal _ caps _ -> mem c caps
  | TSum variants  -> variants_have_cap c variants
  | TName _        -> false
  | TBox _         -> false
  | TRc  _         -> false

and variants_have_cap (c:cap) (vs:list seg)
  : Tot bool (decreases %[variants_size vs; 2; length vs]) =
  match vs with
  | []     -> true
  | v :: r -> seg_has_cap c v && variants_have_cap c r

and seg_has_cap (c:cap) (s:seg)
  : Tot bool (decreases %[seg_size s; 1; 0]) =
  match s with
  | []     -> true
  | t :: r -> has_cap c t && seg_has_cap c r

let copyable (t:dtype) : bool = has_cap CCopy t
let droppable (t:dtype) : bool = has_cap CDrop t

/// A segment is linear when some component may be neither duplicated nor
/// discarded. Used by M06 to reject `dup`/`pop` and by D03's object model.
let linear_seg (s:seg) : bool = not (seg_has_cap CCopy s) || not (seg_has_cap CDrop s)

(* ------------------------------------------------------------------------ *)
(* Well-formedness                                                          *)
(* ------------------------------------------------------------------------ *)

/// `TName` is legal only behind a pointer. This is the condition that makes
/// recursive declarations have finite layout: the pointer is what breaks the
/// cycle, so a name reached without crossing one would be a type of infinite
/// size, exactly as `struct S { S field; }` is rejected in C++.
///
/// `under_ptr` is monotone -- once a pointer has been crossed it stays crossed
/// -- so `Box[Sum[... TName n ...]]` is accepted. Only the path from the root
/// matters, not the immediate parent.
let rec wf_dtype (under_ptr:bool) (t:dtype)
  : Tot bool (decreases %[(dtype_size t <: nat); 0; 0]) =
  match t with
  | TPrim _          -> true
  | TName _          -> under_ptr
  | TBox inner       -> wf_dtype true inner
  | TRc  inner       -> wf_dtype true inner
  | TSeal _ _ repr   -> wf_seg under_ptr repr
  | TSum variants    -> wf_variants under_ptr variants

and wf_variants (under_ptr:bool) (vs:list seg)
  : Tot bool (decreases %[variants_size vs; 2; length vs]) =
  match vs with
  | []     -> true
  | v :: r -> wf_seg under_ptr v && wf_variants under_ptr r

and wf_seg (under_ptr:bool) (s:seg)
  : Tot bool (decreases %[seg_size s; 1; 0]) =
  match s with
  | []     -> true
  | t :: r -> wf_dtype under_ptr t && wf_seg under_ptr r

/// A type usable as the shape of a stack slot: no dangling incomplete type.
let wf (t:dtype) : bool = wf_dtype false t

/// A bare name is never well formed at the top level -- the point of the rule.
let lemma_bare_name_ill_formed (n:nom_id) : Lemma (~(wf (TName n))) = ()

/// Behind a pointer it always is, whatever the name refers to. This is what
/// makes a recursive declaration expressible.
let lemma_boxed_name_wf (n:nom_id) : Lemma (wf (TBox (TName n))) = ()

/// Pointers are linear, both of them.
let lemma_pointers_linear (t:dtype)
  : Lemma (not (copyable (TBox t)) /\ not (droppable (TBox t)) /\
           not (copyable (TRc t))  /\ not (droppable (TRc t))) = ()

(* ------------------------------------------------------------------------ *)
(* Small facts                                                              *)
(* ------------------------------------------------------------------------ *)

/// Capability of a segment is exactly the conjunction over its members: the
/// property M06 needs when it splits a stack at a signature boundary.
let rec lemma_seg_has_cap_append (c:cap) (s1 s2:seg)
  : Lemma (ensures seg_has_cap c (s1 @ s2) == (seg_has_cap c s1 && seg_has_cap c s2))
          (decreases s1) =
  match s1 with
  | []     -> ()
  | _ :: r -> lemma_seg_has_cap_append c r s2

/// A sealed type's capabilities are independent of its representation. This is
/// the formal content of "sealing narrows": the theorem M10 appeals to when it
/// argues that a class can expose a linear interface over a copyable
/// representation.
let lemma_seal_caps (n:nom_id) (caps:list cap) (repr:seg) (c:cap)
  : Lemma (has_cap c (TSeal n caps repr) == mem c caps) = ()
