module M02_Stacks

/// catcat core specification, module 02: intrinsically typed value stacks.
///
/// This module replaces the approach taken in the abandoned draft, where a
/// stack was `list value` refined by a `splitAt`-based predicate. That design
/// forced every operation to re-establish its invariant by hand, so the draft
/// accumulated a pile of lemmas about `splitAt` and none about the language.
/// Worse, it stated the frame property -- "a word does not disturb the stack
/// beneath it" -- as a refinement on each individual function, making it a
/// proof obligation at every definition site.
///
/// Here the stack is an inductive family indexed by `list dtype`, so
/// well-typedness is structural and unstateable-otherwise. The frame property
/// is proved exactly once, about the `frame` combinator at the bottom of this
/// file, and every word inherits it for free.
///
/// CONVENTION, fixed globally and relied on everywhere downstream: the HEAD of
/// the index list is the TOP of the stack. A signature `(a -- b)` with row `r`
/// therefore denotes a map `vstack (a @ r) -> vstack (b @ r)`: the row is the
/// TAIL of the list, which is the part of the stack further from the top.

open FStar.List.Tot
open M01_Kinds

(* ------------------------------------------------------------------------ *)
(* Values and stacks                                                        *)
(* ------------------------------------------------------------------------ *)

/// Values and stacks are mutually inductive. A sealed value wraps a stack
/// segment -- this is the formal content of "a product is just a run of stack
/// slots", and of D03's claim that a class instance is a sealed segment.
///
/// A sum value is a tag plus the segment that tag selects. This is the one
/// place where a shape genuinely varies at runtime, which is why sums cannot
/// be encoded as segments and must be primitive.
noeq type value : dtype -> Type =
  | VPrim : #p:prim -> prim_rep p -> value (TPrim p)
  | VSeal : n:nom_id -> caps:list cap -> #repr:seg -> vstack repr
          -> value (TSeal n caps repr)
  | VSum  : #variants:list seg -> tag:nat { tag < length variants }
          -> vstack (index variants tag) -> value (TSum variants)
  /// Pointers. The indirection is what lets a recursive declaration have a
  /// finite value: `VBox` nests a value of the pointee type, and the tree
  /// stays finite because it terminates at some non-recursive variant.
  | VBox  : #t:dtype -> value t -> value (TBox t)
  | VRc   : #t:dtype -> value t -> value (TRc t)
  /// A value at an INCOMPLETE type. `n` names a declaration; `t` is what the
  /// value actually is.
  ///
  /// The pairing is unchecked here, deliberately: M02 is environment-free, so
  /// it can record that a value sits behind a name but cannot verify that `t`
  /// is what `n` declares. That check belongs to M06, which has the
  /// environment. This is what "incomplete type" means formally -- the name is
  /// a promise M02 carries and M06 discharges.
  | VName : #n:nom_id -> #t:dtype -> value t -> value (TName n)

and vstack : seg -> Type =
  | VNil  : vstack []
  | VCons : #t:dtype -> #ts:seg -> value t -> vstack ts -> vstack (t :: ts)

(* ------------------------------------------------------------------------ *)
(* Concatenation and splitting                                              *)
(* ------------------------------------------------------------------------ *)

/// Push a whole segment onto a stack. Note the index: the result type is
/// `a @ r`, computed, not asserted -- there is no invariant to restore.
let rec vappend (#a #r:seg) (x:vstack a) (y:vstack r)
  : Tot (vstack (a @ r)) (decreases x) =
  match x with
  | VNil        -> y
  | VCons v rest -> VCons v (vappend rest y)

/// Split a stack at a segment boundary. `a` is explicit because it is the
/// recursion and index driver: the caller always knows the shape it wants off
/// the top, since that shape comes from a word's signature.
let rec vsplit (a:seg) (#r:seg) (s:vstack (a @ r))
  : Tot (vstack a & vstack r) (decreases a) =
  match a with
  | []      -> (VNil, s)
  | t :: ts ->
    let VCons v rest = s in
    let (x, y) = vsplit ts rest in
    (VCons v x, y)

/// The two round-trip laws. These are the ONLY structural lemmas the entire
/// specification needs -- compare the draft, which needed four just to state
/// its stack type.
let rec lemma_vsplit_vappend (#a #r:seg) (x:vstack a) (y:vstack r)
  : Lemma (ensures vsplit a (vappend x y) == (x, y)) (decreases x) =
  match x with
  | VNil         -> ()
  | VCons _ rest -> lemma_vsplit_vappend rest y

let rec lemma_vappend_vsplit (a:seg) (#r:seg) (s:vstack (a @ r))
  : Lemma (ensures (let (x, y) = vsplit a s in vappend x y == s)) (decreases a) =
  match a with
  | []      -> ()
  | _ :: ts -> let VCons _ rest = s in lemma_vappend_vsplit ts #r rest

(* ------------------------------------------------------------------------ *)
(* The frame combinator                                                     *)
(* ------------------------------------------------------------------------ *)

/// A stack transformer of a fixed shape: what a word's signature denotes
/// before any row is supplied.
type xform (a b:seg) = vstack a -> vstack b

/// Run `f` on the top `a` slots, leaving the row `r` beneath untouched.
///
/// This is the tensor `f (X) id_r` of the monoidal category the language
/// denotes into. Everything the draft wanted to say about words not
/// disturbing the rest of the stack is said here, once.
let frame (#a #b:seg) (r:seg) (f:xform a b) : xform (a @ r) (b @ r) =
  fun s -> let (x, y) = vsplit a s in vappend (f x) y

let vid (#a:seg) : xform a a = fun s -> s

let vcomp (#a #b #c:seg) (f:xform a b) (g:xform b c) : xform a c =
  fun s -> g (f s)

(* ------------------------------------------------------------------------ *)
(* Functoriality of framing                                                 *)
(* ------------------------------------------------------------------------ *)

/// The computational content of framing: `f` runs on the top segment and the
/// row beneath is returned untouched. This is the property the draft tried to
/// impose as a refinement on every stack function; here it is one lemma, and
/// it is the one M07 and M09 actually cite.
let lemma_frame_apply (#a #b:seg) (r:seg) (f:xform a b) (x:vstack a) (y:vstack r)
  : Lemma (frame r f (vappend x y) == vappend (f x) y) =
  lemma_vsplit_vappend x y

/// `frame r` preserves identities.
let lemma_frame_id (#a:seg) (r:seg) (s:vstack (a @ r))
  : Lemma (frame r (vid #a) s == s) =
  lemma_vappend_vsplit a s

/// `frame r` preserves composition. Together with `lemma_frame_id` this says
/// `frame r` is a functor, which is what licenses compiling a word once and
/// reusing it at every stack depth instead of once per depth.
let lemma_frame_comp (#a #b #c:seg) (r:seg) (f:xform a b) (g:xform b c)
                     (s:vstack (a @ r))
  : Lemma (frame r (vcomp f g) s == frame r g (frame r f s)) =
  let (x, y) = vsplit a s in
  lemma_vsplit_vappend (f x) y

/// The unit law `frame [] f == f` is omitted deliberately: `a @ []` is only
/// propositionally equal to `a`, so the statement needs a transport and says
/// nothing `lemma_frame_apply` does not already say. M03 states the unit law
/// where it is type-correct, at the level of signatures.

(* ------------------------------------------------------------------------ *)
(* Capability-directed operations                                           *)
(* ------------------------------------------------------------------------ *)

/// `dup` and `pop`, the two operations that linearity governs. Their
/// preconditions are the entire runtime content of the linear type system:
/// a value with neither capability can only be moved, never duplicated or
/// discarded, so a linear resource must be routed to a consuming word.
///
/// These are total functions here; M06 is responsible for rejecting programs
/// that would call them at a type lacking the capability.
let vdup (#t:dtype { copyable t }) (#r:seg) (s:vstack (t :: r))
  : vstack (t :: t :: r) =
  let VCons v rest = s in VCons v (VCons v rest)

let vpop (#t:dtype { droppable t }) (#r:seg) (s:vstack (t :: r)) : vstack r =
  let VCons _ rest = s in rest

/// `swap`, which needs no capability: it moves, and moving is always allowed.
let vswap (#t1 #t2:dtype) (#r:seg) (s:vstack (t1 :: t2 :: r))
  : vstack (t2 :: t1 :: r) =
  let VCons v1 (VCons v2 rest) = s in VCons v2 (VCons v1 rest)

/// `pick` and `roll`, the deep counterparts of `dup` and `swap` (`M05.sop`).
/// `above` is the segment sitting above the target slot, so the stack is
/// `above @ (t :: r)` with head = top -- which is what makes an n-deep access
/// expressible without a variadic rule.
///
/// These were absent until M07 needed them, and their absence was a real hole
/// rather than an oversight: `vpick` COPIES, so it must carry the same
/// `copyable` refinement `vdup` does, and hand-writing it at the denotation site
/// in M07 would have put a duplication outside the one file where the capability
/// premises live. `vroll_up` only moves, so it carries none. M07's T6 quantifies
/// over this section, and that is only meaningful if nothing bypasses it.
let vpick (above:seg) (#t:dtype { copyable t }) (#r:seg)
          (s:vstack (above @ (t :: r)))
  : vstack (t :: (above @ (t :: r))) =
  let (_, y) = vsplit above s in
  let VCons v _ = y in
  VCons v s

let vroll_up (above:seg) (#t:dtype) (#r:seg) (s:vstack (above @ (t :: r)))
  : vstack (t :: (above @ r)) =
  let (x, y) = vsplit above s in
  let VCons v rest = y in
  VCons v (vappend x rest)

(* ------------------------------------------------------------------------ *)
(* Booleans                                                                 *)
(* ------------------------------------------------------------------------ *)

/// The boolean-to-sum coercion (`M05.PBoolSum`, D-33): `false` becomes variant 0
/// of `M01.bool_variants` and `true` becomes variant 1. This is the only way to
/// branch on a `bool`, since `TCase` eliminates a sum and `bool` is primitive.
///
/// It belongs here rather than inline at its denotation for a mundane reason as
/// well as a tidy one: the argument's index has to be `TPrim PBool`
/// DEFINITIONALLY for the payload to be usable at `bool`, and at the denotation
/// site that equation is only propositional.
///
/// The payload comes out through `vprim`, and it has to. Destructing `VPrim`
/// in place leaves `p` unsolved -- F* resolves a constructor's implicit index
/// from the EXPECTED TYPE of the match, so `let VPrim b = v in b` at result type
/// `prim_rep p` works while the same pattern used inside a larger expression does
/// not. Naming the projection is what supplies that expected type.
let vprim (#p:prim) (v:value (TPrim p)) : prim_rep p = let VPrim x = v in x

let vbool_sum (#r:seg) (s:vstack (TPrim PBool :: r))
  : vstack (TSum bool_variants :: r) =
  let VCons v rest = s in
  if vprim v then VCons (VSum #bool_variants 1 VNil) rest
             else VCons (VSum #bool_variants 0 VNil) rest

(* ------------------------------------------------------------------------ *)
(* Sealing                                                                  *)
(* ------------------------------------------------------------------------ *)

/// Sealing and unsealing are the class boundary from D03. `vseal` bundles a
/// representation segment into one nominal slot; `vunseal` is the inverse and
/// is available only inside the class body.
///
/// The pair is definitionally an isomorphism, which is the formal reason
/// sealing is free at runtime: the erasure pass in M11 removes both.
let vseal (n:nom_id) (caps:list cap) (#repr:seg) (#r:seg) (s:vstack (repr @ r))
  : vstack (TSeal n caps repr :: r) =
  let (x, y) = vsplit repr s in
  VCons (VSeal n caps x) y

let vunseal (#n:nom_id) (#caps:list cap) (#repr:seg) (#r:seg)
            (s:vstack (TSeal n caps repr :: r))
  : vstack (repr @ r) =
  let VCons (VSeal _ _ inner) rest = s in
  vappend inner rest

let lemma_unseal_seal (n:nom_id) (caps:list cap) (#repr:seg) (#r:seg)
                      (s:vstack (repr @ r))
  : Lemma (vunseal (vseal n caps s) == s) =
  lemma_vappend_vsplit repr s

(* ------------------------------------------------------------------------ *)
(* Pointers                                                                 *)
(* ------------------------------------------------------------------------ *)

/// Allocate and consume. There is no `vboxdrop`: `TBox` lacks `CDrop`, so a
/// box is discarded only by opening it and then dealing with the payload,
/// which is exactly the discipline that prevents a leak.
let vbox_new (#t:dtype) (#r:seg) (s:vstack (t :: r)) : vstack (TBox t :: r) =
  let VCons v rest = s in VCons (VBox v) rest

let vbox_open (#t:dtype) (#r:seg) (s:vstack (TBox t :: r)) : vstack (t :: r) =
  let VCons (VBox v) rest = s in VCons v rest

let lemma_box_open_new (#t:dtype) (#r:seg) (s:vstack (t :: r))
  : Lemma (vbox_open (vbox_new s) == s) = ()

/// `Rc` operations. `vrc_clone` is the `Clone` interface word, not `dup`:
/// duplicating the handle is a real operation, which is precisely why `TRc`
/// lacks `CCopy`. Likewise `vrc_drop` is `release`, not `pop`.
let vrc_new (#t:dtype) (#r:seg) (s:vstack (t :: r)) : vstack (TRc t :: r) =
  let VCons v rest = s in VCons (VRc v) rest

let vrc_clone (#t:dtype) (#r:seg) (s:vstack (TRc t :: r))
  : vstack (TRc t :: TRc t :: r) =
  let VCons v rest = s in VCons v (VCons v rest)

let vrc_drop (#t:dtype) (#r:seg) (s:vstack (TRc t :: r)) : vstack r =
  let VCons _ rest = s in rest

/// Reading through a shared pointer without consuming it. Restricted to
/// copyable payloads: a non-copyable payload would need borrowing, which is
/// deliberately not a feature yet (N02 Q-03).
let vrc_read (#t:dtype { copyable t }) (#r:seg) (s:vstack (TRc t :: r))
  : vstack (t :: TRc t :: r) =
  let VCons (VRc v) rest = s in VCons v (VCons (VRc v) rest)

/// Roll and unroll an incomplete type. Both are runtime no-ops -- the name is
/// type-level only -- which is why R04 erases `VName` to its payload.
let vroll (n:nom_id) (#t:dtype) (#r:seg) (s:vstack (t :: r))
  : vstack (TName n :: r) =
  let VCons v rest = s in VCons (VName #n #t v) rest

let lemma_pointers_are_linear (t:dtype)
  : Lemma (not (copyable (TBox t)) /\ not (copyable (TRc t))) = ()

(* ------------------------------------------------------------------------ *)
(* The frame laws, as a structure rather than a comment                     *)
(* ------------------------------------------------------------------------ *)

/// WHY BUNDLE LAWS THAT ARE ALREADY PROVED (D-64).
///
/// The lemmas above are each true and each separately citable, and a reader has
/// to be told in prose that together they say `frame r` is a functor. Prose is
/// where that claim can rot: nothing checks that the three lemmas still add up
/// to functoriality after one of them is restated. A RECORD TYPE checks it. The
/// obligation becomes a type, discharging it becomes exhibiting a value, and the
/// value below costs nothing to build because the fields ARE the existing
/// lemmas.
///
/// A record and not a `class`: in F* a class is a record plus tactic-driven
/// instance resolution, and resolution pays only when a LATER module wants to be
/// generic over "any lawful frame". There is exactly one. Promoting is one
/// keyword when P04 needs it.
///
/// Function-typed fields are allowed here for the reason `M04.handler`'s are:
/// D-20 bars them from modules P02 and P03 EXTRACT, and nothing extracts M02's
/// law bundles — they are specification-side objects with no runtime content.
noeq type frame_laws = {
  /// Framing applies the transformer to the top and leaves the rest alone.
  fl_apply : (#a:seg) -> (#b:seg) -> (r:seg) -> (f:xform a b)
           -> (x:vstack a) -> (y:vstack r)
           -> Lemma (frame r f (vappend x y) == vappend (f x) y);
  /// Identity is preserved.
  fl_id    : (#a:seg) -> (r:seg) -> (s:vstack (a @ r))
           -> Lemma (frame r (vid #a) s == s);
  /// Composition is preserved.
  fl_comp  : (#a:seg) -> (#b:seg) -> (#c:seg) -> (r:seg)
           -> (f:xform a b) -> (g:xform b c) -> (s:vstack (a @ r))
           -> Lemma (frame r (vcomp f g) s == frame r g (frame r f s));
}

/// `frame r` is a functor, and this value is the proof. It is what licenses
/// compiling a word once and reusing it at every stack depth rather than once
/// per depth -- the claim `lemma_frame_comp`'s comment makes in prose, now
/// checked.
let frame_is_functorial : frame_laws = {
  fl_apply = lemma_frame_apply;
  fl_id    = lemma_frame_id;
  fl_comp  = lemma_frame_comp;
}
