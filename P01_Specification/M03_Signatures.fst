module M03_Signatures

/// catcat core specification, module 03: stack signatures and concatenative
/// composition.
///
/// A signature is implicitly row-polymorphic. `{ pre; post }` denotes
///
///     forall r. vstack (pre @ r) -> vstack (post @ r)
///
/// so the row variable is never written in the core; it is recovered by
/// `M02_Stacks.frame`. This is what makes the frame property structural
/// rather than a per-word proof obligation.
///
/// The abandoned draft approached composition with `is_compatible_stack_types`
/// and `extract_uncommon_suffixes`. Two defects are worth recording, because
/// avoiding them is the whole point of this module:
///
///   * `compose_stack_functions` never applied its second argument -- the body
///     returned `(f stem) @ tail`, so the promised composition was identity
///     with extra steps.
///   * The residual segments were placed on the wrong sides of the arrow. When
///     the producer's outputs run out, the shortfall is drawn from BELOW, so
///     it belongs in the composite's `pre`; when the consumer's inputs run
///     out, the surplus stays on the stack, so it belongs in the composite's
///     `post`. The draft's type swapped these.

open FStar.List.Tot
open M01_Kinds
open M02_Stacks

(* ------------------------------------------------------------------------ *)
(* Signatures                                                               *)
(* ------------------------------------------------------------------------ *)

type srow = { pre : seg; post : seg }

/// The identity signature: consumes nothing, produces nothing.
let sid : srow = { pre = []; post = [] }

(* ------------------------------------------------------------------------ *)
(* Row unification                                                          *)
(* ------------------------------------------------------------------------ *)

/// Match a producer's outputs `b` against a consumer's inputs `c`, both with
/// head = top of stack. Returns `(b_rest, c_rest)`:
///
///   * `b_rest` -- outputs the consumer did not take. They remain on the
///     stack, beneath whatever the consumer produces.
///   * `c_rest` -- inputs the consumer still needs. They must come from below
///     the producer, i.e. from the composite's own inputs.
///
/// At most one of the two is non-empty; `lemma_unify_disjoint` records this.
let rec unify (b c:seg) : Tot (option (seg & seg)) (decreases b) =
  match b, c with
  | [], _              -> Some ([], c)
  | _, []              -> Some (b, [])
  | t1 :: b', t2 :: c' -> if t1 = t2 then unify b' c' else None

let rec lemma_unify_disjoint (b c:seg)
  : Lemma (ensures (match unify b c with
                    | Some (br, cr) -> Nil? br \/ Nil? cr
                    | None          -> True))
          (decreases b) =
  match b, c with
  | [], _              -> ()
  | _, []              -> ()
  | t1 :: b', t2 :: c' -> if t1 = t2 then lemma_unify_disjoint b' c' else ()

/// Unification is symmetric up to swapping the residuals, which is the formal
/// statement that neither side of a composition is privileged.
let rec lemma_unify_sym (b c:seg)
  : Lemma (ensures (match unify b c, unify c b with
                    | Some (br, cr), Some (cr', br') -> br == br' /\ cr == cr'
                    | None, None                     -> True
                    | _                              -> False))
          (decreases b) =
  match b, c with
  | [], _              -> ()
  | _, []              -> ()
  | t1 :: b', t2 :: c' -> if t1 = t2 then lemma_unify_sym b' c' else ()

/// A segment unifies with itself, leaving nothing over on either side.
let rec lemma_unify_refl (b:seg)
  : Lemma (ensures unify b b == Some ([], [])) (decreases b) =
  match b with
  | []     -> ()
  | _ :: r -> lemma_unify_refl r

/// Unification only ever inspects a common prefix, so a prefix shared by both
/// arguments is invisible to it. This is the workhorse of associativity below:
/// every branch of that case analysis learns, from `lemma_unify_common`, that
/// one segment IS another extended by a residual, and then cancels it here.
let rec lemma_unify_pfx (x a b:seg)
  : Lemma (ensures unify (x @ a) (x @ b) == unify a b) (decreases x) =
  match x with
  | []     -> ()
  | _ :: r -> lemma_unify_pfx r a b

/// The two one-sided corollaries: an extension unifies with what it extends,
/// leaving exactly the extension over on that side.
let lemma_unify_left (x y:seg)
  : Lemma (unify x (x @ y) == Some ([], y)) =
  lemma_unify_pfx x [] y; append_l_nil x

let lemma_unify_right (x y:seg)
  : Lemma (unify (x @ y) x == Some (y, [])) =
  lemma_unify_pfx x y []; append_l_nil x

/// What unification is FOR: the two residuals name the one shape both segments
/// extend to. Extending each side by the other's leftover gives the same
/// segment, which is the common instantiation of the two implicit rows.
///
/// This is the fact `srow_join` below rests on, and it is worth proving rather
/// than assuming: it is the precise sense in which `unify` succeeds only when
/// the two shapes are compatible, as opposed to merely non-contradictory.
let rec lemma_unify_common (b c:seg)
  : Lemma (ensures (match unify b c with
                    | Some (br, cr) -> b @ cr == c @ br
                    | None          -> True))
          (decreases b) =
  match b, c with
  | [], _              -> append_l_nil c
  | _, []              -> append_l_nil b
  | t1 :: b', t2 :: c' -> if t1 = t2 then lemma_unify_common b' c' else ()

(* ------------------------------------------------------------------------ *)
(* Composition                                                              *)
(* ------------------------------------------------------------------------ *)

/// Sequential composition of signatures: the denotation of juxtaposing two
/// programs. Partial, because the stack shapes may simply not agree.
let compose (f g:srow) : option srow =
  match unify f.post g.pre with
  | None                  -> None
  | Some (b_rest, c_rest) ->
    Some ({ pre = f.pre @ c_rest; post = g.post @ b_rest })

/// Composition never fails against the identity, and preserves the operand.
let lemma_compose_left_unit (f:srow)
  : Lemma (compose sid f == Some f) =
  append_l_nil f.post

let lemma_compose_right_unit (f:srow)
  : Lemma (compose f sid == Some f) =
  append_l_nil f.pre;
  (match f.post with [] -> () | _ -> ())

/// Associativity. Together with the unit laws this makes signatures the
/// morphisms of a category, which is the precise form of the draft's claim
/// that a program is nothing but a composition of functions.
///
/// The proof is a four-way case analysis on which operand's segment runs out
/// first. `lemma_unify_disjoint` collapses each pair of residuals to one, so
/// the cases are named by `c1` and `e1`; `lemma_unify_common` then turns each
/// surviving residual into an equation saying one segment extends another, and
/// `lemma_unify_pfx` cancels the shared part. What is left is associativity of
/// `@`. Note that no case needs to know anything about the segments' contents
/// -- which is the formal reason composition is a category and not merely a
/// partial operation that usually works.
let lemma_compose_assoc (f g h:srow)
  : Lemma (match compose f g with
           | Some fg -> (match compose g h with
                         | Some gh -> compose fg h == compose f gh
                         | None    -> True)
           | None    -> True) =
  match unify f.post g.pre with
  | None -> ()
  | Some (b1, c1) ->
    match unify g.post h.pre with
    | None -> ()
    | Some (d1, e1) ->
      lemma_unify_disjoint f.post g.pre;
      lemma_unify_common   f.post g.pre;
      lemma_unify_disjoint g.post h.pre;
      lemma_unify_common   g.post h.pre;
      (match c1, e1 with
       (* f.post == g.pre @ b1  and  g.post == h.pre @ d1: both consumers run
          short, so both residuals pile up on the producer side. *)
       | [], [] ->
         append_l_nil f.post; append_l_nil g.post;
         append_assoc h.pre  d1 b1;
         lemma_unify_right h.pre (d1 @ b1);
         lemma_unify_pfx g.pre b1 [];
         append_l_nil f.pre;
         append_assoc h.post d1 b1

       (* f.post == g.pre @ b1  and  h.pre == g.post @ e1: `g`'s surplus and
          `h`'s shortfall meet, so the outer unification is `unify b1 e1` on
          both sides of the equation. *)
       | [], _ ->
         append_l_nil f.post; append_l_nil g.post;
         lemma_unify_pfx g.post b1 e1;
         lemma_unify_pfx g.pre  b1 e1;
         append_l_nil f.pre;
         append_l_nil h.post

       (* g.pre == f.post @ c1  and  g.post == h.pre @ d1: `g` is the wide one,
          short on both ends, and each residual passes straight through. *)
       | _, [] ->
         append_l_nil g.pre; append_l_nil g.post;
         lemma_unify_right h.pre d1;
         append_l_nil (f.pre @ c1);
         append_l_nil (h.post @ d1)

       (* g.pre == f.post @ c1  and  h.pre == g.post @ e1: `g` consumes more
          than `f` produces and produces less than `h` consumes, so both
          shortfalls are drawn from below and concatenate. *)
       | _, _ ->
         append_l_nil g.post;
         lemma_unify_left g.post e1;
         append_assoc f.post c1 e1;
         lemma_unify_left f.post (c1 @ e1);
         append_assoc f.pre  c1 e1;
         append_l_nil h.post)

(* ------------------------------------------------------------------------ *)
(* Joining: agreement between alternative branches                          *)
(* ------------------------------------------------------------------------ *)

/// When do two ALTERNATIVE programs -- the branches of a `case` -- agree?
///
/// Not when their signatures are equal. Each branch is row-polymorphic, so
/// they agree when there is a common instantiation of the two rows. Framing
/// each side by what the other had extra is exactly that instantiation:
///
///   `then { }`      is  ( -- )
///   `else { 1 - }`  is  ( i64 -- i64 )
///
/// The first touches nothing and the second consumes a slot from beneath, yet
/// they leave the stack in the same state, so a `case` over them is well
/// formed. Framing the first by `[i64]` makes both `( i64 -- i64 )`.
///
/// What is rejected is disagreement at the head -- one branch consuming a
/// `bool` where the other consumes an `i64` -- because `unify` fails there.
/// So the check is on the resulting stack state, which is the property that
/// actually matters, rather than on how each branch happened to be written.
///
/// Note there are no type variables anywhere in this: joining is prefix
/// matching, exactly like `compose`. D-31's claim that the language needs no
/// unifier survives.
let srow_join (s1 s2:srow) : Tot (option srow) =
  match unify s1.pre s2.pre with
  | None          -> None
  | Some (r1, r2) ->
    /// `r2` is what `s2` demanded beyond `s1`, so it is what `s1` must be
    /// framed by, and symmetrically. `lemma_unify_common` says the two framed
    /// `pre`s coincide; the test is whether the framed `post`s do too.
    if s1.post @ r2 = s2.post @ r1
    then Some ({ pre = s1.pre @ r2; post = s1.post @ r2 })
    else None

/// A branch always agrees with itself.
let lemma_srow_join_refl (s:srow)
  : Lemma (srow_join s s == Some s) =
  lemma_unify_refl s.pre;
  append_l_nil s.pre;
  append_l_nil s.post

/// Agreement does not depend on which branch was written first. This is what
/// makes folding `srow_join` across a `case`'s branches a well-defined notion
/// of "all these agree" rather than an artefact of the traversal order.
let lemma_srow_join_sym (s1 s2:srow)
  : Lemma (srow_join s1 s2 == srow_join s2 s1) =
  lemma_unify_sym s1.pre s2.pre;
  lemma_unify_common s1.pre s2.pre

/// OBLIGATION, stated rather than stubbed (see the note at the foot of
/// `M07_Denotation.fst` for why a `Lemma True` placeholder is worse than an
/// honest gap): the fold of `srow_join` over a branch list is associative, so
/// `M06.infer_branches` computes the same answer whatever the branch order.
/// Symmetry above is the two-branch case. The general statement needs the
/// framed segments to compose, which is the same transport reasoning as
/// `lemma_compose_assoc`, and is best discharged alongside it rather than
/// separately.

(* ------------------------------------------------------------------------ *)
(* Denotation of a signature                                                *)
(* ------------------------------------------------------------------------ *)

/// What a signature means: a transformer that works at EVERY stack depth.
/// Making this a function of the row, rather than a refinement mentioning the
/// row, is the single change that dissolves the draft's difficulties.
type denotation (s:srow) = r:seg -> xform (s.pre @ r) (s.post @ r)

/// Every shape-specific transformer lifts to a row-polymorphic one. The
/// lifting is `frame`, and its correctness is `M02_Stacks.lemma_frame_apply`.
let lift (s:srow) (f:xform s.pre s.post) : denotation s =
  fun r -> frame r f

/// A lifted transformer leaves the row untouched -- stated here, at the level
/// where "the row" is meaningful, rather than at each word definition.
let lemma_lift_frames (s:srow) (f:xform s.pre s.post) (r:seg)
                      (x:vstack s.pre) (y:vstack r)
  : Lemma (lift s f r (vappend x y) == vappend (f x) y) =
  lemma_frame_apply r f x y
