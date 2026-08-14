module M05_Terms

/// catcat core specification, module 05: core term syntax.
///
/// This is the CORE language, not the surface language. Locals (`$x`), sigils,
/// namespacing, generics and macros are all elaborated away before a term
/// reaches this type -- see D05. In particular there is no `local` form here,
/// because `$x` compiles to stack shuffles and the core never learns that
/// locals existed.
///
/// One structural decision, from D02: quotations are NOT values. Code is
/// first-class at elaboration time, but there are no runtime function values,
/// so a `{}` block never appears on the value stack. It appears only as a
/// syntactic argument to a construct that consumes it -- `THandle`, `TTry`,
/// `TSpecialize`. This is what lets every block be inlined and keeps closures
/// out of the core entirely.
///
/// This type is also the interface between the specification and the compiler.
/// Because F* is the source of truth (D06), compiler passes are F* functions
/// over `term`, and self-hosting is extraction of those passes rather than a
/// separately written catcat compiler.

open FStar.List.Tot
open M01_Kinds
open M04_Effects

(* ------------------------------------------------------------------------ *)
(* Literals and stack primitives                                            *)
(* ------------------------------------------------------------------------ *)

/// `noeq` because `prim_rep` may be an abstract float type.
noeq type lit =
  | LPrim : p:prim -> prim_rep p -> lit

let lit_type (l:lit) : dtype =
  match l with
  | LPrim p _ -> TPrim p

/// The stack shuffles. Each carries the type it operates at: the core is
/// monomorphic, and generic `dup`/`pop` are instantiated during elaboration.
///
/// `SDup` and `SPop` are the only operations gated on capabilities, and that
/// gating is the entire enforcement mechanism for linearity. `SSwap` needs no
/// capability because moving a value is always permitted.
/// `SPick` and `SRoll` reach past the top of the stack. They carry the segment
/// ABOVE the target slot, which is what makes an n-deep access expressible
/// without a variadic rule: the stack is `above @ [d] @ rest`, head = top.
///
///   `SPick above d`  ( above d -- d above d )   copy;  requires Copy
///   `SRoll above d`  ( above d -- d above )     move;  no capability needed
///
/// These exist because `$x` locals (D05) compile to deep access, and `SDup` /
/// `SPop` / `SSwap` only reach the top two slots — no composition of them can
/// touch a third. Adding them here rather than inventing a fixed `rot` keeps
/// the rule uniform at every depth.
type sop =
  | SDup  : dtype -> sop
  | SPop  : dtype -> sop
  | SSwap : dtype -> dtype -> sop
  | SPick : seg -> dtype -> sop
  | SRoll : seg -> dtype -> sop

type word_id = nat

(* ------------------------------------------------------------------------ *)
(* Primitives                                                               *)
(* ------------------------------------------------------------------------ *)

/// The intrinsics: every core operation whose signature is a function of its
/// own arguments and whose meaning is a PURE stack transformer. Literals,
/// shuffles, sealing, sum injection, the boolean coercion and the pointer
/// operations are all instances of that one shape, so they are one term
/// constructor over a table rather than twelve constructors over none (D-55).
///
/// WHY THIS IS A TABLE AND NOT TWELVE CONSTRUCTORS. Each of these needs a
/// signature (`M06.prim_sig`), a denotation (`M07`) and a machine action
/// (`R02.step`). Spelled as constructors, adding one means amending three
/// functions and every induction over `term` in M07 and M09 grows a case.
/// Spelled as a table, adding one is a row, and each induction has a single
/// uniform primitive case discharged once. The core drops from nineteen
/// constructors to seven, and the eight that remain (D-71 added the abort) are
/// exactly the language's structure: identity, composition, naming,
/// elimination, handling, aborting, staging.
///
/// The invariant that pays for the grouping: EVERY PRIMITIVE IS PURE. There
/// is no `erow` in `prim_sig`'s result because none of these can perform an
/// operation, so `M07`'s T4 covers the whole class at once. Anything that
/// could perform an effect is a `TWord` resolving to an operation instead —
/// which is why `print` is not here.
///
/// Named `prim_op` and `TPrimOp` because `M01.TPrim` is already the primitive
/// *type* constructor; these are primitive *operations* and the two are in
/// scope together everywhere downstream.
///
/// FUTURE (D-55): a native library defined in F* contributes entries with
/// their own invariants, at which point this closed inductive becomes the
/// built-in half of a two-level table and `TBox`/`TRc` move out of it. The
/// shape here is chosen to make that move a change of lookup and not a change
/// of language.
noeq type prim_op =
  /// A constant. The only primitive whose meaning depends on a value rather
  /// than only on types.
  | PLit     : lit -> prim_op
  /// A stack shuffle.
  | PStack   : sop -> prim_op
  /// Bundle a representation segment into a nominal type, and its inverse.
  /// Named `PPack`/`PUnpack` rather than `PSeal`/`PUnseal` to stay clear of
  /// the `dtype` constructor `M01_Kinds.TSeal`.
  /// `PUnpack` is well typed only inside the class body (D03).
  | PPack    : nom_id -> list cap -> seg -> prim_op
  | PUnpack  : nom_id -> list cap -> seg -> prim_op
  /// Sum introduction: build variant `tag` of `variants`.
  | PInj     : variants:list seg -> tag:nat -> prim_op
  /// `( bool -- TSum [[]; []] )`, false to tag 0 and true to tag 1.
  ///
  /// This is the ONLY way to branch on a boolean, and it is deliberately a
  /// coercion rather than an eliminator (D-33). `bool` is a primitive type, so
  /// `TCase` -- which eliminates a sum -- cannot see it; giving the core a
  /// separate `TIf` would mean a second copy of the branch-agreement rule that
  /// `infer_branches` already implements. One coercion plus the existing rule
  /// costs one table row and no new typing logic.
  ///
  /// The tag order is `false = 0`, `true = 1`, matching the usual reading of a
  /// bool as a two-element enumeration. Surface `if` therefore lists its ELSE
  /// branch first; `E04` is where that is arranged, and it is stated in both
  /// places because a silent reversal here would be a plausible-looking bug.
  | PBoolSum : prim_op
  /// Pointer operations. `PBoxOpen` consumes the box and yields the payload;
  /// there is no discard, because `TBox` lacks `CDrop` and the payload must be
  /// dealt with explicitly.
  | PBoxNew  : dtype -> prim_op
  | PBoxOpen : dtype -> prim_op
  /// `PRcClone` is the `Clone` interface word and `PRcDrop` is `release` --
  /// neither is `dup` or `pop`, which is exactly why `TRc` carries no
  /// capabilities. `PRcRead` needs a copyable payload; the alternative is
  /// borrowing, deliberately deferred.
  | PRcNew   : dtype -> prim_op
  | PRcClone : dtype -> prim_op
  | PRcDrop  : dtype -> prim_op
  | PRcRead  : dtype -> prim_op
  /// Roll and unroll an incomplete type. Runtime no-ops; they exist so that
  /// the type system can cross a `TName` boundary explicitly rather than by
  /// silent coercion.
  | PRoll    : nom_id -> dtype -> prim_op
  | PUnroll  : nom_id -> dtype -> prim_op

(* ------------------------------------------------------------------------ *)
(* Terms                                                                    *)
(* ------------------------------------------------------------------------ *)

/// Eight constructors. Everything else the language can do is either a table
/// row (`prim_op`) or a word (`TWord`), and that is the whole claim of D-55:
/// the core is the structure, not the vocabulary.
noeq type term =
  /// The empty program. Identity of composition.
  | TNil     : term
  /// Juxtaposition. The ONLY sequencing construct: `a b` and nothing else.
  | TSeq     : term -> term -> term
  /// A primitive operation. One constructor over the `prim_op` table above.
  | TPrimOp  : prim_op -> term
  /// A named word, or an interface operation. The typing rules do not
  /// distinguish them -- that is the unification of D03 made concrete.
  | TWord    : word_id -> term
  /// Sum elimination: PERFORM THE OPERATION THE TAG SELECTS (D-68).
  ///
  /// `ops` gives one operation id per variant. The scrutinee is a `TSum
  /// variants` on top of the stack; eliminating it means performing
  /// `index ops tag` with that variant's payload as the operation's arguments.
  /// The BRANCHES ARE THE HANDLER'S IMPLEMENTATIONS, so a `case` is
  ///
  ///     THandle e [] TNil branches (TDispatch ops variants)
  ///
  /// and there is no branching construct in the core at all -- only dispatch,
  /// which is one `M04.Op` node, and handling, which already existed.
  ///
  /// WHY THIS IS A LEAF AND `TCase` WAS NOT. The branches moved out, so this
  /// constructor has no subterms: every induction over `term` loses its
  /// branch-list case, and `M06.infer_branches` and `M07.denote_case` are gone
  /// rather than rewritten. What replaces them is `infer_impls` and `handle`,
  /// which the language already needed for effects.
  ///
  /// The common frame lives in the OPERATION'S DECLARED SIGNATURE: variant `i`
  /// declares `( variants[i] @ j.pre -- j.post )` where `j` is what
  /// `M03.srow_join` computes across the branches. That is what keeps a branch
  /// able to reach beneath the scrutinee -- an implementation is handed exactly
  /// `st @ op_pre` and nothing else, so without folding `j.pre` into `op_pre` a
  /// branch could not touch the stack under the sum, and `if { } then { pop 1 }
  /// else { … } endif` would stop typing.
  | TDispatch : ops:list op_id -> variants:list seg -> term
  /// Install a handler for `eff` and run `body` under it.
  ///
  /// HANDLERS ARE STATEFUL OBJECTS, NOT CONTINUATION CONSUMERS (D-36). An
  /// operation call runs its implementation, which RETURNS; nothing is
  /// captured. `st` is the segment of handler state and `init` the program
  /// that produces it, so a handler is exactly D03 §3's `class … over ( … )`
  /// — one construct, D-01 again.
  ///
  /// The state is threaded through each implementation's own signature: an
  /// implementation of `o` is typed at
  ///
  ///     { pre = st @ o.op_pre ; post = st @ o.op_post }
  ///
  /// so `st` sits on TOP, above the operation's arguments. That position is
  /// not a preference, it is the only one the machine can splice into without
  /// knowing the operation's arity at runtime (see `R02.step`), and it reads
  /// correctly anyway: the state is the receiver, and a receiver is pushed
  /// last. A stateless handler is `st = []`, so it needs no separate rule.
  ///
  /// On exit the final state is left on the stack, above whatever the body
  /// produced. The handler *is* the object, so the object outlives the block;
  /// discarding it instead would need `CDrop` and would silently throw away
  /// the result of the computation the state was accumulating.
  | THandle  : eff:eff_id -> st:seg -> init:term
             -> impls:list (op_id & term) -> body:term -> term
  /// Handle an ABORTING effect: run `body`, and if it performs any operation of
  /// `eff`, abandon it and run `catch` instead (D-71).
  ///
  /// WHY THIS IS NOT A `THandle` (D-71). An aborting operation's meaning is "do
  /// not run the rest of the body", and the only place the rest of the body
  /// exists is the continuation `M04.handle` holds. Handling one therefore means
  /// DISCARDING that continuation — which is not continuation capture, nothing
  /// is stored or re-entered, but it is not something an `M04.op_impl` can do
  /// either: an implementation is handed `st @ op_pre` and must produce
  /// `st @ op_post`, and `catch` has to produce the result of the WHOLE handled
  /// computation. Making `M04.handler` able to express that would index it by
  /// the result type of the code it handles, and a method table indexed by its
  /// client's result type is not a method table. D03's identification of
  /// handlers with classes, interfaces and modules is what would break, so the
  /// abort gets its own eliminator and the identification stays exact.
  ///
  /// `pre` is the body's own `pre`, which `M06.infer` checks rather than
  /// trusts. The denotation does not need it — the stack below the body is in
  /// scope as `M02.vsplit`'s residual — but `R02` does: the machine's stack is
  /// flat, so the frame has to record how far down to cut back to when the
  /// abort discards whatever the body had built.
  ///
  /// EVERY operation of `eff` aborts; there is no per-operation flag. An
  /// aborting effect is one whose operations all mean "stop", which is what
  /// `Fail` is, and a handler for a non-aborting effect is still a `THandle`.
  ///
  /// CODE AFTER AN ABORT IS TYPECHECKED AS LIVE AND IS SEMANTICALLY DEAD
  /// (D-72), and the two are not in tension. `fail` is declared `( -- )`, so
  /// `M06.infer`'s `TSeq` rule composes the sequel exactly as if it returned,
  /// and the row it computes is the `row_union` -- which is how `!Fail`
  /// propagates outward through ordinary code. The deadness is not a fact about
  /// the term at all: `M04.lemma_abort_kills_sequel` shows the sequel's
  /// denotation does not appear in the result, and it is `handle_abort` that
  /// makes that so. Nothing about `fail`, and nothing about sequencing, is
  /// special-cased for it.
  | TTry     : eff:eff_id -> pre:seg -> body:term -> catch:term -> term
  /// Resolve the static effects of the body against the ambient dictionary,
  /// producing a residual program. Invoked at elaboration time this is
  /// specialization; invoked at runtime it is the JIT. One construct, one
  /// theorem (M11).
  | TSpecialize : body:term -> term

(* ------------------------------------------------------------------------ *)
(* Structural measures                                                      *)
(* ------------------------------------------------------------------------ *)

let rec term_size (t:term) : Tot pos =
  match t with
  | TNil                -> 1
  | TSeq a b            -> 1 + term_size a + term_size b
  | TPrimOp _           -> 1
  | TWord _             -> 1
  | TDispatch _ _       -> 1
  | THandle _ _ i impls b -> 1 + term_size i + impls_size impls + term_size b
  | TTry _ _ b c          -> 1 + term_size b + term_size c
  | TSpecialize b       -> 1 + term_size b

and terms_size (ts:list term) : Tot nat =
  match ts with
  | []     -> 0
  | t :: r -> term_size t + terms_size r

and impls_size (is:list (op_id & term)) : Tot nat =
  match is with
  | []            -> 0
  | (_, t) :: r   -> term_size t + impls_size r

(* ------------------------------------------------------------------------ *)
(* Smart constructors                                                       *)
(* ------------------------------------------------------------------------ *)

/// Build a program from a sequence of terms. Left-associated, matching the
/// reading order of the source: `a b c` is `((a b) c)`.
let rec seq_of (ts:list term) : Tot term =
  match ts with
  | []     -> TNil
  | t :: r -> TSeq t (seq_of r)

(* ------------------------------------------------------------------------ *)
(* Word rebinding                                                           *)
(* ------------------------------------------------------------------------ *)

/// Rewrite every `TWord w` for which `su` gives a replacement.
///
/// This is `M11.specialize` restricted to one kind of static effect, and the
/// first piece of D-02 that runs: surface `with { old new } { body }` installs
/// a Dictionary handler, the elaborator discharges it immediately, and the
/// residual program is this substitution. Nothing about the rebinding survives.
/// See M11's header for why that is the zero-cost theorem in miniature, and E7
/// for what it preserves.
///
/// Defined here rather than in M11 because it needs no environment -- it is a
/// rewrite of syntax, not a use of the typing judgment.
let subst_word (su:list (word_id & word_id)) (w:word_id) : Tot word_id =
  match assoc w su with
  | Some w' -> w'
  | None    -> w

/// Measure as above: the rank orders `list(1) > term(0)`.
let rec subst_words (su:list (word_id & word_id)) (t:term)
  : Tot term (decreases %[(term_size t <: nat); 0]) =
  match t with
  | TWord w              -> TWord (subst_word su w)
  | TSeq a b             -> TSeq (subst_words su a) (subst_words su b)
  | TDispatch _ _        -> t
  | THandle e st i im b  -> THandle e st (subst_words su i)
                                    (subst_words_impls su im)
                                    (subst_words su b)
  | TTry e p b c         -> TTry e p (subst_words su b) (subst_words su c)
  | TSpecialize b        -> TSpecialize (subst_words su b)
  | _                    -> t

and subst_words_list (su:list (word_id & word_id)) (ts:list term)
  : Tot (list term) (decreases %[terms_size ts; 1]) =
  match ts with
  | []     -> []
  | t :: r -> subst_words su t :: subst_words_list su r

/// An implementation's KEY is not substituted, only its body. The key says
/// which operation is being implemented; rebinding it would change which
/// handler answers, rather than what that handler does.
and subst_words_impls (su:list (word_id & word_id)) (im:list (op_id & term))
  : Tot (list (op_id & term)) (decreases %[impls_size im; 1]) =
  match im with
  | []            -> []
  | (o, t) :: r   -> (o, subst_words su t) :: subst_words_impls su r

/// Whether a term mentions `TSpecialize` anywhere. The linker uses the
/// analogous predicate over the whole dependency tree to decide how much of
/// the compiler to embed in the output binary (D04): if this is false
/// everywhere, no compiler stage is linked in at all.
/// Measure note, as in M01: a plain size measure is only non-strict on the
/// list-to-element edges, so the rank component orders `list(1) > term(0)`.
/// This is acyclic because every term-to-list edge strictly decreases size.
let rec needs_compiler (t:term)
  : Tot bool (decreases %[(term_size t <: nat); 0]) =
  match t with
  | TSpecialize _       -> true
  | TSeq a b            -> needs_compiler a || needs_compiler b
  | TDispatch _ _       -> false
  | THandle _ _ i impls b -> needs_compiler i || needs_compiler_impls impls
                           || needs_compiler b
  | TTry _ _ b c          -> needs_compiler b || needs_compiler c
  | _                   -> false

and needs_compiler_list (ts:list term)
  : Tot bool (decreases %[terms_size ts; 1]) =
  match ts with
  | []     -> false
  | t :: r -> needs_compiler t || needs_compiler_list r

and needs_compiler_impls (is:list (op_id & term))
  : Tot bool (decreases %[impls_size is; 1]) =
  match is with
  | []          -> false
  | (_, t) :: r -> needs_compiler t || needs_compiler_impls r

/// Whether a term mentions `PUnroll` anywhere.
///
/// This exists for one reason: `PUnroll` AS TYPED HAS NO MEANING, so a term
/// containing one is outside the fragment M07's `denote_static` can interpret.
/// `M06.prim_sig` asks only for `wf d`, so `PRoll n d1` followed by
/// `PUnroll n d2` typechecks for any well-formed `d2` and reinterprets one type
/// as another; `M02.VName` compounds it by hiding the payload's type as an
/// implicit index, so nothing can recover what the value actually is. See M07's
/// `prim_den` for the full statement and N02 Q-13 for the two candidate fixes.
///
/// The predicate is a HOLDING PATTERN, and naming it as one is the point. Its
/// job is to keep the soundness hole out of the domain of every theorem stated
/// about `denote_static`, so that T3, T4 and T6 are unconditionally true of a
/// well-defined fragment rather than conditional on a fix that has not been
/// made. When roll/unroll is settled, this predicate is DELETED rather than
/// discharged, and the fragment grows to the whole core.
///
/// Deliberately not folded into `needs_compiler`: that one is a real and
/// permanent property of a program -- the linker consumes it (D04, M11's E5) --
/// whereas this one is a defect marker. Merging them would hide the defect
/// inside a predicate that has every reason to survive.
let rec uses_unroll (t:term)
  : Tot bool (decreases %[(term_size t <: nat); 0]) =
  match t with
  | TPrimOp (PUnroll _ _) -> true
  | TSeq a b              -> uses_unroll a || uses_unroll b
  | TDispatch _ _         -> false
  | THandle _ _ i impls b -> uses_unroll i || uses_unroll_impls impls
                           || uses_unroll b
  | TTry _ _ b c          -> uses_unroll b || uses_unroll c
  | TSpecialize b         -> uses_unroll b
  | _                     -> false

and uses_unroll_list (ts:list term)
  : Tot bool (decreases %[terms_size ts; 1]) =
  match ts with
  | []     -> false
  | t :: r -> uses_unroll t || uses_unroll_list r

and uses_unroll_impls (is:list (op_id & term))
  : Tot bool (decreases %[impls_size is; 1]) =
  match is with
  | []          -> false
  | (_, t) :: r -> uses_unroll t || uses_unroll_impls r

let mx (a b:nat) : Tot nat = if a > b then a else b

let rec ops_bound (ops:list op_id) : Tot nat (decreases ops) =
  match ops with
  | []      -> 0
  | o :: r  -> mx (o + 1) (ops_bound r)

/// One past the highest word id `t` calls: every `TWord w` and every dispatch
/// target in `t` has `w < word_bound t`, and `word_bound t = 0` exactly when `t`
/// calls nothing.
///
/// THE DICTIONARY IS ORDERED (D-70). A word may call only words defined BEFORE
/// it, and since ids are handed out in definition order that is precisely
/// `word_bound body <= id`. Two things follow, and they are the reason this
/// replaced D-67's `mentions_word`:
///
///   * Recursion is detected without a call graph. `E06.install_def` marks a
///     word `!Rec` — resolved at runtime by frame lookup rather than by
///     inlining — exactly when its body breaks the ordering. Self-reference
///     breaks it, so D-67's case is still caught.
///   * MUTUAL RECURSION NEEDS NO DETECTION, because it cannot arise. For `f`
///     and `g` to call each other one of them must name a word defined after
///     it, which breaks the ordering and gets the same `!Rec` mark. The
///     transitive call-graph reachability that `mentions_word`'s header
///     admitted it was missing is not needed: the ordering is the invariant
///     that reachability would have had to establish.
///
/// It is also the termination measure `M11.specialize` needs. Inlining every
/// call to the highest word in `t` yields a term of strictly smaller
/// `word_bound`, because the body substituted in is ordered below it — see
/// `M10.dict_ordered`.
let rec word_bound (t:term) : Tot nat (decreases %[(term_size t <: nat); 0]) =
  match t with
  | TWord w               -> w + 1
  | TSeq a b              -> mx (word_bound a) (word_bound b)
  /// The dispatch targets are CALLS (D-68), so they count. This is the one
  /// place `mentions_word` was wrong as well as incomplete: it returned `false`
  /// here, which was harmless only because `E04` allocated case operation ids
  /// above the word being defined, where nothing could collide with them.
  | TDispatch ops _       -> ops_bound ops
  | THandle _ _ i impls b -> mx (word_bound i) (mx (word_bound_impls impls)
                                                   (word_bound b))
  | TTry _ _ b c          -> mx (word_bound b) (word_bound c)
  | TSpecialize b         -> word_bound b
  | _                     -> 0

and word_bound_list (ts:list term)
  : Tot nat (decreases %[terms_size ts; 1]) =
  match ts with
  | []     -> 0
  | t :: r -> mx (word_bound t) (word_bound_list r)

and word_bound_impls (is:list (op_id & term))
  : Tot nat (decreases %[impls_size is; 1]) =
  match is with
  | []          -> 0
  | (o, t) :: r -> mx (o + 1) (mx (word_bound t) (word_bound_impls r))

/// `t` may be the body of the word defined at `w`: it calls nothing defined at
/// or after `w`. The negation is what `E06` reads as "this word is recursive".
let ordered_at (w:word_id) (t:term) : Tot bool = word_bound t <= w
