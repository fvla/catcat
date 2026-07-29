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
/// syntactic argument to a construct that consumes it -- `TCase`, `THandle`,
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
(* Terms                                                                    *)
(* ------------------------------------------------------------------------ *)

noeq type term =
  /// The empty program. Identity of composition.
  | TNil     : term
  /// Juxtaposition. The ONLY sequencing construct: `a b` and nothing else.
  | TSeq     : term -> term -> term
  | TLit     : lit -> term
  | TStack   : sop -> term
  /// A named word, or an interface operation. The typing rules do not
  /// distinguish them -- that is the unification of D03 made concrete.
  | TWord    : word_id -> term
  /// Bundle a representation segment into a nominal type, and its inverse.
  /// Named `TPack`/`TUnpack` rather than `TSeal`/`TUnseal` to stay clear of
  /// the `dtype` constructor `M01_Kinds.TSeal`.
  /// `TUnpack` is well typed only inside the class body (D03).
  | TPack    : nom_id -> list cap -> seg -> term
  | TUnpack  : nom_id -> list cap -> seg -> term
  /// Sum introduction: build variant `tag` of `variants`.
  | TInj     : variants:list seg -> tag:nat -> term
  /// `( bool -- TSum [[]; []] )`, false to tag 0 and true to tag 1.
  ///
  /// This is the ONLY way to branch on a boolean, and it is deliberately a
  /// coercion rather than an eliminator (D-33). `bool` is a primitive, so
  /// `TCase` -- which eliminates a sum -- cannot see it; giving the core a
  /// separate `TIf` would mean a second copy of the branch-agreement rule that
  /// `infer_branches` already implements. One coercion plus the existing rule
  /// costs one constructor and no new typing logic.
  ///
  /// The tag order is `false = 0`, `true = 1`, matching the usual reading of a
  /// bool as a two-element enumeration. Surface `if` therefore lists its ELSE
  /// branch first; `E04` is where that is arranged, and it is stated in both
  /// places because a silent reversal here would be a plausible-looking bug.
  | TBoolSum : term
  /// Sum elimination: one `{}` block per variant, all with the same result.
  | TCase    : variants:list seg -> branches:list term -> term
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
  /// Resolve the static effects of the body against the ambient dictionary,
  /// producing a residual program. Invoked at elaboration time this is
  /// specialization; invoked at runtime it is the JIT. One construct, one
  /// theorem (M11).
  | TSpecialize : body:term -> term
  /// Pointer operations. `TBoxOpen` consumes the box and yields the payload;
  /// there is no discard, because `TBox` lacks `CDrop` and the payload must be
  /// dealt with explicitly.
  | TBoxNew   : dtype -> term
  | TBoxOpen  : dtype -> term
  /// `TRcClone` is the `Clone` interface word and `TRcDrop` is `release` --
  /// neither is `dup` or `pop`, which is exactly why `TRc` carries no
  /// capabilities. `TRcRead` needs a copyable payload; the alternative is
  /// borrowing, deliberately deferred.
  | TRcNew    : dtype -> term
  | TRcClone  : dtype -> term
  | TRcDrop   : dtype -> term
  | TRcRead   : dtype -> term
  /// Roll and unroll an incomplete type. Runtime no-ops; they exist so that
  /// the type system can cross a `TName` boundary explicitly rather than by
  /// silent coercion.
  | TRoll     : nom_id -> dtype -> term
  | TUnroll   : nom_id -> dtype -> term

(* ------------------------------------------------------------------------ *)
(* Structural measures                                                      *)
(* ------------------------------------------------------------------------ *)

let rec term_size (t:term) : Tot pos =
  match t with
  | TNil                -> 1
  | TSeq a b            -> 1 + term_size a + term_size b
  | TLit _              -> 1
  | TStack _            -> 1
  | TWord _             -> 1
  | TPack _ _ _         -> 1
  | TUnpack _ _ _       -> 1
  | TInj _ _            -> 1
  | TBoolSum            -> 1
  | TCase _ bs          -> 1 + terms_size bs
  | THandle _ _ i impls b -> 1 + term_size i + impls_size impls + term_size b
  | TSpecialize b       -> 1 + term_size b
  | TBoxNew _           -> 1
  | TBoxOpen _          -> 1
  | TRcNew _            -> 1
  | TRcClone _          -> 1
  | TRcDrop _           -> 1
  | TRcRead _           -> 1
  | TRoll _ _           -> 1
  | TUnroll _ _         -> 1

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
  | TCase variants bs    -> TCase variants (subst_words_list su bs)
  | THandle e st i im b  -> THandle e st (subst_words su i)
                                    (subst_words_impls su im)
                                    (subst_words su b)
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
  | TCase _ bs          -> needs_compiler_list bs
  | THandle _ _ i impls b -> needs_compiler i || needs_compiler_impls impls
                           || needs_compiler b
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
