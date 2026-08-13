module M04_Effects

/// catcat core specification, module 04: effect signatures and the free monad.
///
/// The central claim of D03 is that ONE construct plays the role of effects,
/// interfaces, traits, classes, modules and the Dictionary. That construct is
/// `eff_sig` below: a named set of word declarations with stack signatures.
/// What varies between those five uses is only which handler is in scope and
/// when it is resolved -- never the underlying mechanism.
///
/// Effects are given free-monad semantics, so a program's meaning is a syntax
/// tree of operation calls rather than an interpretation of them. Handlers
/// (M10) interpret that tree. Deep handlers, which fold through the
/// continuation, are what the draft was describing when it required every
/// effect to be reentrant.

open FStar.List.Tot
open FStar.FunctionalExtensionality
open M01_Kinds
open M02_Stacks
open M03_Signatures

(* ------------------------------------------------------------------------ *)
(* Operations, effects, rows                                                *)
(* ------------------------------------------------------------------------ *)

type op_id  = nat
type eff_id = nat

/// An operation is declared exactly like a word: a stack signature. This is
/// not an analogy -- `declare-word` in an `interface` block elaborates to one
/// of these.
type op_sig = { op_pre : seg; op_post : seg }

let sig_of_op (o:op_sig) : srow = { pre = o.op_pre; post = o.op_post }

/// When an effect is resolved. `SStatic` effects must be discharged during
/// elaboration and are erased before runtime -- this is the annotation M11's
/// zero-cost theorem quantifies over. `SDynamic` effects survive to runtime
/// and compile to handler-frame lookup.
type stage =
  | SStatic
  | SDynamic

/// An effect row. The row variable is implicit, exactly as for stack rows.
type erow = list (eff_id & stage)

let pure_row : erow = []

/// EFFECT 0 IS THE DICTIONARY, AND IT IS RESERVED (D-37, D-63).
///
/// D-37 said `!Dict` is to effect rows what the implicit row variable is to
/// stack signatures: pervasive, never written, static by default. It also said
/// rows stay clean because a statically resolved word is `TWord w` and not a
/// `Dict` operation, so `within` never sees it. THAT LAST CLAUSE WAS WRONG, and
/// M07 is where it was found: `denote_static` gives `TWord w` the denotation
/// `Op w` (D-60), because a word has a signature and no body and the ambient
/// Dictionary is what supplies one. A word call IS an operation call, so the
/// Dictionary needs an id like any other effect.
///
/// Reserving 0 rather than allocating one has two consequences worth naming.
/// `op_unknown` below now defaults to `Dict` rather than to whatever effect
/// happened to be numbered 0 -- an undeclared word is a Dictionary word with
/// signature `( -- )`, which is what it should always have been. And the host's
/// `IO` moves to 1 (`R03.eff_io`), so the two reserved ids sit next to each
/// other and user effects allocate from 2.
///
/// It stays INVISIBLE at the surface: `E05.row_effs` drops a static `Dict`
/// entry when rendering a row, which is the elision D-37 asked for, now
/// implemented in one place instead of assumed.
let eff_dict : eff_id = 0

/// One operation's declaration: which effect it belongs to, at which stage, and
/// its signature.
///
/// `od_stage` is here rather than left to the caller's row because the stage of
/// an operation is a property of its DECLARATION -- `Dict` words are static,
/// a declared effect's operations are dynamic until D04's annotations reach the
/// surface -- and because it lets `M06.w_eff` derive the row entry for a word
/// instead of trusting a table to have stored a consistent one.
type op_decl = { od_eff : eff_id; od_stage : stage; od_sig : op_sig }

/// The ambient declaration table. Keeping operations in a table rather than
/// inside the `free` type is what lets a handler replace an operation's
/// implementation without changing any program's type.
///
/// AN ASSOCIATION LIST, NOT A FUNCTION (D-45). The obvious spelling of this
/// record is `{ op_of : op_id -> op_sig; eff_of : op_id -> eff_id }`, and it
/// was, until the REPL had to build one: constructing a function-typed field
/// needs a closure, which is outside the first-order subset every extractable
/// module is written in (D-20). A table is constructible by anything that can
/// build a list, which is the whole point.
type sig_env = { se_ops : list (op_id & op_decl) }

let empty_sig_env : sig_env = { se_ops = [] }

/// The declaration an UNDECLARED operation resolves to.
///
/// A total function is not a convenience here, it is a requirement: `op_of`
/// appears inside the TYPE of `free`, so it cannot return an option and it
/// cannot fail. An undeclared id gets the nullary operation of `Dict`, and
/// nothing is thereby made well typed that should not be — M06 checks that an
/// operation is declared before it will accept a program using it.
///
/// `Dict` is the right default and not merely an available one: an unknown word
/// is a Dictionary word nobody has bound, so `( -- )` at `!Dict` describes it
/// exactly. Before `eff_dict` existed this read `od_eff = 0`, which under P03's
/// numbering silently claimed the unknown word performed `IO`.
let op_unknown : op_decl = { od_eff = eff_dict; od_stage = SStatic;
                             od_sig = { op_pre = []; op_post = [] } }

let rec lookup_op (ops:list (op_id & op_decl)) (o:op_id)
  : Tot op_decl (decreases ops) =
  match ops with
  | []            -> op_unknown
  | (o', d) :: r  -> if o' = o then d else lookup_op r o

let op_of (env:sig_env) (o:op_id) : Tot op_sig = (lookup_op env.se_ops o).od_sig

let eff_of (env:sig_env) (o:op_id) : Tot eff_id = (lookup_op env.se_ops o).od_eff

let stage_of (env:sig_env) (o:op_id) : Tot stage = (lookup_op env.se_ops o).od_stage

let declared (env:sig_env) (o:op_id) : Tot bool =
  existsb (fun (o', _) -> o' = o) env.se_ops

(* ------------------------------------------------------------------------ *)
(* The free monad                                                           *)
(* ------------------------------------------------------------------------ *)

/// `free env a` is a computation returning a stack of shape `a`, built from
/// operation calls in `env`. The `Op` node carries the operation's arguments
/// and the REST OF THE PROGRAM, as a function of the operation's results.
///
/// That "rest of the program" is a continuation in the technical sense, but it
/// is not one a handler ever receives: per D-36 a handler implementation takes
/// the arguments, returns the results, and never sees the tail. The tail is
/// here because a free monad has to represent sequencing somehow, and this is
/// how; M10's `handle` walks past it rather than handing it over.
///
/// THE CONTINUATION IS A RESTRICTED FUNCTION (`^->`, i.e. `on_domain`-normal).
/// This is what makes the monad laws below provable rather than admitted. Both
/// laws are true pointwise and the two sides build syntactically distinct
/// lambdas, so `==` on the raw arrow type is out of reach; `^->` is exactly the
/// device F*'s library provides for that, and the only cost is an `on` at each
/// construction site. There is precisely one such site, in `fbind`.
noeq type free (env:sig_env) (a:seg) : Type =
  | Pure : vstack a -> free env a
  | Op   : op:op_id
         -> oarg:vstack (op_of env op).op_pre
         -> okont:(vstack (op_of env op).op_post ^-> free env a)
         -> free env a

let rec fbind (#env:sig_env) (#a #b:seg)
              (m:free env a) (f:vstack a -> free env b)
  : Tot (free env b) (decreases m) =
  match m with
  | Pure v        -> f v
  | Op op arg k   -> Op op arg (on _ (fun res -> fbind (k res) f))

/// Kleisli composition. THIS is sequential composition of catcat programs:
/// M07 defines the denotation so that juxtaposition is exactly `kcomp`.
let kcomp (#env:sig_env) (#a #b #c:seg)
          (f:vstack a -> free env b) (g:vstack b -> free env c)
  : vstack a -> free env c =
  fun s -> fbind (f s) g

(* ------------------------------------------------------------------------ *)
(* Monad laws                                                               *)
(* ------------------------------------------------------------------------ *)

/// Left identity holds definitionally.
let lemma_fbind_left_id (#env:sig_env) (#a #b:seg)
                        (v:vstack a) (f:vstack a -> free env b)
  : Lemma (fbind (Pure v) f == f v) = ()

/// Right identity and associativity need functional extensionality in the `Op`
/// case: the two sides build continuations that agree pointwise but are not the
/// same term. Each is proved in two pieces -- a helper doing the `Op` step, and
/// an induction that supplies the pointwise hypothesis -- and both rely on
/// `free`'s continuation being `on_domain`-normal, since `extensionality`
/// concludes about `on_domain f` and nothing else would bridge back to the `Op`
/// node.
///
/// THE HELPERS TAKE THE CONSTRUCTOR APPLIED, and that is the whole trick. Two
/// alpha-equivalent lambdas written at two places are different closures to the
/// solver, so an inductive proof that spells out `fbind`'s continuation at its
/// own site can never connect it to the one `fbind` built. Applying the helper
/// to a literal `Op` node lets F* reduce `fbind` by conversion instead, and the
/// continuation is then obtained by PROJECTION -- never written down, so never
/// a second closure.
///
/// The `requires` of each helper is stated so that it contains no lambda the
/// caller does not already have: right identity's is lambda-free outright, and
/// associativity's composite is taken as the parameter `h`.

/// Right identity, one `Op` node deep.
let lemma_right_id_op (#env:sig_env) (#a:seg) (op:op_id)
                      (arg:vstack (op_of env op).op_pre)
                      (k:(vstack (op_of env op).op_post ^-> free env a))
  : Lemma (requires (forall res. fbind (k res) Pure == k res))
          (ensures  fbind (Op op arg k) Pure == Op op arg k) =
  let k' : (vstack (op_of env op).op_post ^-> free env a) =
    Op?.okont (fbind (Op op arg k) Pure) in
  extensionality (vstack (op_of env op).op_post) (fun _ -> free env a) k' k

let rec lemma_fbind_right_id (#env:sig_env) (#a:seg) (m:free env a)
  : Lemma (ensures fbind m Pure == m) (decreases m) =
  match m with
  | Pure _      -> ()
  | Op op arg k ->
    let aux (res:vstack (op_of env op).op_post)
      : Lemma (fbind (k res) Pure == k res) =
      lemma_fbind_right_id (k res) in
    FStar.Classical.forall_intro aux;
    lemma_right_id_op op arg k

/// The same shape for associativity, with the composite `h` left abstract
/// rather than spelled as a lambda. That generality is not decoration: writing
/// `fun v -> fbind (f v) g` inside the helper would make it a DIFFERENT closure
/// from the one the caller's goal mentions, and the two could not be related.
/// Taking it as a parameter means the caller supplies its own, once, and the
/// helper never has to name it.
let lemma_assoc_op (#env:sig_env) (#a #b #c:seg) (op:op_id)
                   (arg:vstack (op_of env op).op_pre)
                   (k:(vstack (op_of env op).op_post ^-> free env a))
                   (f:vstack a -> free env b)
                   (g:vstack b -> free env c)
                   (h:vstack a -> free env c)
  : Lemma (requires (forall res. fbind (fbind (k res) f) g == fbind (k res) h))
          (ensures  fbind (fbind (Op op arg k) f) g == fbind (Op op arg k) h) =
  let k1 : (vstack (op_of env op).op_post ^-> free env c) =
    Op?.okont (fbind (fbind (Op op arg k) f) g) in
  let k2 : (vstack (op_of env op).op_post ^-> free env c) =
    Op?.okont (fbind (Op op arg k) h) in
  extensionality (vstack (op_of env op).op_post) (fun _ -> free env c) k1 k2

let rec lemma_fbind_assoc (#env:sig_env) (#a #b #c:seg)
                          (m:free env a)
                          (f:vstack a -> free env b)
                          (g:vstack b -> free env c)
  : Lemma (ensures fbind (fbind m f) g == fbind m (fun v -> fbind (f v) g))
          (decreases m) =
  match m with
  | Pure _      -> ()
  | Op op arg k ->
    let aux (res:vstack (op_of env op).op_post)
      : Lemma (fbind (fbind (k res) f) g == fbind (k res) (fun v -> fbind (f v) g)) =
      lemma_fbind_assoc (k res) f g in
    FStar.Classical.forall_intro aux;
    lemma_assoc_op op arg k f g (fun v -> fbind (f v) g)

(* ------------------------------------------------------------------------ *)
(* Handling: the eliminator of `free`                                       *)
(* ------------------------------------------------------------------------ *)

/// WHY THIS IS HERE AND NOT IN M10 (D-59). `handle` is the fold over `free`,
/// and an inductive type's eliminator belongs with the type. It was in M10
/// until M07 needed it: `denote_static`'s `THandle` clause IS a call to
/// `handle`, so leaving the fold downstream of the denotation would have made
/// M07 depend on M10 and broken the rule that numbering and dependency order
/// agree.
///
/// The split is at the right seam rather than merely a convenient one. What
/// lives here is the MECHANISM, which needs nothing but the monad. What stays in
/// M10 is the IDENTIFICATION -- that this one fold serves effect handlers,
/// typeclass dictionaries, class method tables, module implementations and
/// Dictionary frames alike -- together with the laws H1-H5, which are about the
/// typing judgment and so genuinely need M06.

/// An implementation of a single operation, under D-36: it receives the
/// handler's state on top of the operation's arguments, and returns the updated
/// state on top of the operation's results. No continuation appears, and there
/// is nowhere one could be smuggled in -- the type is a plain stack transformer
/// in the free monad, so an implementation can perform effects of its own but
/// cannot see, duplicate or discard the rest of the program.
///
/// STATE ON TOP, not underneath (D-46). This is forced rather than chosen: the
/// runtime dictionary records which effect an operation belongs to and not its
/// arity, so the machine cannot splice state in beneath the arguments. It reads
/// correctly anyway, the receiver being pushed last.
type op_impl (env:sig_env) (st:seg) (o:op_sig) =
  vstack (st @ o.op_pre) -> free env (st @ o.op_post)

/// A handler for one effect: a state segment and an implementation per
/// operation. M10 is where this record is shown to be simultaneously an effect
/// handler, a typeclass dictionary, a class method table, a module
/// implementation and a Dictionary frame -- not by analogy, but because there is
/// literally one type.
///
/// The state segment is what makes a handler a CLASS rather than merely a
/// dispatch table: `st` is the instance's representation and each implementation
/// is a method over it. A stateless handler is `st = []`, so nothing needs a
/// separate rule.
///
/// `h_ops` is a function field, which every extractable module in this project
/// is forbidden (D-20). Nothing constructs a `handler` outside the
/// specification, so the closure is confined to the denotational side; the table
/// is dependently typed per operation, so de-closuring it the way D-45
/// de-closured `sig_env` would need an existential rather than a list.
noeq type handler (env:sig_env) (eff:eff_id) (st:seg) = {
  h_ops : op:op_id -> op_impl env st (op_of env op);
}

/// Interpret away one effect.
///
/// A fold over `free` carrying the handler state. `Pure` returns the state on
/// top of the body's results -- which is why M06's `THandle` rule gives the
/// composite the signature `( s.pre -- st @ s.post )`, and why `handle Counter
/// over ( i64 ) init { 0 } { ... } { tick tick + }` leaves `1 2` and not `1`.
/// An operation of `eff` runs its implementation, whose result is split back
/// into the new state and the operation's results; anything else is forwarded
/// with the handler still wrapped around the tail.
///
/// That forwarding clause is where reentrancy lives. The handler is still
/// installed around `k res`, so an operation performed by the continuation --
/// including one performed by an implementation, since an implementation's own
/// effects are part of the tree it returns -- reaches this same handler. No
/// continuation was captured to achieve it.
let rec handle (#env:sig_env) (#eff:eff_id) (#st:seg) (#a:seg)
               (h:handler env eff st) (state:vstack st) (m:free env a)
  : Tot (free env (st @ a)) (decreases m) =
  match m with
  | Pure v      -> Pure (vappend state v)
  | Op op arg k ->
    if eff_of env op = eff
    then fbind (h.h_ops op (vappend state arg))
               (fun r -> let (state', res) = vsplit st r in
                      handle h state' (k res))
    else Op op arg (on _ (fun res -> handle h state (k res)))

/// The handler that changes nothing: no state, every implementation
/// re-performing its own operation. M10's H3 is the statement that handling with
/// it is the identity, which is the sanity check that the fold loses nothing --
/// and note it typechecks only because the state segment is `[]`, so `handle`'s
/// result shape `[] @ a` is `a` on the nose.
let id_handler (env:sig_env) (eff:eff_id) : handler env eff [] =
  { h_ops = (fun op -> fun args -> Op op args (on _ Pure)) }

/// The implementation an UNIMPLEMENTED operation gets: strip the state, perform
/// the operation, put the state back. This is what makes partial overriding of a
/// Dictionary work, and it is the semantic content of M06's `infer_impls`
/// accepting a handler that does not mention every operation of its effect --
/// such an operation forwards outward, which is also what `R02.find_handler`
/// does by walking to the next frame.
let fwd_impl (env:sig_env) (st:seg) (op:op_id)
  : op_impl env st (op_of env op) =
  fun args ->
    let (state, oarg) = vsplit st args in
    Op op oarg (on _ (fun res -> Pure (vappend state res)))

(* ------------------------------------------------------------------------ *)
(* Effect rows and containment                                              *)
(* ------------------------------------------------------------------------ *)

let eff_mem (e:eff_id) (row:erow) : bool =
  existsb (fun (e', _) -> e' = e) row

/// `within row m` holds when every operation `m` can perform belongs to an
/// effect listed in `row`. M06 assigns each program an effect row; M09's
/// soundness statement is in part that the denotation satisfies `within` for
/// the row the type system computed.
let rec within (#env:sig_env) (#a:seg) (row:erow) (m:free env a)
  : Tot prop (decreases m) =
  match m with
  | Pure _      -> True
  | Op op _ k   -> eff_mem (eff_of env op) row /\
                   (forall res. within row (k res))

/// Purity is the empty row: no operations at all.
let lemma_within_pure (#env:sig_env) (#a:seg) (v:vstack a)
  : Lemma (within #env pure_row (Pure v)) = ()

/// Effect rows admit weakening, which is what lets a caller propagate a
/// callee's effects alongside its own.
let rec lemma_within_weaken (#env:sig_env) (#a:seg)
                            (row1 row2:erow) (m:free env a)
  : Lemma (requires (forall e. eff_mem e row1 ==> eff_mem e row2))
          (ensures  within row1 m ==> within row2 m)
          (decreases m) =
  match m with
  | Pure _    -> ()
  | Op _ _ k  ->
    let aux (res:vstack (op_of env (Op?.op m)).op_post)
      : Lemma (within row1 (k res) ==> within row2 (k res)) =
      lemma_within_weaken row1 row2 (k res)
    in
    FStar.Classical.forall_intro aux

/// A row is fully static when every effect in it is discharged at elaboration
/// time. M11's erasure theorem applies exactly to programs whose row is
/// `all_static`.
let all_static (row:erow) : bool =
  for_all (fun (_, s) -> s = SStatic) row
