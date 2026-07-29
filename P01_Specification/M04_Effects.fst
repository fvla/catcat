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

/// One operation's declaration: which effect it belongs to, and its signature.
type op_decl = { od_eff : eff_id; od_sig : op_sig }

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
/// cannot fail. An undeclared id gets the nullary operation of effect 0, and
/// nothing is thereby made well typed that should not be — M06 checks that an
/// operation is declared before it will accept a program using it.
let op_unknown : op_decl = { od_eff = 0; od_sig = { op_pre = []; op_post = [] } }

let rec lookup_op (ops:list (op_id & op_decl)) (o:op_id)
  : Tot op_decl (decreases ops) =
  match ops with
  | []            -> op_unknown
  | (o', d) :: r  -> if o' = o then d else lookup_op r o

let op_of (env:sig_env) (o:op_id) : Tot op_sig = (lookup_op env.se_ops o).od_sig

let eff_of (env:sig_env) (o:op_id) : Tot eff_id = (lookup_op env.se_ops o).od_eff

let declared (env:sig_env) (o:op_id) : Tot bool =
  existsb (fun (o', _) -> o' = o) env.se_ops

(* ------------------------------------------------------------------------ *)
(* The free monad                                                           *)
(* ------------------------------------------------------------------------ *)

/// `free env a` is a computation returning a stack of shape `a`, built from
/// operation calls in `env`. The continuation of `Op` takes the operation's
/// results, which is what makes handlers reentrant by construction: the
/// handler receives the rest of the program and may run it zero, one, or many
/// times.
noeq type free (env:sig_env) (a:seg) : Type =
  | Pure : vstack a -> free env a
  | Op   : op:op_id
         -> vstack (op_of env op).op_pre
         -> (vstack (op_of env op).op_post -> free env a)
         -> free env a

let rec fbind (#env:sig_env) (#a #b:seg)
              (m:free env a) (f:vstack a -> free env b)
  : Tot (free env b) (decreases m) =
  match m with
  | Pure v        -> f v
  | Op op arg k   -> Op op arg (fun res -> fbind (k res) f)

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

/// Right identity and associativity are true but need functional
/// extensionality in the `Op` case: the two sides build syntactically
/// distinct continuations that agree pointwise.
///
/// ADMITTED, both. Discharging them means restating `free`'s continuation
/// field over `FStar.FunctionalExtensionality.(^->)` and redoing the
/// inductions; that is a mechanical but invasive change, and deferring it
/// keeps the shape of the definition readable while the design is still
/// moving. Nothing downstream depends on the proofs, only the statements.
let lemma_fbind_right_id (#env:sig_env) (#a:seg) (m:free env a)
  : Lemma (fbind m Pure == m) = admit ()

let lemma_fbind_assoc (#env:sig_env) (#a #b #c:seg)
                      (m:free env a)
                      (f:vstack a -> free env b)
                      (g:vstack b -> free env c)
  : Lemma (fbind (fbind m f) g == fbind m (fun v -> fbind (f v) g)) = admit ()

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
