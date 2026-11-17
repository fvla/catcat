import Catcat.Kernel.Term
namespace Catcat
variable {B N V : Type}

/-- A computation: finished, waiting on an operation, or stuck. -/
inductive Free (B N V : Type) where
  | pure (stack : List V)
  | op (o : Op B N) (args : List V) (k : Nat → List V → Free B N V)
  | stuck (msg : String)
  /-- Means `next ()`. Returning it lets a long chain of recursive calls unwind the native stack. -/
  | later (next : Unit → Free B N V)

abbrev Kont (B N V : Type) := List V → Free B N V
/-- A meaning takes the stack and the rest of the computation. -/
abbrev Den (B N V : Type) := List V → Kont B N V → Free B N V
/-- A handler in action: its state, the computation it handles, and what follows. -/
abbrev Handling (B N V : Type) := List V → Free B N V → Kont B N V → Free B N V

section
variable [BEq B] [BEq N]

/-- Handles `m` with state `st`. Only `reenter`, which handles a recursive clause's own
operations, is not structural; `handler` passes it in with less fuel. -/
def handlerStep (reenter : Handling B N V) (rec : Bool) (nst : Nat)
    (clauses : List (Op B N × Den B N V)) : Handling B N V
  | st, .pure v, k => k (st ++ v)
  | _, .stuck msg, _ => .stuck msg
  | st, .later next, k => .later fun _ => handlerStep reenter rec nst clauses st (next ()) k
  | st, .op o x kk, k =>
    match clauses.lookup o with
    | none => .op o x fun i r => handlerStep reenter rec nst clauses st (kk i r) k
    | some c =>
      if rec then .later fun _ => reenter [] (c x (kk 0)) k
      else c (st ++ x) fun r =>
        handlerStep reenter rec nst clauses (r.take nst) (kk 0 (r.drop nst)) k

def handler (rec : Bool) (nst : Nat) (clauses : List (Op B N × Den B N V)) : Nat → Handling B N V
  | 0 => handlerStep (fun _ _ _ => .stuck "out of fuel") rec nst clauses
  | fuel + 1 => handlerStep (handler rec nst clauses fuel) rec nst clauses

mutual
/-- `again` gives the meaning of a decoded code value. Like `reenter`, it is the one call
that is not structural, and `den` passes it in with less fuel. -/
def denStep (decode : V → Option (Term B N)) (again : Term B N → Den B N V) (fuel : Nat) :
    Term B N → Den B N V
  | .nil => fun s k => k s
  | .seq t u => fun s k => denStep decode again fuel t s fun s => denStep decode again fuel u s k
  | .op o us => fun s k =>
    let branches := denAll decode again fuel us
    .op o (s.take o.pre.length) fun i r =>
      match branches[i]? with
      | some d => d (r ++ s.drop o.pre.length) k
      | none => .stuck "an operation chose an outcome it does not have"
  | .handle rec st cl b => fun s k =>
    handler rec st.length (denClauses decode again fuel cl) fuel (s.take st.length)
      (denStep decode again fuel b (s.drop st.length) .pure) k
  | .run _ => fun s k =>
    match s with
    | c :: s => match decode c with
      | some t => again t s k
      | none => .stuck "run: not a code value"
    | [] => .stuck "run: empty stack"

def denAll (decode : V → Option (Term B N)) (again : Term B N → Den B N V) (fuel : Nat) :
    List (Term B N) → List (Den B N V)
  | [] => []
  | t :: ts => denStep decode again fuel t :: denAll decode again fuel ts

def denClauses (decode : V → Option (Term B N)) (again : Term B N → Den B N V) (fuel : Nat) :
    List (Op B N × Term B N) → List (Op B N × Den B N V)
  | [] => []
  | (o, c) :: cl => (o, denStep decode again fuel c) :: denClauses decode again fuel cl
end

/-- The meaning of a term. Fuel is spent only by `run` and by recursive handlers. -/
def den (decode : V → Option (Term B N)) : Nat → Term B N → Den B N V
  | 0 => denStep decode (fun _ _ _ => .stuck "out of fuel") 0
  | fuel + 1 => denStep decode (den decode fuel) (fuel + 1)

end

/-- Runs to completion under a root model with state `σ`. The model returns the chosen
outcome, the results and its new state. -/
def Free.exec {σ : Type}
    (root : Op B N → List V → σ → Except String (Nat × List V × σ)) :
    Free B N V → σ → Except String (List V) × σ
  | .pure stack, w => (.ok stack, w)
  | .stuck msg, w => (.error msg, w)
  | .later next, w => (next ()).exec root w
  | .op o x k, w =>
    match root o x w with
    | .ok (i, r, w) => (k i r).exec root w
    | .error msg => (.error msg, w)

end Catcat
