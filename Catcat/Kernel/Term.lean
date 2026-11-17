namespace Catcat

/-- A stack signature. Lists are top-first. Read `∀ r, pre ++ r → post ++ r`. -/
structure Sig (B : Type) where
  pre : List B
  post : List B
deriving BEq, Repr

/-- An operation label. It carries its own signature: one result segment per outcome. -/
structure Op (B N : Type) where
  name : N
  pre : List B
  outs : List (List B)
deriving BEq, Repr

inductive Term (B N : Type) where
  | nil
  | seq (t u : Term B N)
  /-- Performs `o`, then continues with the branch for the outcome it chose. -/
  | op (o : Op B N) (branches : List (Term B N))
  /-- `st` is the type of the handler's state, which sits on top of the stack on entry and exit.
  With `rec`, a clause's own operations are handled by this same handler. -/
  | handle (rec : Bool) (st : List B) (clauses : List (Op B N × Term B N)) (body : Term B N)
  /-- Pops a code value of signature `s` and executes it here. -/
  | run (s : Sig B)

end Catcat
