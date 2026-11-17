import Catcat.Kernel.Term
namespace Catcat
variable {B N : Type} [BEq B] [BEq N]

/-- Whether framing `s`, adding one segment below both sides, gives `t`. -/
def Sig.fits (s t : Sig B) : Bool :=
  let r := t.pre.drop s.pre.length
  s.pre ++ r == t.pre && s.post ++ r == t.post

/-- `a` then `b`. Whichever of `a.post` and `b.pre` is deeper passes its remainder through. -/
def Sig.compose (a b : Sig B) : Option (Sig B) :=
  if a.post.length ≥ b.pre.length then
    let r := a.post.drop b.pre.length
    if b.pre ++ r == a.post then some ⟨a.pre, b.post ++ r⟩ else none
  else
    let r := b.pre.drop a.post.length
    if a.post ++ r == b.pre then some ⟨a.pre ++ r, b.post⟩ else none

/-- The one signature all branches have once each is framed to the deepest. -/
def Sig.join : List (Sig B) → Option (Sig B)
  | [] => none
  | s :: ss =>
    ss.foldlM (fun a b => if b.fits a then some a else if a.fits b then some b else none) s

mutual
def Term.infer (code : Sig B → B) : Term B N → Option (Sig B)
  | .nil => some ⟨[], []⟩
  | .seq t u => do (← t.infer code).compose (← u.infer code)
  | .run s => some ⟨code s :: s.pre, s.post⟩
  | .op o us => do
    let j ← Sig.join (← inferBranches code o.outs us)
    some ⟨o.pre ++ j.pre, j.post⟩
  | .handle rec st cl b => do
    guard (!rec || st.isEmpty)
    inferClauses code st cl
    let s ← b.infer code
    some ⟨st ++ s.pre, st ++ s.post⟩

/-- Each branch's signature, counted from where its outcome's results are already pushed. -/
def inferBranches (code : Sig B → B) : List (List B) → List (Term B N) → Option (List (Sig B))
  | [], [] => some []
  | out :: outs, u :: us => do
    let s ← (Sig.mk [] out).compose (← u.infer code)
    (s :: ·) <$> inferBranches code outs us
  | _, _ => none

def inferClauses (code : Sig B → B) (st : List B) : List (Op B N × Term B N) → Option Unit
  | [] => some ()
  | (o, c) :: cl => do
    let [out] := o.outs | none
    guard ((← c.infer code).fits ⟨st ++ o.pre, st ++ out⟩)
    inferClauses code st cl
end

mutual
/-- The operations a term may perform that nothing inside it handles: its effect row. -/
def Term.free : Term B N → List (Op B N)
  | .nil | .run _ => []
  | .seq t u => t.free ++ u.free
  | .op o us => o :: freeAll us
  | .handle rec _ cl b =>
    let bound o := cl.any (·.1 == o)
    -- A clause's own operations escape this handler unless it is recursive.
    b.free.filter (!bound ·) ++ (freeClauses cl).filter fun o => !(rec && bound o)

def freeAll : List (Term B N) → List (Op B N)
  | [] => []
  | t :: ts => t.free ++ freeAll ts

def freeClauses : List (Op B N × Term B N) → List (Op B N)
  | [] => []
  | (_, c) :: cl => c.free ++ freeClauses cl
end

end Catcat
