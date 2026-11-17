namespace Catcat

inductive Bracket where
  | paren | square | brace
deriving BEq, Repr

inductive Item where
  | int (n : Int)
  | word (w : String)
  | group (b : Bracket) (items : List Item)
deriving BEq, Repr

def Bracket.opening : Bracket → String
  | .paren => "(" | .square => "[" | .brace => "{"

def Bracket.closing : Bracket → String
  | .paren => ")" | .square => "]" | .brace => "}"

mutual
def Item.show : Item → String
  | .int n => toString n
  | .word w => w
  | .group b items => s!"{b.opening} {showItems items}{b.closing}"

def showItems : List Item → String
  | [] => ""
  | i :: is => i.show ++ " " ++ showItems is
end

def words (line : String) : List String :=
  let flush w ws := if w = "" then ws else w :: ws
  let step c | (w, ws) => if c.isWhitespace then ("", flush w ws) else (c.toString ++ w, ws)
  let (w, ws) := line.toList.foldr step ("", [])
  flush w ws

/-- A lone `#` starts a comment that runs to the end of the line. -/
def tokens (src : String) : List String :=
  (src.splitOn "\n").flatMap fun line => (words line).takeWhile (· ≠ "#")

/-- `cur` holds the innermost open group's items, newest first; `outer` the groups around it. -/
def readToken : List Item × List (Bracket × List Item) → String →
    Except String (List Item × List (Bracket × List Item))
  | (cur, outer), tok =>
    let opened := [Bracket.paren, .square, .brace].find? (·.opening == tok)
    let closed := [Bracket.paren, .square, .brace].find? (·.closing == tok)
    match opened, closed, outer with
    | some b, _, _ => pure ([], (b, cur) :: outer)
    | _, some b, (b', up) :: outer =>
      if b == b' then pure (.group b cur.reverse :: up, outer)
      else throw s!"expected {b'.closing}, found {tok}"
    | _, some _, [] => throw s!"unmatched {tok}"
    | none, none, _ =>
      pure ((match tok.toInt? with | some n => .int n | none => .word tok) :: cur, outer)

def read (src : String) : Except String (List Item) := do
  match ← (tokens src).foldlM readToken ([], []) with
  | (cur, []) => pure cur.reverse
  | (_, (b, _) :: _) => throw s!"unclosed {b.opening}"

end Catcat
