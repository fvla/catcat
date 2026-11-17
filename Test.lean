import Catcat
open Catcat

/-- Runs every `.cat` file in `dir` and compares what it prints with the `.expected` file
beside it. Returns how many passed and how many failed. -/
def checkDir (dir : System.FilePath) : IO (Nat × Nat) := do
  let mut passed := 0
  let mut failed := 0
  for entry in (← dir.readDir).qsort (·.fileName < ·.fileName) do
    if entry.path.extension == some "cat" then
      -- Little fuel, so a test that loops forever fails fast.
      let got := (runSource (← IO.FS.readFile entry.path) (fuel := 100000)).render
      let want ← IO.FS.readFile (entry.path.withExtension "expected")
      if got == want then passed := passed + 1
      else
        failed := failed + 1
        IO.println s!"FAIL {entry.path}\n--- expected\n{want}--- got\n{got}"
  return (passed, failed)

def main : IO UInt32 := do
  let (p1, f1) ← checkDir "examples"
  let (p2, f2) ← checkDir "tests"
  IO.println s!"{p1 + p2} passed, {f1 + f2} failed"
  return if f1 + f2 == 0 then 0 else 1
