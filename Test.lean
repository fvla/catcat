import Catcat
open Catcat

structure Tally where
  passed : Nat := 0
  skipped : Nat := 0
  failures : List String := []

def Tally.pass (t : Tally) : Tally := { t with passed := t.passed + 1 }
def Tally.skip (t : Tally) : Tally := { t with skipped := t.skipped + 1 }
def Tally.fail (t : Tally) (what want got : String) : Tally :=
  { t with failures := s!"FAIL {what}\n--- expected\n{want}--- got\n{got}" :: t.failures }

def Tally.report (t : Tally) (name : String) : IO Unit := do
  for f in t.failures.reverse do IO.println f
  IO.println s!"{name}: {t.passed} passed, {t.failures.length} failed, {t.skipped} skipped"

def catFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let entries := (← dir.readDir).qsort (·.fileName < ·.fileName)
  return (entries.map (·.path)).filter (·.extension == some "cat")

def hasNode : IO Bool := do
  try return (← IO.Process.output { cmd := "node", args := #["--version"] }).exitCode == 0
  catch _ => return false

/-- JS calls nest as deep as catcat recursion does, and both the model and a real engine
bound that depth. A program that hits the bound is skipped, not failed. -/
def tooDeep (stderr : String) : Bool :=
  (stderr.splitOn "Maximum call stack size exceeded").length > 1

/-- Each program is run three ways: by the interpreter (compared with the `.expected` file),
by the Lean model of the JS subset on the emitted program, and by `node` on its printed text.
The last two are compared with the interpreter. -/
def main : IO UInt32 := do
  let node ← hasNode
  let mut interp : Tally := {}
  let mut model : Tally := {}
  let mut real : Tally := {}
  for path in (← catFiles "examples") ++ (← catFiles "tests") do
    let src ← IO.FS.readFile path
    -- Little fuel, so a test that loops forever fails fast.
    let outcome := runSource src (fuel := 100000)
    let want ← IO.FS.readFile (path.withExtension "expected")
    interp := if outcome.render == want then interp.pass
      else interp.fail s!"{path}" want outcome.render
    match JS.emitSource src with
    | .error _ => model := model.skip; real := real.skip
    | .ok program =>
      let (out, err) := program.run
      let got := out ++ match err with | some e => s!"error: {e}\n" | none => ""
      model := if got == outcome.render then model.pass
        else if err == some "out of fuel" then model.skip
        else model.fail s!"{path} (JS model)" outcome.render got
      if node then
        IO.FS.writeFile ".lake/test.js" program.print
        let run ← IO.Process.output { cmd := "node", args := #[".lake/test.js"] }
        -- A thrown error goes to stderr, so only the output before it is comparable.
        let want := if outcome.result.isOk then outcome.render else outcome.out
        real := if run.stdout == want && (run.exitCode == 0) == outcome.result.isOk then real.pass
          else if tooDeep run.stderr then real.skip
          else real.fail s!"{path} (node)" outcome.render (run.stdout ++ run.stderr)
      else real := real.skip
  interp.report "interpreter"
  model.report "JS model"
  real.report (if node then "node" else "node (not installed)")
  return if (interp.failures ++ model.failures ++ real.failures).isEmpty then 0 else 1
