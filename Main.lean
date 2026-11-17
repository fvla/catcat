import Catcat
open Catcat

def usage : IO UInt32 := do
  IO.eprintln "usage: catcat FILE [FUEL]   run a program"
  IO.eprintln "       catcat js FILE       print it as JavaScript"
  return 2

def main : List String → IO UInt32
  | ["js", path] => do
    match JS.emitSource (← IO.FS.readFile path) with
    | .ok program => IO.print program.print; return 0
    | .error e => IO.eprintln s!"error: {e}"; return 1
  | path :: rest => do
    let fuel := (rest.head? >>= String.toNat?).getD 10000000
    let outcome := runSource (← IO.FS.readFile path) fuel
    IO.print outcome.render
    return if outcome.result.isOk then 0 else 1
  | [] => usage
