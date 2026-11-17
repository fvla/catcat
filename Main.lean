import Catcat

def main : List String → IO UInt32
  | path :: rest => do
    let fuel := (rest.head? >>= String.toNat?).getD 10000000
    let outcome := Catcat.runSource (← IO.FS.readFile path) fuel
    IO.print outcome.render
    return if outcome.result.isOk then 0 else 1
  | [] => do
    IO.eprintln "usage: catcat FILE [FUEL]"
    return 2
