module R03_Prelude

open FStar.List.Tot
open M01_Kinds
open M04_Effects
open M05_Terms
open R01_Runtime

let w_add : word_id = 0
let w_sub : word_id = 1
let w_mul : word_id = 2
let w_div : word_id = 3
let w_mod : word_id = 4
let w_lt  : word_id = 5
let w_le  : word_id = 6
let w_eq  : word_id = 7
let w_not : word_id = 8
let w_and : word_id = 9
let w_or  : word_id = 10
let w_true  : word_id = 11
let w_false : word_id = 12

/// EFFECT 1 IS `IO`, AND ONLY THE HOST CAN HANDLE IT (category 2).
///
/// `print` and `read` are ordinary operations of an ordinary effect -- there is
/// no second mechanism -- but no catcat program can supply an implementation,
/// because the interpreter reserves effects 0 and 1 and the surface `effect`
/// declaration allocates from 2 upward. An `IO` operation therefore always
/// escapes every handler and reaches `R05`'s caller, which performs it.
///
/// It is 1 and not 0 because `M04.eff_dict` reserves 0 for the Dictionary
/// (D-63). The two host-owned ids sit next to each other; nothing here depends
/// on the value, and `bin/catcat.ml` dispatches on the WORD id rather than the
/// effect, so the host loop is unaffected by the renumbering.
///
/// That asymmetry is the whole of "suppliable only by the compiler or
/// interpreter to the entry point": it is a property of who owns the id, not of
/// the effect system, which needed no new feature to express it.
let eff_io  : eff_id  = 1
let w_print : word_id = 13
let w_read  : word_id = 14

let w_user_base : word_id = 100

let prelude : rdict = [
  (w_add, WPrim OAddI);
  (w_sub, WPrim OSubI);
  (w_mul, WPrim OMulI);
  (w_div, WPrim ODivI);
  (w_mod, WPrim OModI);
  (w_lt,  WPrim OLtI);
  (w_le,  WPrim OLeI);
  (w_eq,  WPrim OEqI);
  (w_not, WPrim ONot);
  (w_and, WPrim OAnd);
  (w_or,  WPrim OOr);
  /// Spelled out rather than via `bool_lit`, which the interface orders after
  /// `prelude` — implementation order must match interface order in an
  /// `.fst`/`.fsti` pair.
  (w_true,  WDef (TPrimOp (PLit (LPrim PBool true))));
  (w_false, WDef (TPrimOp (PLit (LPrim PBool false))));
  (w_print, WOp eff_io);
  (w_read,  WOp eff_io);
]

/// `PI64`'s representation is `sint 64`, so the literal must be in range. Out
/// of range collapses to 0 rather than failing: this helper exists for writing
/// tests, and M06 is what rejects bad literals in real programs.
let int_lit (n:int) : Tot term =
  if -(pow2 63) <= n && n < pow2 63
  then TPrimOp (PLit (LPrim PI64 n))
  else TPrimOp (PLit (LPrim PI64 0))

let bool_lit (b:bool) : Tot term = TPrimOp (PLit (LPrim PBool b))

let rec cat (ts:list term) : Tot term (decreases ts) =
  match ts with
  | []      -> TNil
  | t :: [] -> t
  | t :: r  -> TSeq t (cat r)
