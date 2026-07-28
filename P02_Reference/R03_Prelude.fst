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
]

/// `PI64`'s representation is `sint 64`, so the literal must be in range. Out
/// of range collapses to 0 rather than failing: this helper exists for writing
/// tests, and M06 is what rejects bad literals in real programs.
let int_lit (n:int) : Tot term =
  if -(pow2 63) <= n && n < pow2 63
  then TLit (LPrim PI64 n)
  else TLit (LPrim PI64 0)

let bool_lit (b:bool) : Tot term = TLit (LPrim PBool b)

let rec cat (ts:list term) : Tot term (decreases ts) =
  match ts with
  | []      -> TNil
  | t :: [] -> t
  | t :: r  -> TSeq t (cat r)
