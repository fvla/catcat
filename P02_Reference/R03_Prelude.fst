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

/// THE RESERVED EFFECT BLOCK: 0 `Dict`, 1 `IO`, 2 `Unsafe`, 3 `C`, 4 `Rec`
/// (D-66, D-67).
///
/// All five are HOST EFFECTS in the same precise sense: no catcat program can
/// supply an implementation for one, because `effect` allocates from
/// `eff_user_base` upward and cannot name an id below it. What varies is who
/// discharges them.
///
///   * `Dict` (0, `M04.eff_dict`) is discharged by the ambient Dictionary at
///     elaboration time — `M11.specialize`. Every word carries it (D-63).
///   * `IO` (1) is discharged by the interpreter's caller, which performs the
///     operation and resumes. `print` and `read`.
///   * `Unsafe` (2) HAS NO OPERATIONS AT ALL, and that is the whole design
///     (D-57): a word carries `!Unsafe` in its row without there being anything
///     to perform, so unsafety propagates by the ordinary row rules and cannot
///     be hidden by forgetting to annotate. `handle Unsafe` with an empty
///     implementation list discharges it, which is what an `unsafe { … }` block
///     is — an ordinary handler, greppable, with no special case anywhere.
///   * `C` (3) is a foreign call. `extern` declares one; the host performs it
///     against libc. Every `extern` word ALSO carries `!Unsafe`, because the
///     thing on the other side of the boundary is not checked by anything here.
///   * `Rec` (4) HAS NO OPERATIONS EITHER, and is the other half of the same
///     idea as `Unsafe`: a word whose body calls itself carries it, so "may not
///     terminate" is in the signature rather than left for a reader to derive
///     (D-67). Koka spells the same thing `div`. Discharging it with
///     `handle Rec` is a claim that this call does terminate, unproved and
///     therefore exactly as much of a promise as `unsafe` is.
///
/// RESERVING AN ID IS THE WHOLE MECHANISM, and it needed no new feature: it is
/// a fact about who owns the identifier, not a restriction the effect system
/// had to grow. Note that reserved does not mean unhandleable — `handle IO`
/// works and is how a test mocks output. What a program cannot do is DECLARE a
/// new effect that the host will service.
let eff_dict_r  : eff_id = 0
let eff_io      : eff_id = 1
let eff_unsafe  : eff_id = 2
let eff_c       : eff_id = 3
let eff_rec     : eff_id = 4
let eff_case    : eff_id = 5

/// The first id available to a surface `effect` declaration. Named so that P03
/// does not have to track the block above by hand — `se_next_eff` was a literal
/// `2` that a fifth reserved effect would have silently invalidated.
let eff_user_base : eff_id = 6

/// `print` and `read`: ordinary operations of the ordinary effect `IO`. There is
/// no second mechanism, and "suppliable only by the compiler or interpreter to
/// the entry point" is entirely the id-ownership fact stated above.
let w_print : word_id = 13
let w_read  : word_id = 14

let w_show  : word_id = 15
let w_cat   : word_id = 16
let w_streq : word_id = 17
let w_parse : word_id = 18

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
  (w_show,  WPrim OShowI);
  (w_cat,   WPrim OCatS);
  (w_streq, WPrim OEqS);
  (w_parse, WPrim OParseI);
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
