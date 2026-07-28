module R05_Driver

open FStar.List.Tot
open M01_Kinds
open M04_Effects
open M05_Terms
open R01_Runtime
open R02_Machine
open R03_Prelude

let rec run (d:rdict) (fuel:nat) (s:mstate) : Tot rresult (decreases fuel) =
  if fuel = 0 then ROutOfFuel
  else match step d s with
       | SNext s'         -> run d (fuel - 1) s'
       | SDone stk        -> RDone stk
       | SEffect op stk _ -> REffect op stk
       | SStuck msg       -> RStuck msg

let eval (d:rdict) (fuel:nat) (t:term) (init:rstack) : Tot rresult =
  run d fuel (load t init)

let eval_prelude (fuel:nat) (t:term) : Tot rresult =
  eval prelude fuel t []

(* ------------------------------------------------------------------------ *)
(* Rendering                                                                *)
(* ------------------------------------------------------------------------ *)

let rec render_value (v:rvalue) : Tot string =
  match v with
  | RInt n      -> string_of_int n
  | RBool true  -> "true"
  | RBool false -> "false"
  | RUnit       -> "unit"
  | RBits n     -> "bits:" ^ string_of_int n
  | RSeal n vs  -> "<" ^ string_of_int n ^ ":" ^ render_list vs ^ ">"
  | RSum tag vs -> "#" ^ string_of_int tag ^ "(" ^ render_list vs ^ ")"
  | RBox v      -> "box(" ^ render_value v ^ ")"
  | RRc v       -> "rc(" ^ render_value v ^ ")"

and render_list (vs:list rvalue) : Tot string =
  match vs with
  | []      -> ""
  | v :: [] -> render_value v
  | v :: r  -> render_value v ^ " " ^ render_list r

/// Rendered bottom-to-top, matching the surface convention of D05 2: the top
/// of the stack prints on the right, as a Forth programmer expects.
let render_stack (s:rstack) : Tot string =
  match s with
  | [] -> "(empty)"
  | _  -> render_list (rev s)

let render_result (r:rresult) : Tot string =
  match r with
  | RDone stk        -> "ok  " ^ render_stack stk
  | REffect op stk   -> "eff #" ^ string_of_int op ^ "  " ^ render_stack stk
  | RStuck msg       -> "STUCK: " ^ msg
  | ROutOfFuel       -> "out of fuel"

(* ------------------------------------------------------------------------ *)
(* Examples                                                                 *)
(* ------------------------------------------------------------------------ *)

let ex_arith : term =
  cat [int_lit 2; int_lit 3; TWord w_add; int_lit 4; TWord w_mul]

/// Nominal id 7, no capabilities declared -- a linear counter in the sense of
/// D03 5. The interpreter does not enforce that; M06 does.
let counter_nom : nom_id = 7
let counter_repr : seg = [TPrim PI64]

let ex_counter : term =
  cat [
    int_lit 41;
    TPack counter_nom [] counter_repr;          // seal: 41 becomes a Counter
    TUnpack counter_nom [] counter_repr;        // enter the class body
    int_lit 1; TWord w_add;                     // increment
    TPack counter_nom [] counter_repr           // re-seal
  ]

/// `option i64`: variant 0 empty, variant 1 carrying an i64.
let opt_variants : list seg = [[]; [TPrim PI64]]

let ex_sum : term =
  cat [
    int_lit 99;
    TInj opt_variants 1;                        // Some 99
    TCase opt_variants [ int_lit 0              // None  -> 0
                       ; TNil ]                 // Some x -> x
  ]

/// Effect 1, operation 200: "ask", pushing a number the handler chooses.
let eff_ask : eff_id = 1
let op_ask  : op_id  = 200

let demo_dict : rdict = dict_extend prelude op_ask (WOp eff_ask)

let ex_handled : term =
  THandle eff_ask [(op_ask, int_lit 5)]
    (cat [TWord op_ask; int_lit 10; TWord w_mul])

let ex_unhandled : term =
  cat [int_lit 1; TWord op_ask]

/// `List[i64]`: variant 0 is `Nil`; variant 1 is `Cons`, carrying an `i64` on
/// top of a `Box` of the tail. This is the type the project previously could
/// not express at all -- `dtype` was a finite tree, so nothing could refer to
/// itself. The recursion is legal only because it passes through `TBox`:
/// `TName list_nom` is an incomplete-type leaf, boxing it is what keeps
/// `dtype` values finite (M01's `wf_dtype`), and `TRoll`/`TUnroll` are the
/// explicit crossings of that boundary.
let list_nom : nom_id = 42
let list_variants : list seg = [ []; [TPrim PI64; TBox (TName list_nom)] ]
let list_body : dtype = TSum list_variants

/// Builds `[7, 9]` from the inside out: `Nil`, then box and roll it into the
/// tail of `Cons 9`, then box and roll THAT into the tail of `Cons 7`.
let ex_list : term =
  cat [
    TInj list_variants 0;                       // Nil
    TRoll list_nom list_body;
    TBoxNew (TName list_nom);
    int_lit 9;
    TInj list_variants 1;                       // Cons 9 (box Nil)
    TRoll list_nom list_body;
    TBoxNew (TName list_nom);
    int_lit 7;
    TInj list_variants 1                        // Cons 7 (box (Cons 9 (box Nil)))
  ]

let examples : list (string & term) = [
  ("arith",     ex_arith);
  ("counter",   ex_counter);
  ("sum",       ex_sum);
  ("handled",   ex_handled);
  ("unhandled", ex_unhandled);
  ("list",      ex_list);
]
