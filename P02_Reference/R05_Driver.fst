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
       | SEffect op stk k -> REffect op stk k
       | SStuck msg       -> RStuck msg

let eval (d:rdict) (fuel:nat) (t:term) (init:rstack) : Tot rresult =
  run d fuel (load t init)

/// Re-enter the machine at a saved continuation. One line, because that is all
/// it is: the interpreter's state was never destroyed, only handed out.
let resume (d:rdict) (fuel:nat) (k:kont) (stk:rstack) : Tot rresult =
  run d fuel ({ code = k; stk = stk })

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
  /// Quoted, so a string on the stack is distinguishable from a bare word in
  /// the REPL echo. There is no escaping on the way out: this is a diagnostic
  /// renderer, and `print` is what emits a string as itself.
  | RStr s      -> "\"" ^ s ^ "\""
  /// A payload is a stack SEGMENT, so it prints by the same rule the stack
  /// does: bottom-to-top, `rev` on the way out. Head-first would show a
  /// two-field seal in the opposite order to the `( … )` that declared it,
  /// which is a rendering that quietly contradicts the source.
  | RSeal n vs  -> "<" ^ string_of_int n ^ ":" ^ render_seg vs ^ ">"
  | RSum tag vs -> "#" ^ string_of_int tag ^ "(" ^ render_seg vs ^ ")"
  | RBox v      -> "box(" ^ render_value v ^ ")"
  | RRc v       -> "rc(" ^ render_value v ^ ")"

and render_list (vs:list rvalue) : Tot string =
  match vs with
  | []      -> ""
  | v :: [] -> render_value v
  | v :: r  -> render_value v ^ " " ^ render_list r

/// The same list read the other way. Written out rather than `render_list (rev
/// vs)` so the recursion stays structural: `rev` preserves length, not
/// subterm-hood, and this module has no measure to spend on proving that.
and render_seg (vs:list rvalue) : Tot string =
  match vs with
  | []      -> ""
  | v :: [] -> render_value v
  | v :: r  -> render_seg r ^ " " ^ render_value v

/// Rendered bottom-to-top, matching the surface convention of D05 2: the top
/// of the stack prints on the right, as a Forth programmer expects.
let render_stack (s:rstack) : Tot string =
  match s with
  | [] -> "(empty)"
  | _  -> render_list (rev s)

let render_result (r:rresult) : Tot string =
  match r with
  | RDone stk        -> "ok  " ^ render_stack stk
  | REffect op stk _ -> "eff #" ^ string_of_int op ^ "  " ^ render_stack stk
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
    TPrimOp (PPack counter_nom [] counter_repr);          // seal: 41 becomes a Counter
    TPrimOp (PUnpack counter_nom [] counter_repr);        // enter the class body
    int_lit 1; TWord w_add;                     // increment
    TPrimOp (PPack counter_nom [] counter_repr)           // re-seal
  ]

/// `option i64`: variant 0 empty, variant 1 carrying an i64.
let opt_variants : list seg = [[]; [TPrim PI64]]

let eff_opt : eff_id = 2
let op_none : op_id  = 201
let op_some : op_id  = 202

/// ELIMINATION IS A HANDLER (D-68). The dispatch performs the operation the
/// tag selects; the two branches are its implementations. Note that they are
/// NOT at the same signature -- `None` pushes a zero and `Some` consumes the
/// payload -- and both are accepted because each is framed to the joined
/// declaration `( -- i64 )` by `M06.impl_frame`.
let ex_sum : term =
  cat [
    int_lit 99;
    TPrimOp (PInj opt_variants 1);                        // Some 99
    THandle eff_opt [] TNil
      [ (op_none, int_lit 0)                              // None   -> 0
      ; (op_some, TNil) ]                                 // Some x -> x
      (TDispatch [op_none; op_some] opt_variants)
  ]

/// Effect 1, operation 200: "ask", pushing a number the handler chooses.
let eff_ask : eff_id = 1
let op_ask  : op_id  = 200

let demo_dict : rdict =
  dict_extend (dict_extend (dict_extend prelude op_ask (WOp eff_ask))
                           op_none (WOp eff_opt))
              op_some (WOp eff_opt)

/// A STATELESS handler: `st = []`, so the initialiser is `TNil` and the
/// implementation is typed at the operation's own signature. The degenerate
/// case needs no special rule anywhere.
let ex_handled : term =
  THandle eff_ask [] TNil [(op_ask, int_lit 5)]
    (cat [TWord op_ask; int_lit 10; TWord w_mul])

/// A STATEFUL handler, which is the shape D-36 is about: `ask` returns the
/// running count and leaves the count incremented, and nothing captures a
/// continuation to do it.
///
/// The implementation is `( state -- result state )` in surface order, so with
/// the state on top: `dup 1 +` takes `[s]` to `[s+1; s]` -- new state on top,
/// the returned value beneath. Reading it as a method on an object, the state
/// is the receiver and it is pushed last.
///
/// `ask ask +` therefore evaluates `0 + 1 = 1`, and the final state `2` is left
/// beneath it when the handler exits.
let ex_stateful : term =
  THandle eff_ask [TPrim PI64] (int_lit 0)
    [(op_ask, cat [TPrimOp (PStack (SDup (TPrim PI64))); int_lit 1; TWord w_add])]
    (cat [TWord op_ask; TWord op_ask; TWord w_add])

let ex_unhandled : term =
  cat [int_lit 1; TWord op_ask]

/// ABORTING (D-71). Two `try` blocks: the first pushes 7 and then performs
/// `fail`, so the 7 is discarded along with the rest of the block and `catch`
/// runs on the stack the frame saved; the second never aborts and is invisible.
///
/// What this exercises that no other example does is a frame that DISCARDS
/// continuation frames rather than returning through them. `R02.find_try` takes
/// the tail of the continuation at the `KTry`, so everything between the abort
/// and the boundary is dropped -- and nothing is stored, which is why D-36
/// survives it.
let ex_try : term =
  cat [
    TTry eff_fail [] (cat [int_lit 7; TWord w_fail]) (int_lit 42);
    TTry eff_fail [] (int_lit 5) (int_lit 0)
  ]

/// `List[i64]`: variant 0 is `Nil`; variant 1 is `Cons`, carrying an `i64` on
/// top of a `Box` of the tail. This is the type the project previously could
/// not express at all -- `dtype` was a finite tree, so nothing could refer to
/// itself. The recursion is legal only because it passes through `TBox`:
/// `TName list_nom` is an incomplete-type leaf, boxing it is what keeps
/// `dtype` values finite (M01's `wf_dtype`), and `PRoll`/`PUnroll` are the
/// explicit crossings of that boundary.
let list_nom : nom_id = 42
let list_variants : list seg = [ []; [TPrim PI64; TBox (TName list_nom)] ]
let list_body : dtype = TSum list_variants

/// Builds `[7, 9]` from the inside out: `Nil`, then box and roll it into the
/// tail of `Cons 9`, then box and roll THAT into the tail of `Cons 7`.
let ex_list : term =
  cat [
    TPrimOp (PInj list_variants 0);                       // Nil
    TPrimOp (PRoll list_nom list_body);
    TPrimOp (PBoxNew (TName list_nom));
    int_lit 9;
    TPrimOp (PInj list_variants 1);                       // Cons 9 (box Nil)
    TPrimOp (PRoll list_nom list_body);
    TPrimOp (PBoxNew (TName list_nom));
    int_lit 7;
    TPrimOp (PInj list_variants 1)                        // Cons 7 (box (Cons 9 (box Nil)))
  ]

let examples : list (string & term) = [
  ("arith",     ex_arith);
  ("counter",   ex_counter);
  ("sum",       ex_sum);
  ("handled",   ex_handled);
  ("stateful",  ex_stateful);
  ("unhandled", ex_unhandled);
  ("try",       ex_try);
  ("list",      ex_list);
]
