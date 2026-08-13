module R02_Machine

open FStar.List.Tot
open FStar.Mul
open M01_Kinds
open M04_Effects
open M05_Terms
open R01_Runtime

(* ------------------------------------------------------------------------ *)
(* Reading an integer out of a string                                       *)
(* ------------------------------------------------------------------------ *)

/// `parse`'s implementation, and the inverse of `OShowI`.
///
/// IT EXISTS SO THAT STRING IO DOES NOT COST NUMERIC INPUT. `read` used to
/// return an `i64`; now it returns a `str`, and without this word there would be
/// no path from typed input back to a number at all (D-65).
///
/// MALFORMED INPUT YIELDS 0 rather than failing, which is the same concession
/// the `i64`-typed `read` already made and is documented as. The honest return
/// type is `( str -- option[i64] )`, and it becomes writable when sums have
/// surface syntax; until then a sentinel is preferable to a stuck machine,
/// because a stuck machine loses the REPL session.
///
/// Duplicates `E01_Lexer.int_of_run` in miniature, deliberately: P02 cannot
/// depend on P03, and a shared home for it would be a fourth project holding
/// ten lines. Worth revisiting if a second such function appears.
let digit_of (c:FStar.Char.char) : Tot int =
  if c = '0' then 0 else if c = '1' then 1 else if c = '2' then 2
  else if c = '3' then 3 else if c = '4' then 4 else if c = '5' then 5
  else if c = '6' then 6 else if c = '7' then 7 else if c = '8' then 8
  else if c = '9' then 9 else (-1)

let rec digits_of (acc:int) (cs:list FStar.Char.char)
  : Tot (option int) (decreases cs) =
  match cs with
  | []     -> Some acc
  | c :: r -> let d = digit_of c in
              if d < 0 then None else digits_of (acc * 10 + d) r

let parse_int (s:string) : Tot int =
  match FStar.String.list_of_string s with
  | []          -> 0
  | '-' :: rest -> (match rest with
                    | [] -> 0
                    | _  -> (match digits_of 0 rest with
                             | None   -> 0
                             | Some n -> 0 - n))
  | cs          -> (match digits_of 0 cs with
                    | None   -> 0
                    | Some n -> n)

let rec find_handler (k:kont) (e:eff_id) (op:op_id)
  : Tot (option (term & option rstack)) (decreases k) =
  match k with
  | [] -> None
  | KHandler e' impls st :: rest ->
    if e' = e then
      (match assoc op impls with
       | Some body -> Some (body, st)
       | None      -> find_handler rest e op)
    else find_handler rest e op
  | _ :: rest -> find_handler rest e op

/// Deliberately written as the mirror image of `find_handler`, clause for
/// clause, because the two must select the same frame.
let rec set_handler_state (k:kont) (e:eff_id) (op:op_id) (st:option rstack)
  : Tot kont (decreases k) =
  match k with
  | [] -> []
  | KHandler e' impls st' :: rest ->
    if e' = e then
      (match assoc op impls with
       | Some _ -> KHandler e' impls st :: rest
       | None   -> KHandler e' impls st' :: set_handler_state rest e op st)
    else KHandler e' impls st' :: set_handler_state rest e op st
  | f :: rest -> f :: set_handler_state rest e op st

let load (t:term) (s:rstack) : Tot mstate = { code = [KTerm t]; stk = s }

/// Read the value `n` slots below the top, without removing it.
let rec pick_at (n:nat) (s:rstack) : Tot (option rvalue) (decreases s) =
  match s with
  | []     -> None
  | v :: r -> if n = 0 then Some v else pick_at (n - 1) r

/// Remove the value `n` slots below the top, returning it and the remainder.
let rec roll_at (n:nat) (s:rstack) : Tot (option (rvalue & rstack)) (decreases s) =
  match s with
  | []     -> None
  | v :: r ->
    if n = 0 then Some (v, r)
    else (match roll_at (n - 1) r with
          | None          -> None
          | Some (t, r')  -> Some (t, v :: r'))

/// Apply a primitive. Arity and typing were settled by M06, so the
/// shape-failure branches here are unreachable for well-typed input; they
/// return `SStuck` rather than being omitted so that a violation is reported
/// instead of silently mis-executing.
let apply_prim (p:prim_word) (k:kont) (s:rstack) : Tot sresult =
  match p, s with
  | OAddI, RInt a :: RInt b :: r -> SNext ({ code = k; stk = RInt (b + a) :: r })
  | OSubI, RInt a :: RInt b :: r -> SNext ({ code = k; stk = RInt (b - a) :: r })
  | OMulI, RInt a :: RInt b :: r -> SNext ({ code = k; stk = RInt (b * a) :: r })
  | ODivI, RInt a :: RInt b :: r ->
    if a = 0 then SStuck "division by zero"
    else SNext ({ code = k; stk = RInt (b / a) :: r })
  | OModI, RInt a :: RInt b :: r ->
    if a = 0 then SStuck "modulo by zero"
    else SNext ({ code = k; stk = RInt (b % a) :: r })
  | OLtI,  RInt a :: RInt b :: r -> SNext ({ code = k; stk = RBool (b < a) :: r })
  | OLeI,  RInt a :: RInt b :: r -> SNext ({ code = k; stk = RBool (b <= a) :: r })
  | OEqI,  RInt a :: RInt b :: r -> SNext ({ code = k; stk = RBool (b = a) :: r })
  | ONot,  RBool a :: r          -> SNext ({ code = k; stk = RBool (not a) :: r })
  | OAnd,  RBool a :: RBool b :: r -> SNext ({ code = k; stk = RBool (b && a) :: r })
  | OOr,   RBool a :: RBool b :: r -> SNext ({ code = k; stk = RBool (b || a) :: r })
  /// Strings. `OCatS` and `OEqS` take their operands in stack order, so the
  /// DEEPER value comes first in the result: `"a" "b" cat` is `"ab"`, matching
  /// the convention every arithmetic case above already follows.
  | OShowI, RInt a :: r           -> SNext ({ code = k; stk = RStr (string_of_int a) :: r })
  | OCatS, RStr a :: RStr b :: r  -> SNext ({ code = k; stk = RStr (b ^ a) :: r })
  | OEqS,  RStr a :: RStr b :: r  -> SNext ({ code = k; stk = RBool (b = a) :: r })
  | OParseI, RStr a :: r          -> SNext ({ code = k; stk = RInt (parse_int a) :: r })
  | _ -> SStuck "primitive applied to ill-shaped stack"

/// Runtime image of a literal. Integer widths are erased -- M06 has already
/// checked them, so re-deriving them here would duplicate the type system to
/// no benefit.
let lit_value (l:lit) : Tot rvalue =
  match l with
  | LPrim PBool b -> RBool b
  | LPrim PUnit _ -> RUnit
  | LPrim PF32 _  -> RBits 0
  | LPrim PF64 _  -> RBits 0
  | LPrim PStr s  -> RStr s
  | LPrim _ v     -> RInt v

/// Every core intrinsic, in one table (D-55), mirroring `M06.prim_sig` row for
/// row. `Inl` is a stuck message and `Inr` the new stack.
///
/// It takes the stack and returns a stack, and takes neither the dictionary nor
/// the continuation. That signature is the runtime witness for `M05.prim_op`'s
/// purity invariant: a primitive cannot perform an operation, cannot call a
/// word, and cannot alter control flow, because it is not given anything with
/// which to do so. `M07`'s `prim_den` will be this same table over typed
/// stacks, and M09's agreement obligation for the whole primitive class is then
/// one lemma relating the two.
///
/// The shape-failure branches are unreachable for well-typed input -- M06 has
/// already settled arity and typing -- and return a message rather than being
/// omitted so that a violation is reported instead of silently mis-executing.
let apply_primop (p:prim_op) (s:rstack) : Tot (either string rstack) =
  match p with
  | PLit l -> Inr (lit_value l :: s)

  | PStack (SDup _) ->
    (match s with
     | v :: r -> Inr (v :: v :: r)
     | []     -> Inl "dup on empty stack")

  | PStack (SPop _) ->
    (match s with
     | _ :: r -> Inr r
     | []     -> Inl "pop on empty stack")

  | PStack (SSwap _ _) ->
    (match s with
     | a :: b :: r -> Inr (b :: a :: r)
     | _           -> Inl "swap needs two values")

  (* Deep access. The depth is `length above`, recovered from the segment the
     term carries, so neither case is variadic at runtime either. *)
  | PStack (SPick above _) ->
    (match pick_at (length above) s with
     | None   -> Inl "pick: stack too short"
     | Some v -> Inr (v :: s))

  | PStack (SRoll above _) ->
    (match roll_at (length above) s with
     | None           -> Inl "roll: stack too short"
     | Some (v, rest) -> Inr (v :: rest))

  | PPack n _ repr ->
    (match take (length repr) s with
     | None            -> Inl "pack: stack too short"
     | Some (vs, rest) -> Inr (RSeal n vs :: rest))

  | PUnpack _ _ _ ->
    (match s with
     | RSeal _ vs :: r -> Inr (give vs r)
     | _               -> Inl "unpack: not a sealed value")

  | PInj variants tag ->
    if tag >= length variants then Inl "inj: tag out of range"
    else (match take (length (index variants tag)) s with
          | None            -> Inl "inj: stack too short"
          | Some (vs, rest) -> Inr (RSum tag vs :: rest))

  (* D-33: `false` is tag 0 and `true` is tag 1, matching `M06.prim_sig` and
     `M01.bool_variants`. Neither variant carries a payload, so the coerced
     value is a bare tag. *)
  | PBoolSum ->
    (match s with
     | RBool b :: r -> Inr (RSum (if b then 1 else 0) [] :: r)
     | _            -> Inl "bool>sum: not a boolean")

  | PBoxNew _ ->
    (match s with
     | v :: r -> Inr (RBox v :: r)
     | []     -> Inl "box: stack empty")

  | PBoxOpen _ ->
    (match s with
     | RBox v :: r -> Inr (v :: r)
     | _           -> Inl "unbox: not a box")

  | PRcNew _ ->
    (match s with
     | v :: r -> Inr (RRc v :: r)
     | []     -> Inl "rc new: stack empty")

  (* `PRcClone` models no refcount: R01_Runtime.fsti explains why nesting
     already stands in for sharing here (the count only gates when a
     destructor runs, and this interpreter has no observable deallocation).
     So cloning just duplicates the nested value, same as `dup` would. *)
  | PRcClone _ ->
    (match s with
     | RRc v :: r -> Inr (RRc v :: RRc v :: r)
     | _          -> Inl "rc clone: not an rc")

  | PRcDrop _ ->
    (match s with
     | RRc _ :: r -> Inr r
     | _          -> Inl "rc drop: not an rc")

  | PRcRead _ ->
    (match s with
     | RRc v :: r -> Inr (v :: RRc v :: r)
     | _          -> Inl "rc read: not an rc")

  (* Roll/unroll cross a `TName` boundary at the type level only; R01 has no
     `RName`, so both are runtime no-ops (M01_Kinds header, R01_Runtime.fsti). *)
  | PRoll _ _   -> Inr s
  | PUnroll _ _ -> Inr s

let step (d:rdict) (s:mstate) : Tot sresult =
  match s.code with
  | [] -> SDone s.stk

  (* A handler whose body has completed: pop the boundary and hand the final
     state back to the program. The handler IS the object, so the object
     outlives the block -- see `M05.THandle`. *)
  | KHandler _ _ (Some st) :: k -> SNext ({ code = k; stk = give st s.stk })
  | KHandler _ _ None :: k ->
    SStuck "handle: the handler's state was never given back"

  (* The initialiser has finished; move its results into a fresh frame. *)
  | KInit e n impls body :: k ->
    (match take n s.stk with
     | None -> SStuck "handle: the initialiser did not produce the state"
     | Some (st0, rest) ->
       SNext ({ code = KTerm body :: KHandler e impls (Some st0) :: k;
                stk = rest }))

  (* An implementation has finished; take the state back off the top and
     return it to the frame that lent it. *)
  | KRestore e op n :: k ->
    (match take n s.stk with
     | None -> SStuck "handler: the implementation did not return its state"
     | Some (st', rest) ->
       SNext ({ code = set_handler_state k e op (Some st'); stk = rest }))

  | KTerm t :: k ->
    match t with
    | TNil -> SNext ({ code = k; stk = s.stk })

    (* Juxtaposition flattens. Sound because composition is associative (M03),
       which is exactly why M08 made the continuation a list. *)
    | TSeq a b -> SNext ({ code = KTerm a :: KTerm b :: k; stk = s.stk })

    (* Every intrinsic, in one case. `apply_primop` is a pure function of the
       stack alone -- it consults neither the dictionary nor the continuation,
       which is the runtime shadow of `M05.prim_op`'s purity invariant, and the
       reason this case can be lifted out of `step` at all. *)
    | TPrimOp p ->
      (match apply_primop p s.stk with
       | Inl msg  -> SStuck msg
       | Inr stk' -> SNext ({ code = k; stk = stk' }))

    | TWord w ->
      (match dict_lookup d w with
       | None -> SStuck "unbound word"
       | Some (WDef body) -> SNext ({ code = KTerm body :: k; stk = s.stk })
       | Some (WPrim p)   -> apply_prim p k s.stk
       | Some (WOp e)     ->
         (* Dictionary lookup at runtime: walk the handler chain outward.
            The implementation runs with the handler still installed, so
            operations it performs itself reach the same handler -- reentrant
            (D03 2), and reentrant WITHOUT capturing anything (D-36).

            The state is lent to the implementation by pushing it on top of
            the operation's arguments and blanking the frame; `KRestore` takes
            it back. Pushing on TOP is forced: splicing it underneath would
            need the operation's arity, which the dictionary does not record. *)
         (match find_handler k e w with
          | None -> SEffect w s.stk k
          | Some (_, None) ->
            (* The frame is mid-call. Serving a stale copy would silently fork
               the state, so this is reported instead. See the note in
               `R02_Machine.fsti`; it is the aliasing rule a linear language
               ought to enforce statically, and does not yet. *)
            SStuck "handler re-entered while its own state is in use"
          | Some (body, Some hst) ->
            SNext ({ code = KTerm body :: KRestore e w (length hst)
                           :: set_handler_state k e w None;
                     stk = give hst s.stk })))

    | TCase _ branches ->
      (match s.stk with
       | RSum tag vs :: r ->
         if tag >= length branches then SStuck "case: tag out of range"
         else SNext ({ code = KTerm (index branches tag) :: k; stk = give vs r })
       | _ -> SStuck "case: not a sum value")

    (* Two steps, because the state has to be computed before the frame that
       holds it can exist: run `init`, then `KInit` moves its results in. *)
    | THandle e st init impls body ->
      SNext ({ code = KTerm init :: KInit e (length st) impls body :: k;
               stk = s.stk })

    (* Specialization is semantics-preserving (M11 E2), so the reference
       interpreter may ignore it and run the body directly. This is not a
       shortcut: it is the statement of E2, and the interpreter is where that
       statement gets its first empirical test -- comparing a run of
       `TSpecialize t` against a run of `specialize t` must agree. *)
    | TSpecialize body -> SNext ({ code = KTerm body :: k; stk = s.stk })
