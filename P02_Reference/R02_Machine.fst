module R02_Machine

open FStar.List.Tot
open FStar.Mul
open M01_Kinds
open M04_Effects
open M05_Terms
open R01_Runtime

let rec find_handler (k:kont) (e:eff_id) (op:op_id)
  : Tot (option (term & kont)) (decreases k) =
  match k with
  | [] -> None
  | KHandler e' impls :: rest ->
    if e' = e then
      (match assoc op impls with
       | Some body -> Some (body, rest)
       | None      -> find_handler rest e op)
    else find_handler rest e op
  | KTerm _ :: rest -> find_handler rest e op

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
let apply_prim (p:prim_op) (k:kont) (s:rstack) : Tot sresult =
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
  | LPrim _ v     -> RInt v

let step (d:rdict) (s:mstate) : Tot sresult =
  match s.code with
  | [] -> SDone s.stk

  (* A handler whose body has completed: pop the boundary. *)
  | KHandler _ _ :: k -> SNext ({ code = k; stk = s.stk })

  | KTerm t :: k ->
    match t with
    | TNil -> SNext ({ code = k; stk = s.stk })

    (* Juxtaposition flattens. Sound because composition is associative (M03),
       which is exactly why M08 made the continuation a list. *)
    | TSeq a b -> SNext ({ code = KTerm a :: KTerm b :: k; stk = s.stk })

    | TLit l -> SNext ({ code = k; stk = lit_value l :: s.stk })

    | TStack (SDup _) ->
      (match s.stk with
       | v :: r -> SNext ({ code = k; stk = v :: v :: r })
       | []     -> SStuck "dup on empty stack")

    | TStack (SPop _) ->
      (match s.stk with
       | _ :: r -> SNext ({ code = k; stk = r })
       | []     -> SStuck "pop on empty stack")

    | TStack (SSwap _ _) ->
      (match s.stk with
       | a :: b :: r -> SNext ({ code = k; stk = b :: a :: r })
       | _           -> SStuck "swap needs two values")

    (* Deep access. The depth is `length above`, recovered from the segment the
       term carries, so neither case is variadic at runtime either. *)
    | TStack (SPick above _) ->
      (match pick_at (length above) s.stk with
       | None   -> SStuck "pick: stack too short"
       | Some v -> SNext ({ code = k; stk = v :: s.stk }))

    | TStack (SRoll above _) ->
      (match roll_at (length above) s.stk with
       | None            -> SStuck "roll: stack too short"
       | Some (v, rest)  -> SNext ({ code = k; stk = v :: rest }))

    | TWord w ->
      (match dict_lookup d w with
       | None -> SStuck "unbound word"
       | Some (WDef body) -> SNext ({ code = KTerm body :: k; stk = s.stk })
       | Some (WPrim p)   -> apply_prim p k s.stk
       | Some (WOp e)     ->
         (* Dictionary lookup at runtime: walk the handler chain outward.
            The implementation runs with the handler still installed, so
            operations it performs itself reach the same handler -- deep,
            hence reentrant (D03 2). *)
         (match find_handler k e w with
          | Some (body, _) -> SNext ({ code = KTerm body :: k; stk = s.stk })
          | None           -> SEffect w s.stk k))

    | TPack n _ repr ->
      (match take (length repr) s.stk with
       | None            -> SStuck "pack: stack too short"
       | Some (vs, rest) -> SNext ({ code = k; stk = RSeal n vs :: rest }))

    | TUnpack _ _ _ ->
      (match s.stk with
       | RSeal _ vs :: r -> SNext ({ code = k; stk = give vs r })
       | _               -> SStuck "unpack: not a sealed value")

    | TInj variants tag ->
      if tag >= length variants then SStuck "inj: tag out of range"
      else (match take (length (index variants tag)) s.stk with
            | None            -> SStuck "inj: stack too short"
            | Some (vs, rest) -> SNext ({ code = k; stk = RSum tag vs :: rest }))

    | TCase _ branches ->
      (match s.stk with
       | RSum tag vs :: r ->
         if tag >= length branches then SStuck "case: tag out of range"
         else SNext ({ code = KTerm (index branches tag) :: k; stk = give vs r })
       | _ -> SStuck "case: not a sum value")

    | THandle e impls body ->
      SNext ({ code = KTerm body :: KHandler e impls :: k; stk = s.stk })

    (* Specialization is semantics-preserving (M11 E2), so the reference
       interpreter may ignore it and run the body directly. This is not a
       shortcut: it is the statement of E2, and the interpreter is where that
       statement gets its first empirical test -- comparing a run of
       `TSpecialize t` against a run of `specialize t` must agree. *)
    | TSpecialize body -> SNext ({ code = KTerm body :: k; stk = s.stk })

    | TBoxNew _ ->
      (match s.stk with
       | v :: r -> SNext ({ code = k; stk = RBox v :: r })
       | []     -> SStuck "box: stack empty")

    | TBoxOpen _ ->
      (match s.stk with
       | RBox v :: r -> SNext ({ code = k; stk = v :: r })
       | _           -> SStuck "unbox: not a box")

    | TRcNew _ ->
      (match s.stk with
       | v :: r -> SNext ({ code = k; stk = RRc v :: r })
       | []     -> SStuck "rc new: stack empty")

    (* `TRcClone` models no refcount: R01_Runtime.fsti explains why nesting
       already stands in for sharing here (the count only gates when a
       destructor runs, and this interpreter has no observable deallocation).
       So cloning just duplicates the nested value, same as `dup` would. *)
    | TRcClone _ ->
      (match s.stk with
       | RRc v :: r -> SNext ({ code = k; stk = RRc v :: RRc v :: r })
       | _          -> SStuck "rc clone: not an rc")

    | TRcDrop _ ->
      (match s.stk with
       | RRc _ :: r -> SNext ({ code = k; stk = r })
       | _          -> SStuck "rc drop: not an rc")

    | TRcRead _ ->
      (match s.stk with
       | RRc v :: r -> SNext ({ code = k; stk = v :: RRc v :: r })
       | _          -> SStuck "rc read: not an rc")

    (* Roll/unroll cross a `TName` boundary at the type level only; R01 has no
       `RName`, so both are runtime no-ops (M01_Kinds header, R01_Runtime.fsti). *)
    | TRoll _ _ -> SNext ({ code = k; stk = s.stk })

    | TUnroll _ _ -> SNext ({ code = k; stk = s.stk })
