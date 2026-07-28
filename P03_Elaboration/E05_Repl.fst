module E05_Repl

/// P03, module 05: the REPL session.
///
/// SUMMARY
///   Ties the whole pipeline together for one line of input:
///
///     source -> E01 lex -> E03 parse -> E04 elaborate
///            -> M06 typecheck -> R02/R05 evaluate -> rendered stack
///
///   The session carries the pieces that persist between lines: the name
///   environment, the runtime dictionary, the value stack, and — crucially —
///   the stack's *static shape*, so the next line can be typechecked against
///   what is actually sitting there.
///
/// WHY A SHAPE, NOT JUST A STACK
///   A REPL line is a program fragment, and M06 types fragments
///   row-polymorphically: `infer` returns what the fragment consumes and
///   produces, not an absolute stack type. Keeping the shape lets the session
///   check that a line's inputs actually match the live stack, and report a
///   real error instead of getting stuck at runtime.
///
/// KNOWN SUBSET VIOLATION
///   `mk_wenv` builds `M06_Typing.wenv`, whose fields are FUNCTIONS
///   (`w_sig : word_id -> srow`). Constructing one requires a closure, which
///   breaks P02's first-order discipline (D-20) and therefore blocks
///   catcat-extraction of this module. The same is true of `M04.sig_env`.
///   Fixing it means changing those records to association lists in P01.
///   Recorded in N02 rather than papered over: the OCaml build is unaffected,
///   so nothing here fails today.

open FStar.List.Tot
open M01_Kinds
open M03_Signatures
open M04_Effects
open M05_Terms
open M06_Typing
open R01_Runtime
open R02_Machine
open R03_Prelude
open R05_Driver
open E02_Ast
open E03_Parser
open E04_Elaborate

(* ------------------------------------------------------------------------ *)
(* Rendering types (diagnostics)                                            *)
(* ------------------------------------------------------------------------ *)

let render_prim (p:prim) : Tot string =
  match p with
  | PI8 -> "i8"     | PI16 -> "i16"   | PI32 -> "i32"   | PI64 -> "i64"
  | PU8 -> "u8"     | PU16 -> "u16"   | PU32 -> "u32"   | PU64 -> "u64"
  | PF32 -> "f32"   | PF64 -> "f64"
  | PBool -> "bool" | PUnit -> "unit"

let rec render_ty (d:dtype) : Tot string (decreases (dtype_size d)) =
  match d with
  | TPrim p      -> render_prim p
  | TName n      -> "@" ^ string_of_int n
  | TBox u       -> "Box[" ^ render_ty u ^ "]"
  | TRc u        -> "Rc[" ^ render_ty u ^ "]"
  | TSeal n _ _  -> "<" ^ string_of_int n ^ ">"
  | TSum _       -> "sum"

/// Rendered bottom-to-top, matching the surface convention: a core list is
/// top-first, so it is reversed on the way out.
let rec render_tys (ds:list dtype) : Tot string (decreases ds) =
  match ds with
  | []      -> ""
  | d :: [] -> render_ty d
  | d :: r  -> render_ty d ^ " " ^ render_tys r

let render_row (s:srow) : Tot string =
  "( " ^ render_tys (rev s.pre) ^ " -- " ^ render_tys (rev s.post) ^ " )"

(* ------------------------------------------------------------------------ *)
(* Session state                                                            *)
(* ------------------------------------------------------------------------ *)

noeq type session = {
  se_nenv  : nenv;
  /// Backing table for `mk_wenv`.
  se_defs  : list (word_id & srow);
  se_dict  : rdict;
  se_next  : word_id;
  se_stack : rstack;
  /// Static shape of `se_stack`, top-first.
  se_shape : list dtype;
}

let i64_t : dtype = TPrim PI64
let bool_t : dtype = TPrim PBool

let bin_i64 : srow = { pre = [i64_t; i64_t]; post = [i64_t] }
let cmp_i64 : srow = { pre = [i64_t; i64_t]; post = [bool_t] }
let un_bool : srow = { pre = [bool_t]; post = [bool_t] }
let bin_bool : srow = { pre = [bool_t; bool_t]; post = [bool_t] }
let push_bool : srow = { pre = []; post = [bool_t] }

/// Word names are free-form: any run of non-space, non-bracket characters. So
/// the arithmetic and comparison words are spelled as operators (D-31), which
/// is what D-16 was always asking for — `add` and `mul` were placeholders from
/// before the lexer existed, not a naming decision.
///
/// `-` is a word while `-3` is a literal, because `int_of_run` requires at
/// least one digit after the sign. `!=` is deliberately absent: `!` is the
/// effect sigil, so it cannot begin a word.
let prelude_nenv : nenv = [
  { n_name = "+";   n_id = w_add; n_sig = bin_i64 };
  { n_name = "-";   n_id = w_sub; n_sig = bin_i64 };
  { n_name = "*";   n_id = w_mul; n_sig = bin_i64 };
  { n_name = "/";   n_id = w_div; n_sig = bin_i64 };
  { n_name = "%";   n_id = w_mod; n_sig = bin_i64 };
  { n_name = "<";   n_id = w_lt;  n_sig = cmp_i64 };
  { n_name = "<=";  n_id = w_le;  n_sig = cmp_i64 };
  { n_name = "=";   n_id = w_eq;  n_sig = cmp_i64 };
  { n_name = "not"; n_id = w_not; n_sig = un_bool };
  { n_name = "and"; n_id = w_and; n_sig = bin_bool };
  { n_name = "or";  n_id = w_or;  n_sig = bin_bool };
  { n_name = "true";  n_id = w_true;  n_sig = push_bool };
  { n_name = "false"; n_id = w_false; n_sig = push_bool };
]

let rec nenv_defs (e:nenv) : Tot (list (word_id & srow)) (decreases e) =
  match e with
  | []     -> []
  | n :: r -> (n.n_id, n.n_sig) :: nenv_defs r

let init_session : session = {
  se_nenv  = prelude_nenv;
  se_defs  = nenv_defs prelude_nenv;
  se_dict  = prelude;
  se_next  = w_user_base;
  se_stack = [];
  se_shape = [];
}

/// See the KNOWN SUBSET VIOLATION note in the header: these closures are the
/// only ones in P03.
let mk_wenv (defs:list (word_id & srow)) : Tot wenv = {
  w_sig = (fun w -> match assoc w defs with Some s -> s | None -> sid);
  w_eff = (fun _ -> pure_row);
  w_ops = { op_of  = (fun _ -> { op_pre = []; op_post = [] });
            eff_of = (fun _ -> 0) };
}

(* ------------------------------------------------------------------------ *)
(* Shape checking                                                           *)
(* ------------------------------------------------------------------------ *)

/// Does the live stack supply what this fragment consumes? Returns what is
/// left beneath.
let rec strip_prefix (p:list dtype) (l:list dtype)
  : Tot (option (list dtype)) (decreases p) =
  match p, l with
  | [], _            -> Some l
  | _, []            -> None
  | a :: pr, b :: lr -> if a = b then strip_prefix pr lr else None

(* ------------------------------------------------------------------------ *)
(* Evaluating one declaration                                               *)
(* ------------------------------------------------------------------------ *)

let fuel : nat = 1000000

/// Typecheck an elaborated definition with M06 and, if it agrees, install it.
///
/// `declared` is `Some row` when the user wrote a signature and `None` when it
/// was inferred. In the written case a disagreement is the user's error; in the
/// inferred case it would be a bug in `infer_sig`, so the message says so
/// rather than blaming the program.
let install_def (s:session) (name:string) (declared:option srow) (row:srow) (t:term)
  : Tot (session & string) =
  let env = mk_wenv s.se_defs in
  match infer env t with
  | None -> (s, "error: " ^ name ^ " does not typecheck")
  | Some (got, _) ->
    if got <> row
    then (match declared with
          | Some _ -> (s, "error: " ^ name ^ " declares " ^ render_row row
                          ^ " but its body has " ^ render_row got)
          | None   -> (s, "internal error: inferred " ^ render_row row
                          ^ " for " ^ name ^ " but M06 says " ^ render_row got))
    else
      let id = s.se_next in
      let s' = { s with
        se_nenv = ({ n_name = name; n_id = id; n_sig = row }) :: s.se_nenv;
        se_defs = (id, row) :: s.se_defs;
        se_dict = dict_extend s.se_dict id (WDef t);
        se_next = id + 1 } in
      (s', "defined " ^ name ^ " " ^ render_row row)

let eval_decl (s:session) (d:sdecl) : Tot (session & string) =
  match d with

  | SdDefine name sg body ->
    (match elab_define s.se_nenv sg body with
     | Inl e         -> (s, "error: " ^ e)
     | Inr (row, t)  -> install_def s name (Some row) row t)

  /// The inferred form prints the signature it worked out, which is the same
  /// text a language server would show inline (D01's tooling goal, N02 Q-11).
  | SdDefineInfer name body ->
    (match elab_define_infer s.se_nenv body with
     | Inl e         -> (s, "error: " ^ e)
     | Inr (row, t)  -> install_def s name None row t)

  | SdExpr body ->
    (match elab_expr s.se_nenv s.se_shape body with
     | Inl e -> (s, "error: " ^ e)
     | Inr t ->
       let env = mk_wenv s.se_defs in
       (match infer env t with
        | None -> (s, "error: expression does not typecheck")
        | Some (row, _) ->
          (match strip_prefix row.pre s.se_shape with
           | None ->
             (s, "error: this needs " ^ render_tys (rev row.pre)
                 ^ " on the stack, but the stack holds "
                 ^ render_tys (rev s.se_shape))
           | Some below ->
             (match eval s.se_dict fuel t s.se_stack with
              | RDone stk ->
                let s' = { s with se_stack = stk;
                                  se_shape = row.post @ below } in
                (s', "ok  " ^ render_stack stk)
              | REffect op _  -> (s, "unhandled effect #" ^ string_of_int op)
              | RStuck m      -> (s, "STUCK: " ^ m)
              | ROutOfFuel    -> (s, "out of fuel")))))

let rec eval_decls (s:session) (ds:list sdecl) (acc:string)
  : Tot (session & string) (decreases ds) =
  match ds with
  | []     -> (s, acc)
  | d :: r ->
    let (s', msg) = eval_decl s d in
    eval_decls s' r (if acc = "" then msg else acc ^ "\n" ^ msg)

(* ------------------------------------------------------------------------ *)
(* Entry point                                                              *)
(* ------------------------------------------------------------------------ *)

/// Evaluate one line of source, returning the updated session and what to
/// print. A parse or type error leaves the session untouched, which is what
/// makes the REPL safe to type into.
let eval_line (s:session) (src:string) : Tot (session & string) =
  match parse src with
  | Inl e   -> (s, "error: " ^ e)
  | Inr ds  -> eval_decls s ds ""

/// The current stack, rendered bottom-to-top.
let show_stack (s:session) : Tot string = render_stack s.se_stack
