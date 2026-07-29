module E06_Repl

/// P03, module 06: the REPL session.
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
/// FIRST-ORDER THROUGHOUT
///   `mk_wenv` used to build a `wenv` out of closures, because `wenv`'s fields
///   were functions. That was P03's only violation of the first-order subset
///   (D-20) and it blocked catcat-extraction of this module. M04 and M06 now
///   hold association lists (D-45), so the session simply hands over the tables
///   it was already keeping — and the fake operation table, which returned a
///   nullary signature for every id, is gone with it.

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
open E05_Locate

(* ------------------------------------------------------------------------ *)
(* Session state                                                            *)
(* ------------------------------------------------------------------------ *)

noeq type session = {
  se_nenv  : nenv;
  /// What M06 checks against. Carried directly now that it is a pair of
  /// tables rather than a bundle of closures; `install_def` conses onto it.
  se_wenv  : wenv;
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

/// Every prelude word is pure, so the effect row is `pure_row` throughout.
/// That stops being true at the first `effect` declaration.
let rec nenv_decls (e:nenv) : Tot (list (word_id & wdecl)) (decreases e) =
  match e with
  | []     -> []
  | n :: r -> (n.n_id, { wd_sig = n.n_sig; wd_eff = pure_row }) :: nenv_decls r

let init_session : session = {
  se_nenv  = prelude_nenv;
  se_wenv  = { w_defs = nenv_decls prelude_nenv; w_ops = empty_sig_env };
  se_dict  = prelude;
  se_next  = w_user_base;
  se_stack = [];
  se_shape = [];
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
  let env = s.se_wenv in
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
        se_wenv = { s.se_wenv with
                      w_defs = (id, { wd_sig = row; wd_eff = pure_row })
                               :: s.se_wenv.w_defs };
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

  /// Pure inspection: no term is elaborated, nothing runs, the session is
  /// returned untouched. `locate` is the one declaration that cannot fail
  /// interestingly, which is why it is safe to type at any point.
  | SdLocate name -> (s, locate s.se_nenv s.se_dict name)

  | SdExpr body ->
    (match elab_expr s.se_nenv s.se_shape body with
     | Inl e -> (s, "error: " ^ e)
     | Inr t ->
       let env = s.se_wenv in
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
