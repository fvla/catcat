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
  /// OPERATION IDS AND WORD IDS ARE ONE NAMESPACE (D-01). `R02.step` resolves
  /// an operation by calling `find_handler k e w` with a `word_id`, so an
  /// operation allocated here takes the next word id like any definition. This
  /// counter is the whole of that unification at runtime.
  se_next  : word_id;
  se_next_eff : eff_id;
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
let prelude_words : list nentry = [
  { n_name = "+";   n_id = w_add; n_sig = bin_i64; n_op = None };
  { n_name = "-";   n_id = w_sub; n_sig = bin_i64; n_op = None };
  { n_name = "*";   n_id = w_mul; n_sig = bin_i64; n_op = None };
  { n_name = "/";   n_id = w_div; n_sig = bin_i64; n_op = None };
  { n_name = "%";   n_id = w_mod; n_sig = bin_i64; n_op = None };
  { n_name = "<";   n_id = w_lt;  n_sig = cmp_i64; n_op = None };
  { n_name = "<=";  n_id = w_le;  n_sig = cmp_i64; n_op = None };
  { n_name = "=";   n_id = w_eq;  n_sig = cmp_i64; n_op = None };
  { n_name = "not"; n_id = w_not; n_sig = un_bool; n_op = None };
  { n_name = "and"; n_id = w_and; n_sig = bin_bool; n_op = None };
  { n_name = "or";  n_id = w_or;  n_sig = bin_bool; n_op = None };
  { n_name = "true";  n_id = w_true;  n_sig = push_bool; n_op = None };
  { n_name = "false"; n_id = w_false; n_sig = push_bool; n_op = None };
]

/// Every prelude word is pure, so the effect row is `pure_row` throughout.
/// That stops being true at the first `effect` declaration.
let rec nenv_decls (ws:list nentry) : Tot (list (word_id & wdecl)) (decreases ws) =
  match ws with
  | []     -> []
  | n :: r -> (n.n_id, { wd_sig = n.n_sig;
                         wd_eff = (match n.n_op with
                                   | None   -> pure_row
                                   | Some e -> [(e, SDynamic)]) })
              :: nenv_decls r

let prelude_nenv : nenv = { ne_words = prelude_words; ne_effs = [] }

let init_session : session = {
  se_nenv  = prelude_nenv;
  se_wenv  = { w_defs = nenv_decls prelude_words; w_ops = empty_sig_env };
  se_dict  = prelude;
  se_next  = w_user_base;
  se_next_eff = 1;
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

(* --- effect rows in signatures ------------------------------------------- *)

/// `!Eff` in a signature used to be parsed and thrown away, which was the one
/// gap in `DOCS/U01` §7 that could actively mislead: the signature was accepted
/// and the effect vanished. Now it is resolved and checked.
let rec resolve_effs (e:nenv) (ns:list string)
  : Tot (either string (list eff_id)) (decreases ns) =
  match ns with
  | []     -> Inr []
  | n :: r ->
    (match lookup_eff e n with
     | None    -> Inl ("unknown effect: !" ^ n)
     | Some i  -> (match resolve_effs e r with
                   | Inl m   -> Inl m
                   | Inr is  -> Inr (i :: is)))

let subset_effs (a b:list eff_id) : Tot bool = for_all (fun i -> mem i b) a


/// Typecheck an elaborated definition with M06 and, if it agrees, install it.
///
/// `declared` is `Some row` when the user wrote a signature and `None` when it
/// was inferred. In the written case a disagreement is the user's error; in the
/// inferred case it would be a bug in `infer_sig`, so the message says so
/// rather than blaming the program.
/// `deceffs` is `Some is` when the user wrote `!E` markers. An UNWRITTEN
/// effect list is not an assertion of purity — a `define` with no signature at
/// all would otherwise be unable to use any effect — so it is only checked
/// when a signature was written.
let install_def (s:session) (name:string) (declared:option srow)
                (deceffs:option (list eff_id)) (row:srow) (t:term)
  : Tot (session & string) =
  let env = s.se_wenv in
  match infer env t with
  | None -> (s, "error: " ^ name ^ " does not typecheck")
  | Some (got, grow) ->
    if got <> row
    then (match declared with
          | Some _ -> (s, "error: " ^ name ^ " declares " ^ render_row row
                          ^ " but its body has " ^ render_row got)
          | None   -> (s, "internal error: inferred " ^ render_row row
                          ^ " for " ^ name ^ " but M06 says " ^ render_row got))
    else
      let actual = row_effs grow in
      let ok = (match deceffs with
                | None    -> true
                | Some ds -> subset_effs actual ds && subset_effs ds actual) in
      if not ok
      then (s, "error: " ^ name ^ " declares"
               ^ (match deceffs with
                  | Some ds -> (if Nil? ds then " no effects"
                                else render_effs s.se_nenv ds)
                  | None    -> "")
               ^ " but its body has"
               ^ (if Nil? actual then " none" else render_effs s.se_nenv actual))
      else
        let id = s.se_next in
        let s' = { s with
          se_nenv = { s.se_nenv with
                        ne_words = ({ n_name = name; n_id = id;
                                      n_sig = row; n_op = None })
                                   :: s.se_nenv.ne_words };
          se_wenv = { s.se_wenv with
                        w_defs = (id, { wd_sig = row; wd_eff = grow })
                                 :: s.se_wenv.w_defs };
          se_dict = dict_extend s.se_dict id (WDef t);
          se_next = id + 1 } in
        (s', "defined " ^ name ^ " " ^ render_row_eff s.se_nenv row grow)

(* --- effect declarations -------------------------------------------------- *)

/// Install one effect's operations. Each gets the next WORD id — one namespace
/// (D-01) — an `nentry` so it can be called like any word, an `op_decl` so
/// `M06.infer_impls` can check implementations against it, and a `WOp` binding
/// so `R02.step` walks the handler chain when it runs.
///
/// Four tables, one operation, and the fact that they are four rather than one
/// is an artefact of the phase split, not of the design.
let rec install_ops (s:session) (eid:eff_id) (ds:list (string & ssig))
  : Tot (either string session) (decreases ds) =
  match ds with
  | [] -> Inr s
  | (opname, sg) :: r ->
    (match elab_sig sg with
     | Inl e -> Inl ("declare " ^ opname ^ ": " ^ e)
     | Inr row ->
       let id = s.se_next in
       let decl = { od_eff = eid; od_sig = { op_pre = row.pre; op_post = row.post } } in
       let s' = { s with
         se_nenv = { s.se_nenv with
                       ne_words = ({ n_name = opname; n_id = id;
                                     n_sig = row; n_op = Some eid })
                                  :: s.se_nenv.ne_words };
         se_wenv = { w_defs = (id, { wd_sig = row; wd_eff = [(eid, SDynamic)] })
                              :: s.se_wenv.w_defs;
                     w_ops  = { se_ops = (id, decl) :: s.se_wenv.w_ops.se_ops } };
         se_dict = dict_extend s.se_dict id (WOp eid);
         se_next = id + 1 } in
       install_ops s' eid r)

let rec render_ops (e:nenv) (ds:list (string & ssig)) : Tot string (decreases ds) =
  match ds with
  | []               -> ""
  | (opname, _) :: r -> " " ^ opname ^ render_ops e r

let eval_decl (s:session) (d:sdecl) : Tot (session & string) =
  match d with

  | SdDefine name sg body ->
    (match resolve_effs s.se_nenv sg.ss_eff with
     | Inl e -> (s, "error: " ^ e)
     | Inr es ->
       (match elab_define s.se_nenv sg body with
        | Inl e         -> (s, "error: " ^ e)
        | Inr (row, t)  -> install_def s name (Some row) (Some es) row t))

  /// The inferred form prints the signature it worked out, which is the same
  /// text a language server would show inline (D01's tooling goal, N02 Q-11).
  | SdDefineInfer name body ->
    (match elab_define_infer s.se_nenv body with
     | Inl e         -> (s, "error: " ^ e)
     | Inr (row, t)  -> install_def s name None None row t)

  /// An effect declaration installs nothing runnable — it names operations and
  /// gives them signatures. Calling one without a handler in scope is legal and
  /// escapes to the top level, which is what `!IO` at `main` will mean (M5).
  | SdEffect name decls ->
    (match lookup_eff s.se_nenv name with
     | Some _ -> (s, "error: effect " ^ name ^ " is already declared")
     | None ->
       let eid = s.se_next_eff in
       let s0 = { s with
         se_nenv = { s.se_nenv with ne_effs = (name, eid) :: s.se_nenv.ne_effs };
         se_next_eff = eid + 1 } in
       (match install_ops s0 eid decls with
        | Inl e  -> (s, "error: " ^ e)
        | Inr s' -> (s', "effect " ^ name ^ render_ops s'.se_nenv decls)))

  /// Pure inspection: no term is elaborated, nothing runs, the session is
  /// returned untouched. `locate` is the one declaration that cannot fail
  /// interestingly, which is why it is safe to type at any point.
  | SdLocate name -> (s, locate s.se_nenv s.se_wenv s.se_dict name)

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
              /// A legitimate outcome, not an error: an effect with no handler
              /// in scope escapes to the top level, which is exactly what
              /// `!IO` at `main` will mean once the host supplies one (M5).
              | REffect op _  -> (s, "unhandled: " ^ show_word s.se_nenv op
                                     ^ " escaped with no handler in scope")
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
