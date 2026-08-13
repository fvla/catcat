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
open E01_Lexer
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
  /// The macro grammar this session parses against. Starts as the built-in
  /// table and grows with every accepted `macro` declaration; `ll1_extend`
  /// refuses one that would cost the grammar its LL(1) property, so the
  /// invariant `lemma_ll1_extend` states holds at every point in a session.
  se_macros : list mprod;
  se_stack : rstack;
  /// Static shape of `se_stack`, top-first.
  se_shape : list dtype;
}

let i64_t : dtype = TPrim PI64
let bool_t : dtype = TPrim PBool
let str_t  : dtype = TPrim PStr

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
  /// String words. `show` is the only way to get a number into a message now
  /// that IO is string-typed (D-65), and `cat` the only way to join one to a
  /// literal; without the pair, strings would be writable and useless.
  { n_name = "show"; n_id = w_show;
    n_sig = { pre = [i64_t]; post = [str_t] };          n_op = None };
  { n_name = "cat";  n_id = w_cat;
    n_sig = { pre = [str_t; str_t]; post = [str_t] };   n_op = None };
  /// Spelled `str=` because `=` is already `i64` equality and the core is
  /// monomorphic (D02 §5). An overloaded `=` is an interface, which is D03's
  /// job and not something to fake here with a second prelude entry.
  { n_name = "str="; n_id = w_streq;
    n_sig = { pre = [str_t; str_t]; post = [bool_t] };  n_op = None };
  /// Inverse of `show`. 0 on malformed input — the concession the `i64`-typed
  /// `read` already made, kept rather than replaced by a stuck machine.
  { n_name = "parse"; n_id = w_parse;
    n_sig = { pre = [str_t]; post = [i64_t] };          n_op = None };
  /// The built-in `IO` effect (category 2). These are ORDINARY operations of
  /// an ordinary effect — `n_op = Some eff_io` and nothing else — but no
  /// program can handle them, because `effect` allocates ids from 2 upward and
  /// the host owns 0 (`Dict`) and 1 (`IO`). So `print` and `read` always escape
  /// to `bin/catcat.ml`, the only thing in the system that can perform one.
  ///
  /// THEY TAKE AND RETURN STRINGS. The `i64` versions were a placeholder from
  /// before there was a string type, not a design: an IO facility that can only
  /// move integers cannot emit a message, and every example that wanted one had
  /// to print its parts as bare numbers.
  { n_name = "print"; n_id = w_print;
    n_sig = { pre = [str_t]; post = [] };  n_op = Some eff_io };
  { n_name = "read";  n_id = w_read;
    n_sig = { pre = []; post = [str_t] };  n_op = Some eff_io };
]

/// `IO` is in scope from the first line, so `( -- i64 !IO )` resolves without
/// anyone declaring it.
let prelude_effs : list (string & eff_id) =
  [("IO", eff_io); ("Unsafe", eff_unsafe); ("C", eff_c)]

/// EVERY WORD GETS AN OPERATION DECLARATION, not just the ones an `effect`
/// declared (D-63). `M06.w_sig` reads a word's signature out of `w_ops`, so a
/// word missing from this table has no signature at all — which is the point:
/// the drift M07's `coherent` predicate used to describe, where a `define`
/// populated one signature table and not the other, is no longer expressible.
///
/// A prelude word that is not an operation of a declared effect belongs to the
/// Dictionary, so it gets `eff_dict` at `SStatic`. `print` and `read` get `IO`
/// at `SDynamic`, which is what their row said before. Neither needs a `w_effs`
/// entry: a prelude word has no body whose effects would go there.
let rec nenv_ops (ws:list nentry) : Tot (list (word_id & op_decl)) (decreases ws) =
  match ws with
  | []     -> []
  | n :: r -> (n.n_id, { od_eff   = (match n.n_op with
                                     | None   -> eff_dict
                                     | Some e -> e);
                         od_stage = (match n.n_op with
                                     | None   -> SStatic
                                     | Some _ -> SDynamic);
                         od_sig   = { op_pre = n.n_sig.pre; op_post = n.n_sig.post } })
              :: nenv_ops r

let prelude_nenv : nenv = { ne_words = prelude_words; ne_effs = prelude_effs }

let init_session : session = {
  se_nenv  = prelude_nenv;
  se_wenv  = { w_effs = [];
               w_ops  = { se_ops = nenv_ops prelude_words } };
  se_dict  = prelude;
  se_next  = w_user_base;
  /// 0 `Dict`, 1 `IO`, 2 `Unsafe`, 3 `C`; user effects from 4 (D-66).
  se_next_eff = eff_user_base;
  se_macros = builtin_macros;
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
          /// A defined word is a Dictionary operation (D-60, D-63): its
          /// signature goes in `w_ops` under `eff_dict`, exactly like a
          /// declared effect's operation goes in under its own effect. The
          /// body's own effects go in `w_effs`, with the static `Dict` entries
          /// stripped — `M06.w_eff` re-derives the one that matters, and
          /// keeping the rest would make rows grow with call depth.
          se_wenv = { w_effs = (id, row_visible grow) :: s.se_wenv.w_effs;
                      w_ops  = { se_ops =
                        (id, { od_eff   = eff_dict;
                               od_stage = SStatic;
                               od_sig   = { op_pre = row.pre; op_post = row.post } })
                        :: s.se_wenv.w_ops.se_ops } };
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
       let decl = { od_eff = eid; od_stage = SDynamic;
                    od_sig = { op_pre = row.pre; op_post = row.post } } in
       let s' = { s with
         se_nenv = { s.se_nenv with
                       ne_words = ({ n_name = opname; n_id = id;
                                     n_sig = row; n_op = Some eid })
                                  :: s.se_nenv.ne_words };
         /// No `w_effs` entry: an operation performs itself and nothing else,
         /// and `M06.w_eff` derives that entry from `decl` (D-63). Storing a
         /// second copy is what used to let the two disagree.
         se_wenv = { s.se_wenv with
                     w_ops  = { se_ops = (id, decl) :: s.se_wenv.w_ops.se_ops } };
         se_dict = dict_extend s.se_dict id (WOp eid);
         se_next = id + 1 } in
       install_ops s' eid r)

(* --- foreign declarations ------------------------------------------------- *)

/// Which types cross the C boundary. `i64` becomes `long`, `str` becomes
/// `const char *`, and nothing else is allowed through yet.
///
/// CHECKED AT THE DECLARATION, not at the call. The host has no static
/// information at the moment it performs an operation, so a signature it cannot
/// marshal would fail as a stuck machine on some later line, pointing at the
/// call rather than at the mistake. Rejecting `extern f ( bool -- )` where it is
/// written is the difference between a type system and a crash.
let c_marshalable (d:dtype) : Tot bool =
  d = TPrim PI64 || d = TPrim PStr

let rec c_marshalable_all (ds:list dtype) : Tot bool (decreases ds) =
  match ds with
  | []     -> true
  | d :: r -> c_marshalable d && c_marshalable_all r

/// Install a foreign function (D-66).
///
/// FOUR TABLES AGAIN, and the interesting one is the third. An `extern` word is
/// an operation of `C`, so `w_ops` gets `od_eff = eff_c` and `R02.step` walks
/// the handler chain for it exactly as it does for `print` — reaching the host
/// when nobody intercepts. But it ALSO gets a `w_effs` entry of `!Unsafe`, and
/// that is not decoration: `M06.w_eff` returns the derived head entry followed
/// by the stored row, so a call to `strlen` has row `!C !Unsafe` and both
/// propagate to every caller by the ordinary rules.
///
/// This is the split D-63 created paying off. The derived entry says what
/// calling the word PERFORMS; the stored row says what its body does. For a
/// foreign function the body is code this system has never seen, and `!Unsafe`
/// is the honest name for that.
let install_extern (s:session) (name:string) (sg:ssig)
  : Tot (session & string) =
  match lookup_name s.se_nenv name with
  | Some _ -> (s, "error: " ^ name ^ " is already defined")
  | None ->
    (match elab_sig sg with
     | Inl e -> (s, "error: extern " ^ name ^ ": " ^ e)
     | Inr row ->
       if not (Nil? sg.ss_eff)
       then (s, "error: extern " ^ name
                ^ ": the effects are fixed at !C !Unsafe and are not written")
       else if not (c_marshalable_all row.pre && c_marshalable_all row.post)
       then (s, "error: extern " ^ name
                ^ ": only i64 and str cross the C boundary so far")
       else if length row.post > 1
       then (s, "error: extern " ^ name
                ^ ": a C function returns at most one value")
       else
         let id = s.se_next in
         let decl = { od_eff = eff_c; od_stage = SDynamic;
                      od_sig = { op_pre = row.pre; op_post = row.post } } in
         let s' = { s with
           se_nenv = { s.se_nenv with
                         ne_words = ({ n_name = name; n_id = id;
                                       n_sig = row; n_op = Some eff_c })
                                    :: s.se_nenv.ne_words };
           se_wenv = { w_effs = (id, [(eff_unsafe, SDynamic)]) :: s.se_wenv.w_effs;
                       w_ops  = { se_ops = (id, decl) :: s.se_wenv.w_ops.se_ops } };
           se_dict = dict_extend s.se_dict id (WOp eff_c);
           se_next = id + 1 } in
         (s', "extern " ^ name ^ " "
              ^ render_row_eff s'.se_nenv row (w_eff s'.se_wenv id)))

let rec render_ops (e:nenv) (ds:list (string & ssig)) : Tot string (decreases ds) =
  match ds with
  | []               -> ""
  | (opname, _) :: r -> " " ^ opname ^ render_ops e r

/// One line confirming what a `macro` declaration registered: the sentence it
/// consumes, and for a branching production the keys that close it. The full
/// form, templates included, is what `locate` prints.
let render_prod (p:mprod) : Tot string =
  show_slots p.mp_pre
  ^ (if Nil? p.mp_branches then ""
     else " …, closed by " ^ key_list p.mp_branches)

(* --- suspension ----------------------------------------------------------- *)

/// What the session needs in order to finish a line that stopped mid-way
/// because an operation escaped every handler.
///
/// THE HOST IS THE OUTERMOST HANDLER. That is category 2 of the effect design
/// — effects only the compiler or interpreter can supply — and it needs no
/// language feature, only the observation that `R05.run` is a pure function
/// which, on reaching an unhandled operation, can hand its caller everything
/// required to carry on.
///
/// Nothing here is visible to a catcat program. The `kont` is the
/// interpreter's own machine state; see the long note in `R05_Driver.fsti`
/// about why that is not a language-level continuation and must not become one.
noeq type suspension = {
  su_sess  : session;
  /// The expression's outputs, and the shape beneath them, so the session's
  /// static shape can be restored when the line eventually finishes.
  su_post  : list dtype;
  su_below : list dtype;
  /// What is LEFT TO PARSE, not left to evaluate. A `macro` declaration
  /// changes the grammar, so the rest of a line cannot be parsed until
  /// everything before it has run (D-54).
  su_rest  : list token;
  su_acc   : string;
}

noeq type dresult =
  | DDone   : session -> string -> dresult
  | DEffect : op_id -> rstack -> kont -> session -> list dtype -> list dtype
            -> dresult

noeq type lresult =
  | LDone   : session -> string -> lresult
  /// `l_op` escaped with `l_stk` as the live stack — the operation's arguments
  /// on top — and `l_kont` as where to carry on. The host performs the
  /// operation and calls `resume_line`.
  | LEffect : op_id -> rstack -> kont -> suspension -> lresult

/// Interpret one outcome of the machine. Factored out because `resume_line`
/// needs exactly the same four cases: resuming is running.
let run_expr (s:session) (post below:list dtype) (r:rresult) : Tot dresult =
  match r with
  | RDone stk ->
    let s' = { s with se_stack = stk; se_shape = post @ below } in
    DDone s' ("ok  " ^ render_stack stk)
  /// Not an error: an operation with no handler in scope has reached the host,
  /// which is the outermost handler. For `IO` that is the intended path; for a
  /// user effect it means nobody handled it, and what to say about that is the
  /// caller's decision, not this function's.
  | REffect op stk k -> DEffect op stk k s post below
  | RStuck m         -> DDone s ("STUCK: " ^ m)
  | ROutOfFuel       -> DDone s "out of fuel"

let eval_decl (s:session) (d:sdecl) : Tot dresult =
  match d with

  | SdDefine name sg body ->
    (match resolve_effs s.se_nenv sg.ss_eff with
     | Inl e -> DDone s ("error: " ^ e)
     | Inr es ->
       (match elab_define s.se_nenv sg body with
        | Inl e         -> DDone s ("error: " ^ e)
        | Inr (row, t)  -> let (s', m) = install_def s name (Some row) (Some es) row t in
                           DDone s' m))

  /// The inferred form prints the signature it worked out, which is the same
  /// text a language server would show inline (D01's tooling goal, N02 Q-11).
  | SdDefineInfer name body ->
    (match elab_define_infer s.se_nenv body with
     | Inl e         -> DDone s ("error: " ^ e)
     | Inr (row, t)  -> let (s', m) = install_def s name None None row t in
                        DDone s' m)

  /// An effect declaration installs nothing runnable — it names operations and
  /// gives them signatures. Calling one without a handler in scope is legal and
  /// escapes to the top level, which is what `!IO` at `main` will mean (M5).
  | SdEffect name decls ->
    (match lookup_eff s.se_nenv name with
     | Some _ -> DDone s ("error: effect " ^ name ^ " is already declared")
     | None ->
       let eid = s.se_next_eff in
       let s0 = { s with
         se_nenv = { s.se_nenv with ne_effs = (name, eid) :: s.se_nenv.ne_effs };
         se_next_eff = eid + 1 } in
       (match install_ops s0 eid decls with
        | Inl e  -> DDone s ("error: " ^ e)
        | Inr s' -> DDone s' ("effect " ^ name ^ render_ops s'.se_nenv decls)))

  | SdExtern name sg ->
    let (s', msg) = install_extern s name sg in DDone s' msg

  /// Pure inspection: no term is elaborated, nothing runs, the session is
  /// returned untouched. `locate` is the one declaration that cannot fail
  /// interestingly, which is why it is safe to type at any point.
  | SdLocate name ->
    DDone s (locate s.se_macros s.se_nenv s.se_wenv s.se_dict name)

  /// A macro declaration changes the GRAMMAR, so unlike every other
  /// declaration it affects how the rest of the input is read — which is why
  /// `eval_line` parses one declaration at a time (D-54).
  ///
  /// Nothing is elaborated and nothing runs: a macro has no signature, no word
  /// id and no dictionary entry, because it does not exist at run time. Its
  /// template was already expanded against the table in force when it was
  /// declared, so registering it cannot make expansion loop.
  | SdMacro p ->
    (match ll1_extend s.se_macros p with
     | Inl e   -> DDone s ("error: " ^ e)
     | Inr mt' -> DDone ({ s with se_macros = mt' })
                        ("macro " ^ p.mp_name ^ render_prod p))

  | SdExpr body ->
    (match elab_expr s.se_nenv s.se_shape body with
     | Inl e -> DDone s ("error: " ^ e)
     | Inr t ->
       let env = s.se_wenv in
       (match infer env t with
        | None -> DDone s "error: expression does not typecheck"
        | Some (row, _) ->
          (match strip_prefix row.pre s.se_shape with
           | None ->
             DDone s ("error: this needs " ^ render_tys (rev row.pre)
                      ^ " on the stack, but the stack holds "
                      ^ render_tys (rev s.se_shape))
           | Some below -> run_expr s row.post below (eval s.se_dict fuel t s.se_stack))))

let join_msg (acc msg:string) : Tot string =
  if acc = "" then msg else acc ^ "\n" ^ msg

/// Parse ONE declaration against the session's current grammar, run it, and go
/// on with whatever tokens are left.
///
/// Parsing and evaluation interleave because a `macro` declaration changes the
/// grammar the rest of the input is read with — Forth's `IMMEDIATE` has the
/// same shape and for the same reason. The cost is real and worth naming: a
/// parse error part-way through a line no longer leaves the session untouched,
/// because the declarations before it have already run (D-54).
let rec eval_tokens (s:session) (ts:list token) (acc:string)
  : Tot lresult (decreases (length ts)) =
  match ts with
  | [] -> LDone s acc
  | _  ->
    (match parse_decl s.se_macros ts with
     | PErr e -> LDone s (join_msg acc ("error: " ^ e))
     | POk d rest ->
       (match eval_decl s d with
        /// No progress check. `parse_decl` now PROVES it consumed at least one
        /// token (D-58), which it has to, because a `macro` declaration changes
        /// the grammar the rest of the line is read with and so there is no
        /// fixed grammar to appeal to. This loop used to stop the line if the
        /// parser stood still; that branch was unreachable and is gone.
        | DDone s' msg -> eval_tokens s' rest (join_msg acc msg)
        | DEffect op stk k s0 post below ->
          LEffect op stk k ({ su_sess = s0; su_post = post; su_below = below;
                              su_rest = rest; su_acc = acc })))

(* ------------------------------------------------------------------------ *)
(* Entry point                                                              *)
(* ------------------------------------------------------------------------ *)

/// Evaluate one line of source. A LEXING error leaves the session untouched; a
/// parse or type error leaves it as of the last declaration that succeeded,
/// which is the price of macros taking effect where they are written (D-54).
///
/// `LEffect` means the line is not finished: an operation escaped every
/// handler and the host must perform it, then call `resume_line`.
let eval_line (s:session) (src:string) : Tot lresult =
  match lex_line src with
  | Inl e   -> LDone s ("error: " ^ e)
  | Inr tks -> eval_tokens s tks ""

/// Carry on after the host has performed an operation. `stk` is the live stack
/// with the operation's arguments removed and its results pushed.
let resume_line (su:suspension) (k:kont) (stk:rstack) : Tot lresult =
  match run_expr su.su_sess su.su_post su.su_below
                 (resume su.su_sess.se_dict fuel k stk) with
  | DDone s' msg -> eval_tokens s' su.su_rest (join_msg su.su_acc msg)
  | DEffect op stk' k' s0 post below ->
    LEffect op stk' k' ({ su with su_sess = s0; su_post = post; su_below = below })

/// WHAT THE HOST NEEDS IN ORDER TO SERVICE AN OPERATION (D-66).
///
/// `LEffect` carries a `word_id`, and for `IO` that was enough because there
/// were two of them and the host could compare ids. A foreign call cannot work
/// that way: `extern` allocates a fresh id per declaration, and what the host
/// has to know is the C SYMBOL, which is the word's name.
///
/// These two functions are the whole interface. Exposing them beats letting
/// `bin/catcat.ml` reach into `su_sess.se_nenv` itself, which would tie the
/// host loop to the shape of a record that has changed twice already — and the
/// suspension is the only thing the host is handed.
let susp_op_name (su:suspension) (op:op_id) : Tot string =
  show_word su.su_sess.se_nenv op

let susp_op_eff (su:suspension) (op:op_id) : Tot eff_id =
  eff_of su.su_sess.se_wenv.w_ops op

/// What to print when an operation reaches the host and the host has no
/// implementation for it — every user-declared effect, since only `IO` and `C`
/// are the host's to service.
let unhandled_msg (s:session) (op:op_id) : Tot string =
  "unhandled: " ^ show_word s.se_nenv op ^ " escaped with no handler in scope"

/// Finish a line the host has declined to service, running whatever
/// declarations followed the one that suspended.
let abandon_line (su:suspension) (op:op_id) : Tot lresult =
  eval_tokens su.su_sess su.su_rest
              (join_msg su.su_acc (unhandled_msg su.su_sess op))

/// The current stack, rendered bottom-to-top.
let show_stack (s:session) : Tot string = render_stack s.se_stack
