module E03_Parser

/// P03, module 03: tokens to surface AST.
///
/// SUMMARY
///   A hand-written recursive-descent parser. Concatenative syntax has almost
///   no grammar — a program is a flat sequence of terms — so the only real
///   nesting is `{ … }` blocks and `( … )` signatures.
///
/// Every parse function returns the remaining tokens alongside its result, and
/// carries a length refinement so F* can see the recursion terminates. That
/// refinement is load-bearing rather than decorative: without it the block
/// parser has no structural argument to descend on.
///
/// ERROR REPORTING
///   Errors are plain strings. Source positions would need the lexer to carry
///   spans, which is worth doing when the language server work starts (P06) and
///   is not worth doing now.

open M01_Kinds
open FStar.List.Tot
open E01_Lexer
open E02_Ast

/// Parse result: either an error, or a value plus strictly-bounded remainder.
noeq type presult (a:Type) =
  | PErr : string -> presult a
  | POk  : a -> list token -> presult a

(* ------------------------------------------------------------------------ *)
(* Macros                                                                   *)
(* ------------------------------------------------------------------------ *)

/// A MACRO IS A GRAMMAR PRODUCTION PLUS A TERM TRANSFORMER (D-35).
///
/// It declares what it consumes to its right — a fixed sequence of slots,
/// then an alternation keyed on a literal word — and a function turning what
/// was captured into surface terms. Two properties are deliberate:
///
///   * **No stack access.** A macro's input is syntax and its output is
///     syntax. Nothing it does is visible at runtime, so it cannot depend on
///     or disturb the value stack.
///   * **It cannot consume the enclosing `}`.** Slots are parsed by the same
///     functions the block parser uses, and a block's closing brace belongs to
///     the block. A macro that runs out of tokens inside its production
///     reports an error rather than reaching past the brace.
///
/// Every alternation branch is keyed on a word that is CONSUMED, so the
/// grammar has no ε-branch and the whole table stays LL(1) with no token
/// reserved globally (D-34). `ll1_ok` below checks that, and is the seed of
/// the planned verified CFG-to-recursive-descent generator (D-30): the same
/// property that tool will have to establish, checked here on the one grammar
/// the language ships.
///
/// STATUS: the table starts with `if` and grows. A `macro` declaration adds a
/// production and its templates; the session carries the table and rechecks
/// `ll1_ok` before accepting one, so the grammar the parser runs on is verified
/// LL(1) at every point in a session and not merely at startup.
///
/// The types themselves are in `E02_Ast`, because a production is now something
/// a PROGRAM writes rather than a table this module owns.

(* --- the LL(1) invariant ------------------------------------------------- *)

let rec keys_distinct (seen:list string) (bs:list mbranch)
  : Tot bool (decreases bs) =
  match bs with
  | []     -> true
  | b :: r -> not (mem b.mb_key seen) && keys_distinct (b.mb_key :: seen) r

let rec names_distinct (seen:list string) (ps:list mprod)
  : Tot bool (decreases ps) =
  match ps with
  | []     -> true
  | p :: r -> not (mem p.mp_name seen) && names_distinct (p.mp_name :: seen) r

let rec branches_ok (ps:list mprod) : Tot bool (decreases ps) =
  match ps with
  | []     -> true
  | p :: r -> keys_distinct [] p.mp_branches && branches_ok r

/// The macro table is LL(1) exactly when no two macros share a leading word
/// and no two alternatives of one macro share a key. There is nothing else to
/// check, because every alternative is keyed and consumed — an unkeyed or
/// optional tail is what would require a second token, and the slot vocabulary
/// cannot express one.
let ll1_ok (ps:list mprod) : Tot bool =
  names_distinct [] ps && branches_ok ps

(* ------------------------------------------------------------------------ *)
(* Types                                                                    *)
(* ------------------------------------------------------------------------ *)

/// A type is a name, optionally applied to arguments in brackets (D-90).
///
/// `Box` and `Rc` used to be special-cased here, each taking exactly one
/// argument. They are not any more: `N[t₁ … tₙ]` is one production, the arity
/// is whatever the declaration says, and `E04.elab_ty` decides what the name
/// means. So `Box[i64]`, `Rc[str]` and `Option[i64]` all parse by the same rule
/// and a program can introduce the third.
///
/// LL(1) with nothing to look ahead at: `[` is self-delimiting, so `Box[i64` is
/// already three tokens and the decision to read arguments is made on the one
/// token in hand (D-30). A bare `Option` with no brackets parses fine and is
/// rejected later, by arity, where the message can say how many it wanted.
let rec parse_ty (ts:list token)
  : Tot (r:presult sty { POk? r ==> length (POk?._1 r) <= length ts })
        (decreases %[length ts; 0]) =
  match ts with
  | [] -> PErr "expected a type, found end of input"
  | TkHash n :: rest -> POk (StyVar n) rest
  | TkWord w :: TkLBrack :: inner ->
    (match parse_ty_args w [] inner with
     | PErr e -> PErr e
     | POk args tail -> POk (StyApp w args) tail)
  | TkWord w :: rest -> POk (StyName w) rest
  | t :: _ -> PErr ("expected a type, found " ^ render_token t)

/// The arguments of an applied type, up to the closing `]`. `w` is carried only
/// so the errors can name what is being applied.
and parse_ty_args (w:string) (acc:list sty) (ts:list token)
  : Tot (r:presult (list sty) { POk? r ==> length (POk?._1 r) < length ts })
        (decreases %[length ts; 1]) =
  match ts with
  | [] -> PErr ("expected ']' closing " ^ w ^ ", found end of input")
  | TkRBrack :: rest ->
    if Nil? acc
    then PErr (w ^ " needs at least one type argument, as in " ^ w ^ "[i64]")
    else POk (rev acc) rest
  | _ ->
    (match parse_ty ts with
     | PErr e -> PErr e
     | POk t after ->
       if length after >= length ts
       then PErr ("expected a type argument or ']' closing " ^ w)
       else parse_ty_args w (t :: acc) after)

/// `[ t1 t2 … ]` after a word in term position — an explicit instantiation
/// (D-82). Space-separated, like the `[#T #U]` of the declaration it answers.
///
/// LL(1) with nothing to look ahead at, for the same reason `parse_tparams` is:
/// `[` is self-delimiting, so `f[i64` is already three tokens and the decision
/// to come here is made on the one token in hand (D-30).
let rec parse_tyargs (acc:list sty) (ts:list token)
  : Tot (r:presult (list sty) { POk? r ==> length (POk?._1 r) < length ts })
        (decreases (length ts)) =
  match ts with
  | [] -> PErr "expected ']' closing the type arguments, found end of input"
  | TkRBrack :: rest ->
    if Nil? acc
    then PErr "a generic needs at least one type argument, as in f[i64]"
    else POk (rev acc) rest
  | _ ->
    (match parse_ty ts with
     | PErr e -> PErr e
     | POk t after ->
       /// `parse_ty` consumes at least one token on every success, which is what
       /// stops `f[Box]` — an error, not a loop — from spinning here.
       if length after >= length ts
       then PErr "expected a type argument or ']'"
       else parse_tyargs (t :: acc) after)

(* ------------------------------------------------------------------------ *)
(* Signatures                                                               *)
(* ------------------------------------------------------------------------ *)

/// Inputs: everything up to `--`. A `$x:ty` pair yields a named parameter.
let rec parse_inputs (acc:list sparam) (ts:list token)
  : Tot (r:presult (list sparam) { POk? r ==> length (POk?._1 r) <= length ts })
        (decreases (length ts)) =
  match ts with
  | [] -> PErr "expected '--' in signature, found end of input"
  | TkArrow :: rest -> POk (rev acc) rest
  /// The signature ended without an arrow. Overwhelmingly this means `--` was
  /// written against a neighbour — `( i64--i64 )` — which lexes as one word,
  /// since `--` is an ordinary space-separated word (D-28). Say so.
  | TkRParen :: _ ->
    PErr "expected '--' in this signature; it must be surrounded by spaces, \
          as in ( i64 -- i64 )"
  | TkDollar n :: TkColon :: rest ->
    (match parse_ty rest with
     | PErr e -> PErr e
     | POk t after -> parse_inputs ({ sp_name = Some n; sp_ty = t } :: acc) after)
  | TkDollar n :: _ ->
    PErr ("named parameter $" ^ n ^ " needs a type, as in $" ^ n ^ ":i64")
  | _ ->
    (match parse_ty ts with
     | PErr e -> PErr e
     | POk t after ->
       if length after < length ts
       then parse_inputs ({ sp_name = None; sp_ty = t } :: acc) after
       else PErr "signature made no progress")

/// Outputs: types and `!Eff` markers up to the closing paren.
let rec parse_outputs (acc:list sty) (effs:list string) (ts:list token)
  : Tot (r:presult (list sty & list string)
         { POk? r ==> length (POk?._1 r) <= length ts })
        (decreases (length ts)) =
  match ts with
  | [] -> PErr "expected ')' closing signature, found end of input"
  | TkRParen :: rest -> POk (rev acc, rev effs) rest
  | TkBang n :: rest -> parse_outputs acc (n :: effs) rest
  | _ ->
    (match parse_ty ts with
     | PErr e -> PErr e
     | POk t after ->
       if length after < length ts
       then parse_outputs (t :: acc) effs after
       else PErr "signature made no progress")

/// Turn the collected `!` markers into `E02.ssig`'s three-way answer (D-77).
/// A bare `!` arrives as the empty name, which is where it stops: `ssig` says
/// `Some []`, and no later pass has to know that `""` meant anything.
let classify_effs (ns:list string) : Tot (either string (option (list string))) =
  if Nil? ns then Inr None
  else if mem "" ns
  then (if length ns = 1 then Inr (Some [])
        else Inl "'!' asserts that there are no effects, so it cannot be \
                  written alongside a named one")
  else Inr (Some ns)

/// A whole `( … -- … )`, with the opening paren already consumed.
let parse_sig_body (ts:list token)
  : Tot (r:presult ssig { POk? r ==> length (POk?._1 r) <= length ts }) =
  match parse_inputs [] ts with
  | PErr e -> PErr e
  | POk ins after ->
    (match parse_outputs [] [] after with
     | PErr e -> PErr e
     | POk (outs, effs) tail ->
       (match classify_effs effs with
        | Inl e     -> PErr e
        | Inr effs' -> POk ({ ss_in = ins; ss_out = outs; ss_eff = effs' }) tail))

(* ------------------------------------------------------------------------ *)
(* The macro table                                                          *)
(* ------------------------------------------------------------------------ *)

/// `if { c } then { t } endif`, or with an `else { e }` before the terminator.
///
/// The terminator is mandatory and both alternatives are keyed, which is what
/// keeps `then`, `else` and `endif` ordinary word names outside this
/// production (D-34). Verified: they are all still definable.
///
/// EVERY PRODUCTION IN THIS TABLE IS A TEMPLATE (D-73). `if` used to be the one
/// exception: it carried `mp_builtin = true`, empty templates, and a
/// hand-written `expand_if` that `expand` dispatched to by name.
///
/// That was never necessary. A template is a `list sterm` — an F* value, not
/// source text — so it can mention `StCase` perfectly well; what `StCase` lacks
/// is a way for a USER to type it, which is a fact about the surface grammar and
/// not about the macro system. Writing `if`'s two templates out deletes the
/// flag, the expander and the branch of `expand` that chose between them, and
/// leaves one code path where there were two.
///
/// What is still true, and is what `locate if` now says: a user could not
/// declare this macro, because there is no way to write `StCase` in source.
/// Giving `case` a surface spelling is the remaining step and it belongs with
/// surface sums, since a two-branch `case` on a `bool` is all `if` needs and a
/// spelling fixed at two branches would have to be redesigned the moment a sum
/// has three.
///
/// `unsafe`'s template is exactly what a user would type (D-66):
///
///     macro unsafe ( { $b } ) { handle Unsafe over ( ) init { } { } { $b } }
///
/// It is here only so that it exists from the first line. That is the whole
/// implementation of D-57's `unsafe`: an effect with no operations, discharged
/// by an ordinary handler, sugared by an ordinary macro. There is no keyword, no
/// elaborator case, no lint connecting a declaration to a block — a word whose
/// row still carries `!Unsafe` IS an unsafe word, by the same rule that makes
/// `!IO` mean what it means, and the propagation is the effect system doing its
/// usual job. `locate unsafe` prints the expansion, so the sugar is inspectable
/// rather than magic.
let builtin_macros : list mprod = [
  /// The condition's terms are spliced first — `StVar "c"` is a block slot, so
  /// it expands to its CONTENTS — and then the case. Branches in TAG order,
  /// FALSE first (D-33), so `else` precedes `then`; an absent `else` is the
  /// empty branch, which is why "the `then` branch must not change the stack"
  /// needs no rule of its own.
  { mp_name     = "if";
    mp_pre      = [MsBlock "c"; MsKeyword "then"; MsBlock "t"];
    mp_branches = [ { mb_key   = "endif"; mb_slots = [];
                      mb_body  = [StVar "c"; StCase [[]; [StVar "t"]]] };
                    { mb_key   = "else";
                      mb_slots = [MsBlock "e"; MsKeyword "endif"];
                      mb_body  = [StVar "c"; StCase [[StVar "e"]; [StVar "t"]]] } ];
    mp_body     = [] };
  { mp_name     = "unsafe";
    mp_pre      = [MsBlock "b"];
    mp_branches = [];
    mp_body     = [StHandle "Unsafe" [] [] [] [StVar "b"]] };
  /// `try { … } catch { … }` (D-71). Like `if`, a user could not declare it,
  /// because `StTry` has no surface spelling either.
  ///
  /// NO TERMINATOR, and none is needed. `catch` is mandatory and the production
  /// ends after its block, so there is no alternation point and no ε-branch —
  /// the reason `if` needs `endif` (D-34) is that its `else` is optional, which
  /// this has no analogue of. `try` and `catch` stay ordinary word names outside
  /// this production.
  { mp_name     = "try";
    mp_pre      = [MsBlock "b"; MsKeyword "catch"; MsBlock "c"];
    mp_branches = [];
    mp_body     = [StTry [StVar "b"] [StVar "c"]] }
]

/// The built-in table really is LL(1), checked rather than asserted in prose.
let lemma_table_ll1 () : Lemma (ll1_ok builtin_macros) =
  assert_norm (ll1_ok builtin_macros)

/// And it satisfies the rule it imposes on user declarations (D-73). Worth
/// checking rather than assuming: `if`'s templates were empty until this
/// change, so the table had never been asked the question.
let lemma_table_hygienic ()
  : Lemma (for_all (fun p -> None? (mprod_stray p)) builtin_macros) =
  assert_norm (for_all (fun p -> None? (mprod_stray p)) builtin_macros)

let rec lookup_macro (ps:list mprod) (w:string)
  : Tot (option mprod) (decreases ps) =
  match ps with
  | []     -> None
  | p :: r -> if p.mp_name = w then Some p else lookup_macro r w

let rec lookup_branch (bs:list mbranch) (w:string)
  : Tot (option mbranch) (decreases bs) =
  match bs with
  | []     -> None
  | b :: r -> if b.mb_key = w then Some b else lookup_branch r w

let rec key_list (bs:list mbranch) : Tot string (decreases bs) =
  match bs with
  | []      -> ""
  | b :: [] -> "'" ^ b.mb_key ^ "'"
  | b :: r  -> "'" ^ b.mb_key ^ "', " ^ key_list r

(* --- growing the table --------------------------------------------------- *)

/// Add a production, refusing one that would cost the grammar its LL(1)
/// property. The first two tests exist only to say WHICH rule was broken —
/// "the grammar would be ambiguous" is a verdict, not a diagnostic — and the
/// third is the property itself, tested rather than argued.
let ll1_extend (mt:list mprod) (p:mprod) : Tot (either string (list mprod)) =
  if Some? (lookup_macro mt p.mp_name)
  then Inl ("a macro named '" ^ p.mp_name ^ "' already exists; two productions \
             on the same leading word would need a second token to tell apart")
  else if not (keys_distinct [] p.mp_branches)
  then Inl ("two alternatives of '" ^ p.mp_name ^ "' share a key, so the token \
             that selects between them does not")
  else if not (ll1_ok (p :: mt))
  then Inl ("adding '" ^ p.mp_name ^ "' would make the macro grammar ambiguous")
  /// HYGIENE, checked here because here is where a template first exists
  /// (D-73). A `$x` naming no slot cannot be a temporary the author
  /// introduced — nothing in a macro body binds a local — so it can only read
  /// whatever local encloses the expansion, which is capture. The message
  /// quotes the name and says which of the two mistakes it is likely to be.
  else (match mprod_stray p with
        | Some x ->
          Inl ("'" ^ p.mp_name ^ "' reads $" ^ x ^ ", which names no slot of \
                the production; a macro body cannot bind a local, so this \
                would read the caller's $" ^ x ^ ". Add a slot for it, or \
                correct the spelling")
        | None -> Inr (p :: mt))

/// Every table a session ever parses against is LL(1). Not a vacuous statement
/// dressed as a lemma: it holds because `ll1_extend` decides the property
/// before accepting, and it is the whole invariant that lets `parse_terms`
/// dispatch on the token in hand with no lookahead (D-30).
let lemma_ll1_extend (mt:list mprod) (p:mprod)
  : Lemma (match ll1_extend mt p with
           | Inr mt' -> ll1_ok mt'
           | Inl _   -> True) = ()

(* --- what LL(1) buys: the parser's choice is forced ---------------------- *)

/// The content of `ll1_ok` (D-58). `lookup_macro` and `lookup_branch` are
/// functions, so they are trivially deterministic; what is NOT trivial, and is
/// what the parser actually relies on, is that the production they return is
/// the ONLY one that could have matched. Distinctness is precisely that: it is
/// what rules out a second candidate further down the table, and hence what
/// makes "dispatch on the token in hand" equivalent to "consider every
/// production" without any lookahead.
///
/// Stated on membership rather than on position, since the parser never learns
/// where in the table a production sits.
///
/// The two proofs need one fact each: a member's key was never in `seen`. That
/// is what excludes the case where an earlier entry shares the key, which is
/// exactly the case an ambiguous grammar would allow.
let rec lemma_keys_unseen (seen:list string) (bs:list mbranch) (b:mbranch)
  : Lemma (requires keys_distinct seen bs /\ mem b bs)
          (ensures  not (mem b.mb_key seen))
          (decreases bs) =
  match bs with
  | []     -> ()
  | x :: r -> if b = x then () else lemma_keys_unseen (x.mb_key :: seen) r b

let rec lemma_lookup_branch_forced (bs:list mbranch) (b:mbranch) (seen:list string)
  : Lemma (requires keys_distinct seen bs /\ mem b bs)
          (ensures  lookup_branch bs b.mb_key == Some b)
          (decreases bs) =
  match bs with
  | []     -> ()
  | x :: r ->
    if b = x then ()
    else (lemma_keys_unseen (x.mb_key :: seen) r b;
          lemma_lookup_branch_forced r b (x.mb_key :: seen))

let rec lemma_names_unseen (seen:list string) (ps:list mprod) (p:mprod)
  : Lemma (requires names_distinct seen ps /\ mem p ps)
          (ensures  not (mem p.mp_name seen))
          (decreases ps) =
  match ps with
  | []     -> ()
  | x :: r -> if p = x then () else lemma_names_unseen (x.mp_name :: seen) r p

let rec lemma_lookup_macro_forced (ps:list mprod) (p:mprod) (seen:list string)
  : Lemma (requires names_distinct seen ps /\ mem p ps)
          (ensures  lookup_macro ps p.mp_name == Some p)
          (decreases ps) =
  match ps with
  | []     -> ()
  | x :: r ->
    if p = x then ()
    else (lemma_names_unseen (x.mp_name :: seen) r p;
          lemma_lookup_macro_forced r p (x.mp_name :: seen))

/// The form the parser uses: on an LL(1) table, a macro that is present is the
/// one `parse_terms` will find.
/// WHAT IS STILL OWED. The above says the CHOICE is forced once the parser has
/// decided to look a name up. It does not say the parser never has to guess in
/// the first place — that `ll1_ok mt` implies `parse_terms mt` never needs a
/// second token — because there is no grammar OBJECT here to state it against:
/// this is a hand-written recursive-descent parser, and the property would have
/// to relate it to a `list mprod` read as a grammar. That relation is precisely
/// what the planned verified CFG-to-recursive-descent generator (D-30) supplies,
/// and it is the reason `ll1_ok` is written as a predicate over the table rather
/// than folded into the parser: the tool that will discharge it needs the table
/// as data. Recorded in prose rather than stubbed (D-58).
let lemma_ll1_lookup_forced (ps:list mprod) (p:mprod)
  : Lemma (requires ll1_ok ps /\ memP p ps)
          (ensures  lookup_macro ps p.mp_name == Some p) =
  lemma_lookup_macro_forced ps p []

(* --- expansion ----------------------------------------------------------- *)

/// Which template a set of captures selects: the production's own when it has
/// no alternatives, otherwise the one belonging to the branch whose key was
/// consumed. `McKey` is the only reason the key is recorded at all.
let rec key_taken (caps:list mcap) : Tot (option string) (decreases caps) =
  match caps with
  | []            -> None
  | McKey k :: _  -> Some k
  | _ :: r        -> key_taken r

let template_of (p:mprod) (caps:list mcap) : Tot (either string (list sterm)) =
  if Nil? p.mp_branches then Inr p.mp_body
  else match key_taken caps with
       | None   -> Inl (p.mp_name ^ ": no alternative was selected")
       | Some k -> (match lookup_branch p.mp_branches k with
                    | None   -> Inl (p.mp_name ^ ": no alternative keyed '" ^ k ^ "'")
                    | Some b -> Inr b.mb_body)

/// ONE PATH (D-73). This used to branch on `mp_builtin` and dispatch to
/// `expand_if` by name; `if` now carries its templates like everything else,
/// so there is nothing to choose between.
let expand (p:mprod) (caps:list mcap) : Tot (either string (list sterm)) =
  match template_of p caps with
  | Inl e    -> Inl e
  | Inr body -> Inr (subst_terms caps body)

(* ------------------------------------------------------------------------ *)
(* Terms                                                                    *)
(* ------------------------------------------------------------------------ *)

/// Parse terms until `}` (when `closing` is true) or end of input.
/// Measures: `parse_terms` sits above `parse_macro`, which sits above
/// `parse_slots`. Every edge either shortens the token list or drops a rank,
/// and the only same-length edge is a macro handing its own slot list to the
/// slot parser.
///
/// The second conjunct of the refinement is what makes a whole line terminate:
/// at the top level (`closing = false`) the only way to succeed is to reach the
/// end of input, so an unclosed `}` is an error rather than a silent stop. It
/// is what `parse_decl`'s strict progress rests on (D-58).
let rec parse_terms (mt:list mprod) (closing:bool) (acc:list sterm) (ts:list token)
  : Tot (r:presult (list sterm) { POk? r ==> length (POk?._1 r) <= length ts
                                             /\ (not closing ==> Nil? (POk?._1 r)) })
        (decreases %[length ts; 2]) =
  match ts with
  | [] -> if closing
          then PErr "expected '}' closing block, found end of input"
          else POk (rev acc) []
  | TkRBrace :: rest -> if closing
                        then POk (rev acc) rest
                        else PErr "unexpected '}'"
  | TkInt n :: rest -> parse_terms mt closing (StInt n :: acc) rest
  | TkStr s :: rest -> parse_terms mt closing (StStr s :: acc) rest

  /// A word that names a macro invokes it; anything else is an ordinary word.
  /// The expansion is spliced into the enclosing sequence, so a macro's output
  /// composes exactly as if it had been written out by hand.
  /// `handle` is a parser built-in, not a macro (D-38): its implementation
  /// block is a list of `op { … }` pairs, which is not a term list, and the
  /// macro slot vocabulary should not be stretched to cover that before it has
  /// been exercised on the constructs it already fits.
  | TkWord "handle" :: rest ->
    (match parse_handle mt rest with
     | PErr e -> PErr e
     | POk h after -> parse_terms mt closing (h :: acc) after)

  /// `with { old new … } { body }`. Same reason as `handle` for not being a
  /// macro: the rebinding block is a list of name pairs, not a term list.
  | TkWord "with" :: TkLBrace :: r1 ->
    (match parse_rebinds [] r1 with
     | PErr e -> PErr e
     | POk su r2 ->
       (match r2 with
        | TkLBrace :: r3 ->
          (match parse_terms mt true [] r3 with
           | PErr e -> PErr e
           | POk body r4 -> parse_terms mt closing (StWith su body :: acc) r4)
        | _ -> PErr "expected '{' opening the body of a 'with'"))
  | TkWord "with" :: _ ->
    PErr "expected '{ old new … }' after 'with'"

  /// `case { C { … } D { … } else { … } }` (D-90). A parser built-in for the
  /// reason D-38 gives for `handle`, and one more: a macro's production is
  /// fixed when the macro is declared, and a `case`'s branch keys are
  /// constructor names that differ per type — there is no one production to
  /// declare.
  ///
  /// LL(1) with nothing to look ahead at. Inside the body, the token in hand is
  /// `}`, or a word; if it is the word `else` this is the fallback and if it is
  /// any other word it is a constructor. No branch shares a first token.
  | TkWord "case" :: TkLBrace :: r1 ->
    (match parse_case_arms mt [] None r1 with
     | PErr e -> PErr e
     | POk (brs, me) r2 ->
       parse_terms mt closing (StCaseOf brs me :: acc) r2)
  | TkWord "case" :: _ ->
    PErr "expected '{ C { … } … }' after 'case'"

  /// `f[i64]` — an explicit instantiation (D-82). BEFORE the macro branch, and
  /// deliberately: a macro takes its slots from what follows its name, so a
  /// macro called `f` and a generic called `f` would both want this token. The
  /// generic wins because `[` cannot begin any slot, so a macro that lost here
  /// could not have parsed anyway.
  | TkWord w :: TkLBrack :: r1 ->
    (match parse_tyargs [] r1 with
     | PErr e -> PErr e
     | POk tys r2 -> parse_terms mt closing (StWordAt w tys :: acc) r2)

  | TkWord w :: rest ->
    (match lookup_macro mt w with
     | None -> parse_terms mt closing (StWord w :: acc) rest
     | Some p ->
       (match parse_macro mt p rest with
        | PErr e -> PErr e
        | POk caps after ->
          (match expand p caps with
           | Inl e   -> PErr e
           | Inr exp -> parse_terms mt closing (rev exp @ acc) after)))
  | TkDollar n :: rest -> parse_terms mt closing (StVar n :: acc) rest
  | TkLBrace :: rest ->
    (match parse_terms mt true [] rest with
     | PErr e -> PErr e
     | POk inner after -> parse_terms mt closing (StBlock inner :: acc) after)
  | t :: _ -> PErr ("unexpected " ^ render_token t ^ " in a term sequence")

/// Run one macro's production: its fixed slots, then the keyed alternation.
///
/// The alternation reads the token in hand and consumes it — that is LL(1),
/// not lookahead (D-30). With no keyed alternative matching, the error names
/// the keys that would have, which is the whole diagnostic a missing `endif`
/// needs.
and parse_macro (mt:list mprod) (p:mprod) (ts:list token)
  : Tot (r:presult (list mcap) { POk? r ==> length (POk?._1 r) <= length ts })
        (decreases %[length ts; 1]) =
  match parse_slots mt [] p.mp_pre ts with
  | PErr e -> PErr e
  | POk caps after ->
    if Nil? p.mp_branches then POk caps after
    else
      let expected = "expected " ^ key_list p.mp_branches
                     ^ " here, closing '" ^ p.mp_name ^ "'" in
      (match after with
       | TkWord w :: rest ->
         (match lookup_branch p.mp_branches w with
          | None   -> PErr expected
          | Some b ->
            (match parse_slots mt [] b.mb_slots rest with
             | PErr e -> PErr e
             | POk caps2 tail -> POk (caps @ (McKey w :: caps2)) tail))
       | _ -> PErr expected)

/// Consume one slot at a time. Each slot eats at least one token, so a macro
/// cannot spin, and a `}` reached before the slots run out ends the enclosing
/// block rather than being swallowed — macros cannot consume the brace.
/// `handle E over ( t… ) init { … } { op { … } … } { body }`, with the leading
/// `handle` already consumed.
///
/// Every part is keyword-introduced and every bracket is consumed where it
/// appears, so no decision here needs a second token. The shape is fixed rather
/// than optional throughout — a handler with no state still writes
/// `over ( ) init { }` — which is what keeps it LL(1) without reserving
/// `over` or `init` outside this production.
and parse_handle (mt:list mprod) (ts:list token)
  : Tot (r:presult sterm { POk? r ==> length (POk?._1 r) <= length ts })
        (decreases %[length ts; 5]) =
  match ts with
  | TkWord name :: TkWord "over" :: TkLParen :: r1 ->
    (match parse_state_tys [] r1 with
     | PErr e -> PErr e
     | POk tys r2 ->
       (match r2 with
        | TkWord "init" :: TkLBrace :: r3 ->
          (match parse_terms mt true [] r3 with
           | PErr e -> PErr e
           | POk init r4 ->
             (match r4 with
              | TkLBrace :: r5 ->
                (match parse_impls mt [] r5 with
                 | PErr e -> PErr e
                 | POk impls r6 ->
                   (match r6 with
                    | TkLBrace :: r7 ->
                      (match parse_terms mt true [] r7 with
                       | PErr e -> PErr e
                       | POk body r8 ->
                         POk (StHandle name tys init impls body) r8)
                    | _ -> PErr ("expected '{' opening the body handled by "
                                 ^ name)))
              | _ -> PErr ("expected '{' opening the implementations of "
                           ^ name)))
        | _ -> PErr ("expected 'init { … }' after the state of " ^ name)))
  | TkWord name :: _ ->
    PErr ("expected 'over ( … )' after 'handle " ^ name
          ^ "'; a handler with no state writes 'over ( )'")
  | _ -> PErr "expected an effect name after 'handle'"

/// The implementations, up to the closing `}`. Each is `op { … }`.
and parse_impls (mt:list mprod) (acc:list (string & list sterm)) (ts:list token)
  : Tot (r:presult (list (string & list sterm))
         { POk? r ==> length (POk?._1 r) <= length ts })
        (decreases %[length ts; 4]) =
  match ts with
  | TkRBrace :: rest -> POk (rev acc) rest
  | TkWord op :: TkLBrace :: r1 ->
    (match parse_terms mt true [] r1 with
     | PErr e -> PErr e
     | POk blk r2 -> parse_impls mt ((op, blk) :: acc) r2)
  | TkWord op :: _ ->
    PErr ("expected '{' opening the implementation of " ^ op)
  | [] -> PErr "expected '}' closing the implementations, found end of input"
  | t :: _ ->
    PErr ("expected an operation name or '}' here, found " ^ render_token t)

/// A `case`'s branches, up to the closing `}`. Each is `C { … }`, and at most
/// one is `else { … }`.
///
/// `else` is recognised HERE and nowhere else, so it stays an ordinary word
/// outside a `case` — the same rule that lets `then` and `endif` be word names
/// (D-32). Its position among the branches is free: the elaborator works out
/// which variants it covers from the ones that are named, not from order.
and parse_case_arms (mt:list mprod) (acc:list (string & list sterm))
                    (me:option (list sterm)) (ts:list token)
  : Tot (r:presult (list (string & list sterm) & option (list sterm))
         { POk? r ==> length (POk?._1 r) <= length ts })
        (decreases %[length ts; 4]) =
  match ts with
  | TkRBrace :: rest -> POk (rev acc, me) rest
  | TkWord "else" :: TkLBrace :: r1 ->
    if Some? me
    then PErr "a case has at most one 'else'"
    else (match parse_terms mt true [] r1 with
          | PErr e -> PErr e
          | POk blk r2 -> parse_case_arms mt acc (Some blk) r2)
  | TkWord "else" :: _ ->
    PErr "expected '{' opening the 'else' of a case"
  | TkWord c :: TkLBrace :: r1 ->
    (match parse_terms mt true [] r1 with
     | PErr e -> PErr e
     | POk blk r2 -> parse_case_arms mt ((c, blk) :: acc) me r2)
  | TkWord c :: _ ->
    PErr ("expected '{' opening the branch for " ^ c)
  | [] -> PErr "expected '}' closing the case, found end of input"
  | t :: _ ->
    PErr ("expected a constructor name, 'else' or '}' here, found "
          ^ render_token t)

/// The rebindings of a `with`, up to the closing `}`: pairs of plain word
/// names, `replaced` then `replacement`.
and parse_rebinds (acc:list (string & string)) (ts:list token)
  : Tot (r:presult (list (string & string))
         { POk? r ==> length (POk?._1 r) <= length ts })
        (decreases %[length ts; 4]) =
  match ts with
  | TkRBrace :: rest -> POk (rev acc) rest
  | TkWord a :: TkWord b :: r1 -> parse_rebinds ((a, b) :: acc) r1
  | TkWord a :: _ ->
    PErr ("expected a replacement word after '" ^ a ^ "' in this 'with'")
  | [] -> PErr "expected '}' closing the rebindings, found end of input"
  | t :: _ ->
    PErr ("expected a word or '}' here, found " ^ render_token t)

/// The state segment of an `over ( … )`, up to the closing paren. Types only:
/// there is no `--` and no named parameter, because this is one side of a
/// signature rather than a whole one.
and parse_state_tys (acc:list sty) (ts:list token)
  : Tot (r:presult (list sty) { POk? r ==> length (POk?._1 r) <= length ts })
        (decreases %[length ts; 3]) =
  match ts with
  | [] -> PErr "expected ')' closing the handler state, found end of input"
  | TkRParen :: rest -> POk (rev acc) rest
  | _ ->
    (match parse_ty ts with
     | PErr e -> PErr e
     | POk t after ->
       if length after < length ts
       then parse_state_tys (t :: acc) after
       else PErr "handler state made no progress")

and parse_slots (mt:list mprod) (acc:list mcap) (ss:list mslot) (ts:list token)
  : Tot (r:presult (list mcap) { POk? r ==> length (POk?._1 r) <= length ts })
        (decreases %[length ts; 0]) =
  match ss with
  | [] -> POk (rev acc) ts
  | MsBlock n :: sr ->
    (match ts with
     | TkLBrace :: rest ->
       (match parse_terms mt true [] rest with
        | PErr e -> PErr e
        | POk inner after -> parse_slots mt (McBlock n inner :: acc) sr after)
     | _ -> PErr ("expected '{' opening a block for $" ^ n))
  | MsWord n :: sr ->
    (match ts with
     | TkWord w :: rest -> parse_slots mt (McWord n w :: acc) sr rest
     | _ -> PErr ("expected a word for $" ^ n))
  | MsKeyword k :: sr ->
    (match ts with
     | TkWord w :: rest ->
       if w = k then parse_slots mt acc sr rest
       else PErr ("expected '" ^ k ^ "', found '" ^ w ^ "'")
     | _ -> PErr ("expected '" ^ k ^ "' here"))

(* ------------------------------------------------------------------------ *)
(* Declarations                                                             *)
(* ------------------------------------------------------------------------ *)

/// `define name ( sig ) { body }`, or `define name { body }` with the
/// signature inferred (D-31). `define` is already consumed.
///
/// The choice between the two rests on the single token after the name, so
/// this stays LL(1) — no backtracking, no second-token peek (D-30).
/// `[ #T #U ]` after the name (D-79). `[` is self-delimiting, so `f[#T` is
/// already three tokens and the choice between `[`, `(` and `{` after a name is
/// made on the token in hand — LL(1), with nothing to look ahead at (D-30).
let rec parse_tparams (acc:list string) (ts:list token)
  : Tot (r:presult (list string) { POk? r ==> length (POk?._1 r) <= length ts })
        (decreases (length ts)) =
  match ts with
  | TkRBrack :: rest -> if Nil? acc
                        then PErr "a generic needs at least one type parameter, as in define f[#T] ( … )"
                        else POk (rev acc) rest
  | TkHash n :: rest -> parse_tparams (n :: acc) rest
  | t :: _ -> PErr ("expected a type parameter or ']', found " ^ render_token t)
  | [] -> PErr "expected ']' closing the type parameters, found end of input"

let parse_define (mt:list mprod) (ts:list token)
  : Tot (r:presult sdecl { POk? r ==> length (POk?._1 r) <= length ts }) =
  match ts with
  | TkWord name :: TkLBrack :: rest ->
    (match parse_tparams [] rest with
     | PErr e -> PErr e
     | POk ps after ->
       (match after with
        | TkLParen :: rest2 ->
          (match parse_sig_body rest2 with
           | PErr e -> PErr e
           | POk sg after2 ->
             (match after2 with
              | TkLBrace :: body_ts ->
                (match parse_terms mt true [] body_ts with
                 | PErr e -> PErr e
                 | POk body tail -> POk (SdDefineGen name ps sg body) tail)
              | _ -> PErr ("expected '{' opening the body of " ^ name)))
        | _ -> PErr ("expected '(' after the type parameters of " ^ name
                     ^ "; a generic must write its signature")))
  | TkWord name :: TkLParen :: rest ->
    (match parse_sig_body rest with
     | PErr e -> PErr e
     | POk sg after ->
       (match after with
        | TkLBrace :: body_ts ->
          (match parse_terms mt true [] body_ts with
           | PErr e -> PErr e
           | POk body tail -> POk (SdDefine name sg body) tail)
        | _ -> PErr ("expected '{' opening the body of " ^ name)))
  | TkWord name :: TkLBrace :: body_ts ->
    (match parse_terms mt true [] body_ts with
     | PErr e -> PErr e
     | POk body tail -> POk (SdDefineInfer name body) tail)
  | TkWord name :: _ ->
    PErr ("expected '(' or '{' after 'define " ^ name ^ "'")
  | _ -> PErr "expected a name after 'define'"

/// `effect E { declare op ( sig ) … }`, with `effect` already consumed.
///
/// The signature is not optional. An operation has no body, so there is nothing
/// to infer one from — this is where D-31's "mandatory inside an effect
/// declaration" carve-out is actually enforced rather than merely stated.
let rec parse_declares (acc:list (string & ssig)) (ts:list token)
  : Tot (r:presult (list (string & ssig))
         { POk? r ==> length (POk?._1 r) <= length ts })
        (decreases (length ts)) =
  match ts with
  | TkRBrace :: rest -> POk (rev acc) rest
  | TkWord "declare" :: TkWord op :: TkLParen :: r1 ->
    (match parse_sig_body r1 with
     | PErr e -> PErr e
     | POk sg r2 ->
       if length r2 < length ts
       then parse_declares ((op, sg) :: acc) r2
       else PErr "declaration made no progress")
  | TkWord "declare" :: TkWord op :: _ ->
    PErr ("declare " ^ op ^ " needs a signature, as in 'declare " ^ op
          ^ " ( i64 -- i64 )'")
  | TkWord "declare" :: _ -> PErr "expected an operation name after 'declare'"
  | [] -> PErr "expected '}' closing the effect, found end of input"
  | t :: _ ->
    PErr ("expected 'declare' or '}' here, found " ^ render_token t)

/// `extern name ( sig )`. The same shape as one `declare`, because it is the
/// same thing at a different effect (D-66): a word with a signature and no body.
let parse_extern (ts:list token)
  : Tot (r:presult sdecl { POk? r ==> length (POk?._1 r) <= length ts }) =
  match ts with
  | TkWord name :: TkLParen :: r1 ->
    (match parse_sig_body r1 with
     | PErr e   -> PErr e
     | POk sg r2 -> POk (SdExtern name sg) r2)
  | TkWord name :: _ ->
    PErr ("extern " ^ name ^ " needs a signature, as in 'extern " ^ name
          ^ " ( str -- i64 )'")
  | _ -> PErr "expected a name after 'extern'"

let parse_effect (ts:list token)
  : Tot (r:presult sdecl { POk? r ==> length (POk?._1 r) <= length ts }) =
  match ts with
  | TkWord name :: TkLBrace :: rest ->
    (match parse_declares [] rest with
     | PErr e   -> PErr e
     | POk ds r -> POk (SdEffect name ds) r)
  | TkWord name :: _ -> PErr ("expected '{' after 'effect " ^ name ^ "'")
  | _ -> PErr "expected a name after 'effect'"

(* ------------------------------------------------------------------------ *)
(* Type declarations                                                        *)
(* ------------------------------------------------------------------------ *)

/// One variant's payload: types up to `)`, with `(` already consumed.
///
/// Deliberately NOT `parse_sig_body`. A payload is a stack SEGMENT, not a
/// signature: no `--`, no named parameters, no `!Eff` markers. A variant holds
/// values and nothing about holding them can perform.
let rec parse_payload (acc:list sty) (ts:list token)
  : Tot (r:presult (list sty) { POk? r ==> length (POk?._1 r) <= length ts })
        (decreases (length ts)) =
  match ts with
  | [] -> PErr "expected ')' closing a variant's payload, found end of input"
  | TkRParen :: rest -> POk (rev acc) rest
  | _ ->
    (match parse_ty ts with
     | PErr e -> PErr e
     | POk t after ->
       if length after < length ts
       then parse_payload (t :: acc) after
       else PErr "a variant's payload made no progress")

/// `alt C ( tys ) …` up to the closing `}`.
///
/// `alt` is recognised by POSITION — first token of a variant inside a `data`
/// body — so it stays an ordinary word everywhere else, exactly as it already
/// does inside a `macro` declaration (D-32). The two uses never meet.
let rec parse_alts (acc:list (string & list sty)) (ts:list token)
  : Tot (r:presult (list (string & list sty))
         { POk? r ==> length (POk?._1 r) <= length ts })
        (decreases (length ts)) =
  match ts with
  | TkRBrace :: rest ->
    if Nil? acc
    then PErr "a data declaration needs at least one variant, as in \
               'data Color { alt Red ( ) }'"
    else POk (rev acc) rest
  | TkWord "alt" :: TkWord c :: TkLParen :: r1 ->
    (match parse_payload [] r1 with
     | PErr e -> PErr e
     | POk p r2 ->
       if length r2 < length ts
       then parse_alts ((c, p) :: acc) r2
       else PErr "a variant made no progress")
  | TkWord "alt" :: TkWord c :: _ ->
    PErr ("alt " ^ c ^ " needs a payload, as in 'alt " ^ c ^ " ( i64 )'; a \
          variant carrying nothing writes '( )'")
  | TkWord "alt" :: _ -> PErr "expected a constructor name after 'alt'"
  | [] -> PErr "expected 'alt' or '}' closing the declaration, found end of input"
  | t :: _ -> PErr ("expected 'alt' or '}' here, found " ^ render_token t)

/// `data N { alt … }`, or `data N[#T] { alt … }` for a parameterised one
/// (D-89, D-90). `data` is already consumed.
///
/// The choice between the two rests on the single token after the name — `[` or
/// `{` — which is the same LL(1) shape `define` has, and for the same reason:
/// `[` is self-delimiting, so `Option[#T` is already three tokens (D-30).
let parse_data (ts:list token)
  : Tot (r:presult sdecl { POk? r ==> length (POk?._1 r) <= length ts }) =
  match ts with
  | TkWord name :: TkLBrack :: rest ->
    (match parse_tparams [] rest with
     | PErr e -> PErr e
     | POk ps after ->
       (match after with
        | TkLBrace :: r1 ->
          (match parse_alts [] r1 with
           | PErr e    -> PErr e
           | POk vs r2 -> POk (SdData name ps vs) r2)
        | _ -> PErr ("expected '{' after the type parameters of " ^ name)))
  | TkWord name :: TkLBrace :: rest ->
    (match parse_alts [] rest with
     | PErr e    -> PErr e
     | POk vs r2 -> POk (SdData name [] vs) r2)
  | TkWord name :: _ ->
    PErr ("expected '[' or '{' after 'data " ^ name ^ "'")
  | _ -> PErr "expected a name after 'data'"

/// The capability names, which are the language's and not the program's. Two,
/// because `M01.cap` has two; a third would be a change to the core first.
let cap_of_name (s:string) : Tot (option cap) =
  if s = "copy" then Some CCopy else if s = "drop" then Some CDrop else None

/// `cap c`, `pack w`, `unpack w` … up to the closing `}` (D-95).
///
/// Three keyed clauses in any order, accumulated into the record the caller
/// finishes. Keyed by position exactly as `alt` and `declare` are, so `cap`,
/// `pack` and `unpack` stay ordinary word names everywhere else (D-32) — and
/// LL(1) with no ε-branch, since `}` is the only other thing that may appear.
///
/// A repeated `pack` or `unpack` is refused HERE rather than by taking the last
/// one: the clause names the word that will exist, and two names for one
/// operation is a question the declaration has not answered.
let rec parse_seal_body (acc:sseal) (ts:list token)
  : Tot (r:presult sseal { POk? r ==> length (POk?._1 r) <= length ts })
        (decreases (length ts)) =
  match ts with
  | TkRBrace :: rest -> POk ({ acc with sl_caps = rev acc.sl_caps }) rest
  | TkWord "cap" :: TkWord c :: r1 ->
    (match cap_of_name c with
     | None    -> PErr ("unknown capability: " ^ c ^ "; the two are 'copy' and 'drop'")
     | Some cp -> parse_seal_body ({ acc with sl_caps = cp :: acc.sl_caps }) r1)
  | TkWord "cap" :: _ -> PErr "expected 'copy' or 'drop' after 'cap'"
  | TkWord "pack" :: TkWord w :: r1 ->
    if Some? acc.sl_pack
    then PErr ("this seal already names a pack word; " ^ w ^ " would be a second")
    else parse_seal_body ({ acc with sl_pack = Some w }) r1
  | TkWord "pack" :: _ -> PErr "expected a word name after 'pack'"
  | TkWord "unpack" :: TkWord w :: r1 ->
    if Some? acc.sl_unpack
    then PErr ("this seal already names an unpack word; " ^ w ^ " would be a second")
    else parse_seal_body ({ acc with sl_unpack = Some w }) r1
  | TkWord "unpack" :: _ -> PErr "expected a word name after 'unpack'"
  | [] -> PErr "expected 'cap', 'pack', 'unpack' or '}' closing the seal, found \
                end of input"
  | t :: _ ->
    PErr ("expected 'cap', 'pack', 'unpack' or '}' here, found " ^ render_token t)

/// `seal N ( repr ) { … }`, or `seal N[#T] ( repr ) { … }`. `seal` is consumed.
///
/// The representation is `parse_payload`, the same reader a variant uses, and
/// for the same reason: it is a stack SEGMENT — no `--`, no named parameters,
/// no effects. A record's fields and a variant's payload are the same thing
/// laid out the same way, which is D-06 showing through the syntax.
let parse_seal (ts:list token)
  : Tot (r:presult sdecl { POk? r ==> length (POk?._1 r) <= length ts }) =
  let finish (name:string) (ps:list string) (ts:list token)
    : Tot (r:presult sdecl { POk? r ==> length (POk?._1 r) <= length ts }) =
    match ts with
    | TkLParen :: r1 ->
      (match parse_payload [] r1 with
       | PErr e -> PErr e
       | POk repr r2 ->
         (match r2 with
          | TkLBrace :: r3 ->
            (match parse_seal_body ({ sl_name = name; sl_params = ps;
                                      sl_repr = repr; sl_caps = [];
                                      sl_pack = None; sl_unpack = None }) r3 with
             | PErr e    -> PErr e
             | POk sl r4 -> POk (SdSeal sl) r4)
          | _ -> PErr ("expected '{' after the representation of " ^ name)))
    | _ -> PErr ("expected '(' after 'seal " ^ name ^ "'; a sealed type needs a \
                  representation, as in 'seal " ^ name ^ " ( i64 ) { }'") in
  match ts with
  | TkWord name :: TkLBrack :: rest ->
    (match parse_tparams [] rest with
     | PErr e      -> PErr e
     | POk ps after -> finish name ps after)
  | TkWord name :: rest -> finish name [] rest
  | _ -> PErr "expected a name after 'seal'"

(* ------------------------------------------------------------------------ *)
(* Macro declarations                                                       *)
(* ------------------------------------------------------------------------ *)

/// The slot list of a production, up to `)`.
///
///     { $x }   a block slot, spliced at `$x` in the template
///     $x       a word slot, substituted at `$x`
///     w        a literal word that must appear, capturing nothing
///
/// One token decides which, every time: `{`, `$`, a word, or `)`. That is the
/// LL(1) property the macro system is supposed to demonstrate, so the syntax
/// for declaring one had better have it too.
let rec parse_mslots (acc:list mslot) (ts:list token)
  : Tot (r:presult (list mslot) { POk? r ==> length (POk?._1 r) <= length ts })
        (decreases (length ts)) =
  match ts with
  | TkRParen :: rest -> POk (rev acc) rest
  | TkLBrace :: TkDollar n :: TkRBrace :: rest ->
    parse_mslots (MsBlock n :: acc) rest
  | TkLBrace :: _ ->
    PErr "a block slot is written '{ $name }'"
  | TkDollar n :: rest -> parse_mslots (MsWord n :: acc) rest
  | TkWord w :: rest   -> parse_mslots (MsKeyword w :: acc) rest
  | [] -> PErr "expected ')' closing the slots of a macro, found end of input"
  | t :: _ -> PErr ("unexpected " ^ render_token t ^ " in a macro's slots")

/// `alt key ( slots ) { template } … end`.
let rec parse_malts (mt:list mprod) (acc:list mbranch) (ts:list token)
  : Tot (r:presult (list mbranch)
         { POk? r ==> length (POk?._1 r) <= length ts })
        (decreases (length ts)) =
  match ts with
  | TkWord "end" :: rest -> POk (rev acc) rest
  | TkWord "alt" :: TkWord key :: TkLParen :: r1 ->
    (match parse_mslots [] r1 with
     | PErr e -> PErr e
     | POk ss r2 ->
       (match r2 with
        | TkLBrace :: r3 ->
          (match parse_terms mt true [] r3 with
           | PErr e -> PErr e
           | POk body r4 ->
             if length r4 < length ts
             then parse_malts mt ({ mb_key = key; mb_slots = ss; mb_body = body }
                                  :: acc) r4
             else PErr "macro alternative made no progress")
        | _ -> PErr ("expected '{' opening the template of alternative '"
                     ^ key ^ "'")))
  | TkWord "alt" :: TkWord key :: _ ->
    PErr ("expected '(' after 'alt " ^ key ^ "'; a keyed alternative with no \
          slots of its own writes '( )'")
  | TkWord "alt" :: _ -> PErr "expected a key word after 'alt'"
  | [] -> PErr "expected 'alt' or 'end' here, found end of input"
  | t :: _ -> PErr ("expected 'alt' or 'end' here, found " ^ render_token t)

/// `macro name ( slots ) { template }`, or with keyed alternatives:
///
///     macro name ( slots )
///       alt key1 ( slots ) { template }
///       alt key2 ( slots ) { template }
///     end
///
/// `macro` is already consumed. The choice between the two forms rests on the
/// single token after `)` — `{` or `alt` — and `alt` and `end` are keywords
/// only inside this production, so neither is reserved anywhere else.
///
/// THE TEMPLATE IS PARSED AGAINST THE TABLE AS IT STANDS, which has two
/// consequences worth stating. A macro may use macros declared before it, and
/// their expansions are already done by the time it is registered. And a macro
/// cannot use itself, so expansion cannot loop — termination is a property of
/// the declaration order, not a check (D-53).
let parse_macro_decl (mt:list mprod) (ts:list token)
  : Tot (r:presult sdecl { POk? r ==> length (POk?._1 r) <= length ts }) =
  match ts with
  | TkWord name :: TkLParen :: r1 ->
    (match parse_mslots [] r1 with
     | PErr e -> PErr e
     | POk pre r2 ->
       (match r2 with
        | TkLBrace :: r3 ->
          (match parse_terms mt true [] r3 with
           | PErr e -> PErr e
           | POk body r4 ->
             POk (SdMacro ({ mp_name = name; mp_pre = pre; mp_branches = [];
                             mp_body = body })) r4)
        | TkWord "alt" :: _ ->
          (match parse_malts mt [] r2 with
           | PErr e -> PErr e
           | POk bs r4 ->
             POk (SdMacro ({ mp_name = name; mp_pre = pre; mp_branches = bs;
                             mp_body = [] })) r4)
        | _ -> PErr ("expected '{' or 'alt' after the slots of macro " ^ name)))
  | TkWord name :: _ ->
    PErr ("expected '(' after 'macro " ^ name ^ "'; a macro taking nothing \
          writes '( )'")
  | _ -> PErr "expected a name after 'macro'"

(* ------------------------------------------------------------------------ *)
(* Declarations                                                             *)
(* ------------------------------------------------------------------------ *)

/// One declaration. A leading `define` starts a definition, a leading `locate`
/// an inspection; anything else is an expression run to the end of input.
///
/// None of these words is reserved — each is recognised by POSITION, at the
/// start of a declaration, so `define locate { … }` remains legal and a
/// `locate` inside a body is an ordinary word. This is the same rule that keeps
/// `then`, `else` and `endif` free (D-32, D-34).
///
/// STRICT PROGRESS (D-58). A successful parse returns STRICTLY fewer tokens
/// than it was given. This is what makes evaluating a line terminate, and it
/// has to be a theorem rather than an observation because a `macro` declaration
/// changes the grammar the rest of the line is read with (D-54) — the session
/// cannot appeal to one fixed grammar to argue that it advances.
///
/// The keyword-led forms consume their keyword, so `<=` on what follows
/// suffices. The expression form gets it from `parse_terms`'s second conjunct:
/// at the top level the only way to succeed is to reach the end of input, so
/// the remainder is `[]`. End of input is now an error rather than an empty
/// expression, which is what makes the statement unconditional.
///
/// `E06.eval_tokens` used to check this at RUNTIME and stop the line if it
/// failed. That check is gone; this refinement replaced it.
let parse_decl (mt:list mprod) (ts:list token)
  : Tot (r:presult sdecl { POk? r ==> length (POk?._1 r) < length ts }) =
  match ts with
  | [] -> PErr "expected a declaration, found end of input"
  | TkWord "define" :: rest -> parse_define mt rest
  | TkWord "effect" :: rest -> parse_effect rest
  | TkWord "data"   :: rest -> parse_data rest
  | TkWord "seal"   :: rest -> parse_seal rest
  | TkWord "extern" :: rest -> parse_extern rest
  | TkWord "macro"  :: rest -> parse_macro_decl mt rest
  | TkWord "locate" :: TkWord name :: rest -> POk (SdLocate name) rest
  | TkWord "locate" :: _ -> PErr "expected a word after 'locate'"
  | _ ->(match parse_terms mt false [] ts with
          | PErr e -> PErr e
          | POk body tail -> POk (SdExpr body) tail)

/// Lex a whole source string. Parsing is NOT done here any more: a `macro`
/// declaration changes the grammar the rest of the input is read with, so the
/// session parses one declaration at a time, evaluating as it goes (D-54).
let lex_line (src:string) : Tot (either string (list token)) = lex src
