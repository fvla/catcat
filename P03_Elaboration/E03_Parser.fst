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
/// STATUS: the table is built in, with `if` its only entry. User-defined
/// macros — registration from catcat source, via the `Parse` effect of D03 §7
/// — are what this exists for, and need the elaboration-time interpreter.
type mslot =
  /// `{ … }`, captured as its term list.
  | MsBlock   : mslot
  /// One identifier, captured as a string.
  | MsWord    : mslot
  /// A literal word that must appear. Consumed, captures nothing.
  | MsKeyword : string -> mslot

/// What a slot captured. A branch key is recorded as `McWord` so the expander
/// can tell which alternative was taken.
noeq type mcap =
  | McBlock : list sterm -> mcap
  | McWord  : string -> mcap

type mbranch = {
  /// The word that selects this alternative. Consumed.
  mb_key   : string;
  mb_slots : list mslot;
}

noeq type mprod = {
  /// The leading word that invokes the macro.
  mp_name     : string;
  /// Slots consumed before the alternation.
  mp_pre      : list mslot;
  /// Keyed alternatives. Empty means the production ends after `mp_pre`.
  mp_branches : list mbranch;
}

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

/// `Box[i64]` / `Rc[i64]` use the generic brackets; anything else is a name.
let rec parse_ty (ts:list token)
  : Tot (r:presult sty { POk? r ==> length (POk?._1 r) <= length ts })
        (decreases (length ts)) =
  match ts with
  | [] -> PErr "expected a type, found end of input"
  | TkHash n :: rest -> POk (StyVar n) rest
  | TkWord w :: rest ->
    if w = "Box" || w = "Rc" then
      (match rest with
       | TkLBrack :: inner ->
         (match parse_ty inner with
          | PErr e -> PErr e
          | POk t after ->
            (match after with
             | TkRBrack :: tail -> POk (if w = "Box" then StyBox t else StyRc t) tail
             | _ -> PErr ("expected ']' closing " ^ w)))
       | _ -> PErr (w ^ " needs a type argument, as in " ^ w ^ "[i64]"))
    else POk (StyName w) rest
  | t :: _ -> PErr ("expected a type, found " ^ render_token t)

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

/// A whole `( … -- … )`, with the opening paren already consumed.
let parse_sig_body (ts:list token)
  : Tot (r:presult ssig { POk? r ==> length (POk?._1 r) <= length ts }) =
  match parse_inputs [] ts with
  | PErr e -> PErr e
  | POk ins after ->
    (match parse_outputs [] [] after with
     | PErr e -> PErr e
     | POk (outs, effs) tail ->
       POk ({ ss_in = ins; ss_out = outs; ss_eff = effs }) tail)

(* ------------------------------------------------------------------------ *)
(* The macro table                                                          *)
(* ------------------------------------------------------------------------ *)

/// `if { c } then { t } endif`, or with an `else { e }` before the terminator.
///
/// The terminator is mandatory and both alternatives are keyed, which is what
/// keeps `then`, `else` and `endif` ordinary word names outside this
/// production (D-34). Verified: they are all still definable.
let macro_table : list mprod = [
  { mp_name     = "if";
    mp_pre      = [MsBlock; MsKeyword "then"; MsBlock];
    mp_branches = [ { mb_key = "endif"; mb_slots = [] };
                    { mb_key = "else";  mb_slots = [MsBlock; MsKeyword "endif"] } ] }
]

/// The table really is LL(1), checked rather than asserted in prose.
let lemma_table_ll1 () : Lemma (ll1_ok macro_table) =
  assert_norm (ll1_ok macro_table)

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

(* --- expansion ----------------------------------------------------------- *)

/// Expanders dispatch on the macro's name rather than living in `mprod` as a
/// field. That is not a style choice: a function-typed record field would
/// break the first-order subset P03 shares with P02 (D-20), so the dispatch is
/// defunctionalised exactly as `R02` defunctionalises continuations.
///
/// Branches are emitted in TAG order, FALSE first (D-33), so `else` precedes
/// `then`. An absent `else` is `[]` — the empty branch — which is why "the
/// `then` branch must not change the stack" needs no rule of its own.
let expand_if (caps:list mcap) : Tot (either string (list sterm)) =
  match caps with
  | [McBlock cond; McBlock conseq; McWord "endif"] ->
    Inr (cond @ [StCase [[]; conseq]])
  | [McBlock cond; McBlock conseq; McWord "else"; McBlock alt] ->
    Inr (cond @ [StCase [alt; conseq]])
  | _ -> Inl "if: malformed expansion"

let expand (name:string) (caps:list mcap) : Tot (either string (list sterm)) =
  if name = "if" then expand_if caps
  else Inl ("no expander for macro '" ^ name ^ "'")

(* ------------------------------------------------------------------------ *)
(* Terms                                                                    *)
(* ------------------------------------------------------------------------ *)

/// Parse terms until `}` (when `closing` is true) or end of input.
/// Measures: `parse_terms` sits above `parse_macro`, which sits above
/// `parse_slots`. Every edge either shortens the token list or drops a rank,
/// and the only same-length edge is a macro handing its own slot list to the
/// slot parser.
let rec parse_terms (closing:bool) (acc:list sterm) (ts:list token)
  : Tot (r:presult (list sterm) { POk? r ==> length (POk?._1 r) <= length ts })
        (decreases %[length ts; 2]) =
  match ts with
  | [] -> if closing
          then PErr "expected '}' closing block, found end of input"
          else POk (rev acc) []
  | TkRBrace :: rest -> if closing
                        then POk (rev acc) rest
                        else PErr "unexpected '}'"
  | TkInt n :: rest -> parse_terms closing (StInt n :: acc) rest

  /// A word that names a macro invokes it; anything else is an ordinary word.
  /// The expansion is spliced into the enclosing sequence, so a macro's output
  /// composes exactly as if it had been written out by hand.
  /// `handle` is a parser built-in, not a macro (D-38): its implementation
  /// block is a list of `op { … }` pairs, which is not a term list, and the
  /// macro slot vocabulary should not be stretched to cover that before it has
  /// been exercised on the constructs it already fits.
  | TkWord "handle" :: rest ->
    (match parse_handle rest with
     | PErr e -> PErr e
     | POk h after -> parse_terms closing (h :: acc) after)

  | TkWord w :: rest ->
    (match lookup_macro macro_table w with
     | None -> parse_terms closing (StWord w :: acc) rest
     | Some p ->
       (match parse_macro p rest with
        | PErr e -> PErr e
        | POk caps after ->
          (match expand w caps with
           | Inl e   -> PErr e
           | Inr exp -> parse_terms closing (rev exp @ acc) after)))
  | TkDollar n :: rest -> parse_terms closing (StVar n :: acc) rest
  | TkLBrace :: rest ->
    (match parse_terms true [] rest with
     | PErr e -> PErr e
     | POk inner after -> parse_terms closing (StBlock inner :: acc) after)
  | t :: _ -> PErr ("unexpected " ^ render_token t ^ " in a term sequence")

/// Run one macro's production: its fixed slots, then the keyed alternation.
///
/// The alternation reads the token in hand and consumes it — that is LL(1),
/// not lookahead (D-30). With no keyed alternative matching, the error names
/// the keys that would have, which is the whole diagnostic a missing `endif`
/// needs.
and parse_macro (p:mprod) (ts:list token)
  : Tot (r:presult (list mcap) { POk? r ==> length (POk?._1 r) <= length ts })
        (decreases %[length ts; 1]) =
  match parse_slots [] p.mp_pre ts with
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
            (match parse_slots [] b.mb_slots rest with
             | PErr e -> PErr e
             | POk caps2 tail -> POk (caps @ (McWord w :: caps2)) tail))
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
and parse_handle (ts:list token)
  : Tot (r:presult sterm { POk? r ==> length (POk?._1 r) <= length ts })
        (decreases %[length ts; 5]) =
  match ts with
  | TkWord name :: TkWord "over" :: TkLParen :: r1 ->
    (match parse_state_tys [] r1 with
     | PErr e -> PErr e
     | POk tys r2 ->
       (match r2 with
        | TkWord "init" :: TkLBrace :: r3 ->
          (match parse_terms true [] r3 with
           | PErr e -> PErr e
           | POk init r4 ->
             (match r4 with
              | TkLBrace :: r5 ->
                (match parse_impls [] r5 with
                 | PErr e -> PErr e
                 | POk impls r6 ->
                   (match r6 with
                    | TkLBrace :: r7 ->
                      (match parse_terms true [] r7 with
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
and parse_impls (acc:list (string & list sterm)) (ts:list token)
  : Tot (r:presult (list (string & list sterm))
         { POk? r ==> length (POk?._1 r) <= length ts })
        (decreases %[length ts; 4]) =
  match ts with
  | TkRBrace :: rest -> POk (rev acc) rest
  | TkWord op :: TkLBrace :: r1 ->
    (match parse_terms true [] r1 with
     | PErr e -> PErr e
     | POk blk r2 -> parse_impls ((op, blk) :: acc) r2)
  | TkWord op :: _ ->
    PErr ("expected '{' opening the implementation of " ^ op)
  | [] -> PErr "expected '}' closing the implementations, found end of input"
  | t :: _ ->
    PErr ("expected an operation name or '}' here, found " ^ render_token t)

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

and parse_slots (acc:list mcap) (ss:list mslot) (ts:list token)
  : Tot (r:presult (list mcap) { POk? r ==> length (POk?._1 r) <= length ts })
        (decreases %[length ts; 0]) =
  match ss with
  | [] -> POk (rev acc) ts
  | MsBlock :: sr ->
    (match ts with
     | TkLBrace :: rest ->
       (match parse_terms true [] rest with
        | PErr e -> PErr e
        | POk inner after -> parse_slots (McBlock inner :: acc) sr after)
     | _ -> PErr "expected '{' opening a block here")
  | MsWord :: sr ->
    (match ts with
     | TkWord w :: rest -> parse_slots (McWord w :: acc) sr rest
     | _ -> PErr "expected a word here")
  | MsKeyword k :: sr ->
    (match ts with
     | TkWord w :: rest ->
       if w = k then parse_slots acc sr rest
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
let parse_define (ts:list token) : Tot (presult sdecl) =
  match ts with
  | TkWord name :: TkLParen :: rest ->
    (match parse_sig_body rest with
     | PErr e -> PErr e
     | POk sg after ->
       (match after with
        | TkLBrace :: body_ts ->
          (match parse_terms true [] body_ts with
           | PErr e -> PErr e
           | POk body tail -> POk (SdDefine name sg body) tail)
        | _ -> PErr ("expected '{' opening the body of " ^ name)))
  | TkWord name :: TkLBrace :: body_ts ->
    (match parse_terms true [] body_ts with
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
  : Tot (presult (list (string & ssig))) (decreases (length ts)) =
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

let parse_effect (ts:list token) : Tot (presult sdecl) =
  match ts with
  | TkWord name :: TkLBrace :: rest ->
    (match parse_declares [] rest with
     | PErr e   -> PErr e
     | POk ds r -> POk (SdEffect name ds) r)
  | TkWord name :: _ -> PErr ("expected '{' after 'effect " ^ name ^ "'")
  | _ -> PErr "expected a name after 'effect'"

/// One declaration. A leading `define` starts a definition, a leading `locate`
/// an inspection; anything else is an expression run to the end of input.
///
/// Neither word is reserved — both are recognised by POSITION, at the start of
/// a declaration, so `define locate { … }` remains legal and a `locate` inside
/// a body is an ordinary word. This is the same rule that keeps `then`, `else`
/// and `endif` free (D-32, D-34).
let parse_decl (ts:list token) : Tot (presult sdecl) =
  match ts with
  | TkWord "define" :: rest -> parse_define rest
  | TkWord "effect" :: rest -> parse_effect rest
  | TkWord "locate" :: TkWord name :: rest -> POk (SdLocate name) rest
  | TkWord "locate" :: _ -> PErr "expected a word after 'locate'"
  | _ ->(match parse_terms false [] ts with
          | PErr e -> PErr e
          | POk body tail -> POk (SdExpr body) tail)

let rec parse_decls (acc:list sdecl) (ts:list token)
  : Tot (either string (list sdecl)) (decreases (length ts)) =
  match ts with
  | [] -> Inr (rev acc)
  | _ ->
    (match parse_decl ts with
     | PErr e -> Inl e
     | POk d rest ->
       if length rest < length ts
       then parse_decls (d :: acc) rest
       else Inr (rev (d :: acc)))

/// Lex and parse a whole source string.
let parse (src:string) : Tot (either string (list sdecl)) =
  match lex src with
  | Inl e   -> Inl e
  | Inr tks -> parse_decls [] tks
