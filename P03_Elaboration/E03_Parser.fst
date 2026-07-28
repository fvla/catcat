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
(* Terms                                                                    *)
(* ------------------------------------------------------------------------ *)

/// Parse terms until `}` (when `closing` is true) or end of input.
let rec parse_terms (closing:bool) (acc:list sterm) (ts:list token)
  : Tot (r:presult (list sterm) { POk? r ==> length (POk?._1 r) <= length ts })
        (decreases (length ts)) =
  match ts with
  | [] -> if closing
          then PErr "expected '}' closing block, found end of input"
          else POk (rev acc) []
  | TkRBrace :: rest -> if closing
                        then POk (rev acc) rest
                        else PErr "unexpected '}'"
  | TkInt n :: rest -> parse_terms closing (StInt n :: acc) rest

  /// `if { c } then { t } endif` and `if { c } then { t } else { e } endif`.
  ///
  /// **The terminator is mandatory** (D-34). Every alternation point here
  /// consumes a keyword — after the `then` block the next token must be
  /// `else` or `endif`, and both are eaten — so the grammar has no ε-branch
  /// and nothing needs reserving. `then`, `else` and `endif` remain ordinary
  /// word names everywhere except inside this production, which is what keeps
  /// D-32's free-form words intact.
  ///
  /// The condition block runs inline, so its terms are spliced into the
  /// enclosing sequence ahead of the case. Branches are emitted in TAG order,
  /// FALSE first (D-33), so the `else` branch precedes the `then` branch — an
  /// else-less `if` is `else { }`, which is why "the then branch must not
  /// change the stack" needs no separate rule.
  ///
  /// Hardcoded here for now. It moves into the macro table when that exists;
  /// this production is what the table has to be able to express.
  | TkWord "if" :: TkLBrace :: r1 ->
    (match parse_terms true [] r1 with
     | PErr e -> PErr e
     | POk cond r2 ->
       (match r2 with
        | TkWord "then" :: TkLBrace :: r3 ->
          (match parse_terms true [] r3 with
           | PErr e -> PErr e
           | POk conseq r4 ->
             (match r4 with
              | TkWord "endif" :: r5 ->
                parse_terms closing
                  (StCase [[]; conseq] :: (rev cond @ acc)) r5
              | TkWord "else" :: TkLBrace :: r5 ->
                (match parse_terms true [] r5 with
                 | PErr e -> PErr e
                 | POk alt r6 ->
                   (match r6 with
                    | TkWord "endif" :: r7 ->
                      parse_terms closing
                        (StCase [alt; conseq] :: (rev cond @ acc)) r7
                    | _ -> PErr "expected 'endif' closing this if"))
              | TkWord "else" :: _ -> PErr "expected '{' after 'else'"
              | _ -> PErr "expected 'else' or 'endif' after the 'then' block"))
        | TkWord "then" :: _ -> PErr "expected '{' after 'then'"
        | _ -> PErr "expected 'then' after the condition block of an if"))
  | TkWord "if" :: _ ->
    PErr "expected '{' after 'if': the condition is a block, as in \
          if { 0 < } then { … } endif"

  | TkWord w :: rest -> parse_terms closing (StWord w :: acc) rest
  | TkDollar n :: rest -> parse_terms closing (StVar n :: acc) rest
  | TkLBrace :: rest ->
    (match parse_terms true [] rest with
     | PErr e -> PErr e
     | POk inner after -> parse_terms closing (StBlock inner :: acc) after)
  | t :: _ -> PErr ("unexpected " ^ render_token t ^ " in a term sequence")

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

/// One declaration. A leading `define` starts a definition; anything else is
/// an expression run to the end of input.
let parse_decl (ts:list token) : Tot (presult sdecl) =
  match ts with
  | TkWord "define" :: rest -> parse_define rest
  | _ -> (match parse_terms false [] ts with
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
