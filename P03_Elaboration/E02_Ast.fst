module E02_Ast

/// P03, module 02: the surface syntax tree.
///
/// SUMMARY
///   What the parser produces and the elaborator consumes. Deliberately close
///   to the source text: names are still strings, the stack order is still the
///   surface order, and locals are still named.
///
/// The gap between this and `M05_Terms.term` is exactly what E04 closes:
///   * names resolve to `word_id`s,
///   * signature order reverses (surface bottom-to-top, core head-is-top),
///   * `$x` locals become `SPick`/`SRoll` stack access.
///
/// SCOPE OF THIS PASS
///   Literals, words, blocks, signatures with named parameters, `define`,
///   effects and handlers, `with`, and macro productions. Deliberately absent,
///   each already specified in D05 and each needing its own pass: modules and
///   `::`, generics `[]`, sums and classes, strings, `let` destructuring, and
///   `.` member access.
///
///   Macros are here rather than in the parser because `macro` is a
///   DECLARATION now: a production is something a program writes, so `mprod`
///   is part of the syntax tree.

open FStar.List.Tot

(* ------------------------------------------------------------------------ *)
/// Surface types                                                           *)
(* ------------------------------------------------------------------------ *)

/// `sty_name` covers both primitives (`i64`) and nominal references; the
/// elaborator decides which by looking the name up. Keeping them one case here
/// means the parser needs no type table.
type sty =
  | StyName : string -> sty
  | StyBox  : sty -> sty
  | StyRc   : sty -> sty
  /// `#T` — a parametric type variable. Parsed and rejected by E04 for now;
  /// present so generics do not require an AST change.
  | StyVar  : string -> sty

let rec sty_size (t:sty) : Tot pos =
  match t with
  | StyName _ -> 1
  | StyVar _  -> 1
  | StyBox u  -> 1 + sty_size u
  | StyRc u   -> 1 + sty_size u

(* ------------------------------------------------------------------------ *)
(* Signatures                                                               *)
(* ------------------------------------------------------------------------ *)

/// One input slot. `sp_name` is `Some` for `$x:i64`, `None` for a bare `i64`.
type sparam = {
  sp_name : option string;
  sp_ty   : sty;
}

/// A surface signature, in SOURCE order: bottom of stack first, top on the
/// right. `( i64 bool -- i64 )` has `bool` on top. E04 reverses this.
/// THREE MODES OF SPECIFICATION (D-77), and `ss_eff` is what carries the
/// difference between the last two:
///
///   `define f { … }`                 nothing written — infer both
///   `define f ( i64 -- i64 ) { … }`  stack written, effects inferred
///   `define f ( i64 -- i64 !IO ) { … }`   both written, both checked
///
/// So the effect list has to distinguish ABSENT from EMPTY, which a `list
/// string` cannot: `[]` meant "no effects" and there was no way to say "not
/// written". Writing a stack signature therefore forced you to enumerate every
/// effect the body could reach, and a bare `( i64 -- i64 )` asserted purity
/// whether or not you meant to.
///
///   `None`      no `!` appeared; infer the row and check nothing.
///   `Some []`   a bare `!` appeared; the row is asserted EMPTY.
///   `Some ns`   named effects; the row is asserted to be exactly those.
///
/// The bare `!` is the sigil with its name deliberately absent, which is the
/// one spelling that cannot be confused with an effect — every effect has a
/// name. `!Pure` would read better and would be worse: it sits where effect
/// names sit, so it would have to be a name that is not an effect, reserved
/// against `effect Pure { … }`, and exempt from the propagation every other
/// entry in that position obeys.
type ssig = {
  ss_in   : list sparam;
  ss_out  : list sty;
  ss_eff  : option (list string);
}

(* ------------------------------------------------------------------------ *)
(* Terms                                                                    *)
(* ------------------------------------------------------------------------ *)

type sterm =
  | StInt   : int -> sterm
  /// A double-quoted literal (D-65). Carries the DECODED text: escapes are
  /// resolved in `E01`, so nothing downstream re-interprets a backslash.
  | StStr   : string -> sterm
  | StWord  : string -> sterm
  /// `$x` — a read of a named local.
  | StVar   : string -> sterm
  /// `{ … }` — a block. Currently a `define` body or a branch of `StCase`;
  /// handler and macro consumers arrive with those features.
  | StBlock : list sterm -> sterm
  /// Case analysis: one branch per variant of the sum on top of the stack.
  ///
  /// This is the surface form macros target, not a form anyone writes directly
  /// yet — surface `if` expands to it (D-33). Branches are listed in TAG
  /// order, so for a `bool` the FALSE branch comes first. Stated here as well
  /// as in `M05.PBoolSum` because a silent reversal would typecheck.
  | StCase  : list (list sterm) -> sterm
  /// `handle E over ( … ) init { … } { op { … } … } { body }`.
  ///
  /// The state segment is in SURFACE order (bottom-to-top); `E04` reverses it,
  /// as it does every signature. Implementations are keyed by operation name,
  /// resolved against the effect named here.
  | StHandle : string -> list sty -> list sterm
             -> list (string & list sterm) -> list sterm -> sterm
  /// `with { old new … } { body }` — run `body` with words rebound.
  ///
  /// Static by default (D-37): the rebinding is discharged during elaboration
  /// and leaves nothing in the core term, so it costs exactly nothing. The
  /// pairs are `(replaced, replacement)`, both plain word names.
  | StWith   : list (string & string) -> list sterm -> sterm
  /// `try { … } catch { … }` — run the first block, and if it aborts, run the
  /// second instead (D-71).
  ///
  /// THE TRY BLOCK RUNS ON A FRESH STACK, like a handler's initialiser and
  /// unlike its body. `M05.TTry` carries the body's `pre` so the machine knows
  /// how far to cut back on an abort, and the elaborator's shape model cannot
  /// compute it: the model is a concrete stack, so it knows what the body LEFT
  /// but not how deep the body reached. Over-approximating to the whole
  /// modelled stack — which is what `StCase` does for its declarations, safely
  /// — would here make `catch` responsible for rebuilding the caller's entire
  /// stack. So the body gets `pre = []` and E04 elaborates it against `[]`,
  /// which reports an honest "the stack is empty" for a body that reaches out.
  | StTry    : list sterm -> list sterm -> sterm

let rec sterm_size (t:sterm) : Tot pos =
  match t with
  | StInt _    -> 1
  | StStr _    -> 1
  | StWord _   -> 1
  | StVar _    -> 1
  | StBlock ts -> 1 + sterms_size ts
  | StCase bs  -> 1 + sterm_lists_size bs
  | StHandle _ _ i im b -> 1 + sterms_size i + simpls_size im + sterms_size b
  | StWith _ b -> 1 + sterms_size b
  | StTry b c  -> 1 + sterms_size b + sterms_size c

and sterms_size (ts:list sterm) : Tot nat =
  match ts with
  | []     -> 0
  | t :: r -> sterm_size t + sterms_size r

/// One charged per implementation, for the same reason `sterm_lists_size`
/// charges one per branch: an empty implementation block is legitimate
/// (`reset { }` on a unit state) and would otherwise make the measure
/// non-strict on the list-to-list edge.
and simpls_size (im:list (string & list sterm)) : Tot nat =
  match im with
  | []           -> 0
  | (_, ts) :: r -> 1 + sterms_size ts + simpls_size r

/// Note the `1 +` per branch. Without it an EMPTY branch — `else { }`, which
/// is exactly the shape the else-less `if` expands to — makes this measure
/// non-strict on the list-to-list edge, and the rank trick used elsewhere in
/// the project does not rescue it because both sides sit at the same rank.
/// Charging one for each branch restores a strict decrease on the first
/// component, so the ranks below are documentation rather than load-bearing.
and sterm_lists_size (bs:list (list sterm)) : Tot nat =
  match bs with
  | []     -> 0
  | b :: r -> 1 + sterms_size b + sterm_lists_size r

(* ------------------------------------------------------------------------ *)
(* Macros                                                                   *)
(* ------------------------------------------------------------------------ *)

/// A MACRO IS A GRAMMAR PRODUCTION PLUS A TEMPLATE (D-35).
///
/// It declares what it consumes to its right — a fixed sequence of slots, then
/// optionally an alternation keyed on a literal word — and the surface terms to
/// put in its place, with each slot's capture substituted for `$name`.
///
/// These types live in the AST rather than in the parser because a macro
/// declaration is now something a program WRITES, so `mprod` is part of the
/// syntax tree and not merely a parser table.
type mslot =
  /// `{ $x }` — a block, captured as its term list and spliced at `$x`.
  | MsBlock   : string -> mslot
  /// `$x` — one identifier, captured as a word.
  | MsWord    : string -> mslot
  /// A literal word that must appear. Consumed, captures nothing.
  | MsKeyword : string -> mslot

/// What a slot captured, tagged with the name it is bound to. `McKey` records
/// which alternative was taken and binds nothing — a macro dispatches on the
/// key by having a separate template per branch, so it never needs to read it.
noeq type mcap =
  | McBlock : string -> list sterm -> mcap
  | McWord  : string -> string -> mcap
  | McKey   : string -> mcap

type mbranch = {
  /// The word that selects this alternative. Consumed.
  mb_key   : string;
  mb_slots : list mslot;
  mb_body  : list sterm;
}

type mprod = {
  /// The leading word that invokes the macro.
  mp_name     : string;
  /// Slots consumed before the alternation.
  mp_pre      : list mslot;
  /// Keyed alternatives. Empty means the production ends after `mp_pre`, and
  /// `mp_body` is the template.
  mp_branches : list mbranch;
  mp_body     : list sterm;
}

(* --- hygiene -------------------------------------------------------------- *)

/// MACRO HYGIENE IS A WELL-FORMEDNESS CHECK, NOT A RENAMING PASS (D-73).
///
/// The usual hygiene problem is that a template's own temporaries capture, or
/// are captured by, names at the use site, and the usual fix is to rename them
/// apart. Neither applies here, and the reason is a property of the surface
/// language worth stating: **no `sterm` binds a local.** `$x` is a READ; the
/// only binder in the language is a signature parameter, and a signature
/// appears in a declaration, while a macro body is a term list.
///
/// So a `$x` in a template naming no slot of the production cannot be a
/// temporary the author introduced — there is no way to introduce one. It can
/// only be a read of whatever local encloses the expansion, which the author of
/// a macro is in no position to have meant. Renaming it apart would produce a
/// read of nothing, failing later and further away.
///
/// Hygiene therefore reduces to rejecting it at DECLARATION time, which is
/// strictly better than gensym: the error names the macro rather than the call.
/// When `let` arrives (D05 §3.3) a template will be able to bind, and this
/// becomes a genuine renaming problem; until then the check is the whole of it.
let slot_name (s:mslot) : Tot (option string) =
  match s with
  | MsBlock n   -> Some n
  | MsWord n    -> Some n
  | MsKeyword _ -> None

let rec slot_names (ss:list mslot) : Tot (list string) (decreases ss) =
  match ss with
  | []     -> []
  | s :: r -> (match slot_name s with
               | Some n -> n :: slot_names r
               | None   -> slot_names r)

/// The first `$x` in a template that names no slot, or `None`. Returns the name
/// rather than a boolean so the diagnostic can quote it — "the grammar would be
/// ambiguous" is a verdict, and so is "this macro is unhygienic".
let rec stray_var (ok:list string) (t:sterm)
  : Tot (option string) (decreases %[(sterm_size t <: nat); 0]) =
  match t with
  | StVar x    -> if mem x ok then None else Some x
  | StBlock ts -> stray_var_list ok ts
  | StCase bs  -> stray_var_lists ok bs
  | StHandle _ _ i im b ->
    (match stray_var_list ok i with
     | Some x -> Some x
     | None   -> (match stray_var_impls ok im with
                  | Some x -> Some x
                  | None   -> stray_var_list ok b))
  | StWith _ b -> stray_var_list ok b
  | StTry b c  -> (match stray_var_list ok b with
                   | Some x -> Some x
                   | None   -> stray_var_list ok c)
  | _          -> None

and stray_var_list (ok:list string) (ts:list sterm)
  : Tot (option string) (decreases %[sterms_size ts; 1]) =
  match ts with
  | []     -> None
  | t :: r -> (match stray_var ok t with
               | Some x -> Some x
               | None   -> stray_var_list ok r)

and stray_var_lists (ok:list string) (bs:list (list sterm))
  : Tot (option string) (decreases %[sterm_lists_size bs; 1]) =
  match bs with
  | []     -> None
  | b :: r -> (match stray_var_list ok b with
               | Some x -> Some x
               | None   -> stray_var_lists ok r)

and stray_var_impls (ok:list string) (im:list (string & list sterm))
  : Tot (option string) (decreases %[simpls_size im; 1]) =
  match im with
  | []          -> None
  | (_, b) :: r -> (match stray_var_list ok b with
                    | Some x -> Some x
                    | None   -> stray_var_impls ok r)

/// A branch's template may read the production's leading slots as well as its
/// own, since both are in scope by the time it expands.
let rec stray_in_branches (pre:list string) (bs:list mbranch)
  : Tot (option string) (decreases bs) =
  match bs with
  | []     -> None
  | b :: r -> (match stray_var_list (slot_names b.mb_slots @ pre) b.mb_body with
               | Some x -> Some x
               | None   -> stray_in_branches pre r)

let mprod_stray (p:mprod) : Tot (option string) =
  let pre = slot_names p.mp_pre in
  match stray_var_list pre p.mp_body with
  | Some x -> Some x
  | None   -> stray_in_branches pre p.mp_branches

(* --- template substitution ----------------------------------------------- *)

let rec cap_of (caps:list mcap) (x:string) : Tot (option mcap) (decreases caps) =
  match caps with
  | []                -> None
  | McBlock n ts :: r -> if n = x then Some (McBlock n ts) else cap_of r x
  | McWord n w :: r   -> if n = x then Some (McWord n w)   else cap_of r x
  | McKey _ :: r      -> cap_of r x

/// Instantiate a template. Each term expands to a LIST, because a block slot
/// splices its contents rather than nesting them — `{ $b $b }` with `$b` bound
/// to `1 +` gives `1 + 1 +`, not two blocks.
///
/// A `$x` naming no slot is left alone HERE, and cannot arrive: `mprod_stray`
/// above rejects such a template when the macro is declared (D-73). This
/// function is therefore total on well-formed input in a stronger sense than
/// its type says, and the fallthrough is retained rather than refined because
/// the refinement would have to travel through `subst_terms`, `subst_lists` and
/// `subst_impls` for one caller.
let rec subst_term (caps:list mcap) (t:sterm)
  : Tot (list sterm) (decreases %[(sterm_size t <: nat); 0]) =
  match t with
  | StVar x -> (match cap_of caps x with
                | Some (McBlock _ inner) -> inner
                | Some (McWord _ w)      -> [StWord w]
                | _                      -> [StVar x])
  | StBlock ts            -> [StBlock (subst_terms caps ts)]
  | StCase bs             -> [StCase (subst_lists caps bs)]
  | StHandle e tys i im b -> [StHandle e tys (subst_terms caps i)
                                       (subst_impls caps im) (subst_terms caps b)]
  | StWith su b           -> [StWith su (subst_terms caps b)]
  | StTry b c             -> [StTry (subst_terms caps b) (subst_terms caps c)]
  | _                     -> [t]

and subst_terms (caps:list mcap) (ts:list sterm)
  : Tot (list sterm) (decreases %[sterms_size ts; 1]) =
  match ts with
  | []     -> []
  | t :: r -> subst_term caps t @ subst_terms caps r

and subst_lists (caps:list mcap) (bs:list (list sterm))
  : Tot (list (list sterm)) (decreases %[sterm_lists_size bs; 2]) =
  match bs with
  | []     -> []
  | b :: r -> subst_terms caps b :: subst_lists caps r

and subst_impls (caps:list mcap) (im:list (string & list sterm))
  : Tot (list (string & list sterm)) (decreases %[simpls_size im; 2]) =
  match im with
  | []           -> []
  | (o, ts) :: r -> (o, subst_terms caps ts) :: subst_impls caps r

(* ------------------------------------------------------------------------ *)
(* Declarations                                                             *)
(* ------------------------------------------------------------------------ *)

type sdecl =
  /// `define name ( sig ) { body }`
  | SdDefine      : string -> ssig -> list sterm -> sdecl
  /// `define name { body }` — signature inferred from the body (D-31).
  | SdDefineInfer : string -> list sterm -> sdecl
  /// `effect E { declare op ( sig ) … }`.
  ///
  /// Signatures are MANDATORY here, which is where D-31's carve-out finally
  /// gets enforced: an operation has no body to infer from, so a declaration
  /// without a written signature has nothing to mean.
  | SdEffect      : string -> list (string & ssig) -> sdecl
  /// `locate name` — print what `name` is: a macro production, a primitive, or
  /// a definition decompiled back to surface syntax (E05_Locate).
  ///
  /// A declaration rather than a word, for the same reason `define` is one: its
  /// argument is a NAME, not a value, so it has nothing to do with the stack
  /// and cannot be given a signature. Forth reaches the same shape from the
  /// other direction, by making `LOCATE` immediate.
  | SdLocate      : string -> sdecl
  /// `macro name ( slots ) { template }`, or with keyed alternatives.
  ///
  /// The production arrives already checked for shape by the parser and gets
  /// checked for LL(1) compatibility with the table it is about to join by the
  /// session, which is the one place that knows the table.
  | SdMacro       : mprod -> sdecl
  /// `extern name ( sig )` — a foreign function, called through libc (D-66).
  ///
  /// The word name IS the C symbol; there is no aliasing form, because one
  /// would need a second name in the syntax to buy nothing the Dictionary
  /// cannot already do (`with { c_name nicer_name }`).
  ///
  /// It is `declare` with a different effect, and deliberately parsed the same
  /// way: an `extern` word has no body, so its signature is mandatory for the
  /// reason D-31 already gives for an operation's.
  | SdExtern      : string -> ssig -> sdecl
  /// A bare sequence of terms, evaluated against the current REPL stack.
  | SdExpr   : list sterm -> sdecl

(* ------------------------------------------------------------------------ *)
(* Occurrence counting                                                      *)
(* ------------------------------------------------------------------------ *)

/// How many times `$x` is read in a body.
///
/// E04 needs this to choose between `SPick` and `SRoll`: a copyable local can
/// be read any number of times (each a pick), while a non-copyable one must be
/// read exactly once (a roll, which consumes it). Counting occurrences up front
/// is what makes that decision without a liveness analysis.
/// Measure follows the M01/M05 pattern: rank orders `list(1) > term(0)`.
let rec count_var (x:string) (t:sterm)
  : Tot nat (decreases %[(sterm_size t <: nat); 0]) =
  match t with
  | StVar y    -> if y = x then 1 else 0
  | StBlock ts -> count_var_list x ts
  /// A read inside a branch is FORCED to count as repeated, whatever the
  /// actual number is. The elaborator compiles a sole read to a `roll`, which
  /// consumes the slot — and a slot consumed in one branch but not the other
  /// leaves the two branches with different stacks, so `if { } then { $x }
  /// endif` would be rejected for a reason that has nothing to do with what
  /// the programmer wrote.
  ///
  /// Forcing `pick` instead costs an end-of-body drop and requires `Copy`,
  /// which is the honest requirement: a value read under a condition cannot be
  /// statically known to be moved exactly once.
  | StCase bs  -> let n = count_var_lists x bs in
                  if n = 0 then 0 else n + 1
  /// Only the BODY is counted. A handler's initialiser and implementations run
  /// on their own stacks — the state segment, plus the operation's arguments —
  /// so an enclosing definition's locals are not in scope there and `E04`
  /// rejects a read of one. Counting them would inflate the count for a read
  /// that cannot occur.
  ///
  /// The body needs no inflation either, unlike a branch: it runs exactly once.
  | StHandle _ _ _ _ b -> count_var_list x b
  /// `with` does not change the stack at all, so its body counts exactly as if
  /// it had been written in place — which, after elaboration, it was.
  | StWith _ b -> count_var_list x b
  /// Neither block is counted: both run on a fresh stack, so an enclosing
  /// definition's locals are not in scope in either (see `StHandle` above).
  | StTry _ _  -> 0
  | _          -> 0

and count_var_list (x:string) (ts:list sterm)
  : Tot nat (decreases %[sterms_size ts; 1]) =
  match ts with
  | []     -> 0
  | t :: r -> count_var x t + count_var_list x r

/// Counting ACROSS branches, not within one, so a local read in either arm of
/// an `if` counts as read. That is the conservative direction: over-counting
/// costs a `pick` and an end-of-body drop where a `roll` would have done,
/// while under-counting would compile a read to a move in a branch that does
/// not run.
and count_var_lists (x:string) (bs:list (list sterm))
  : Tot nat (decreases %[sterm_lists_size bs; 2]) =
  match bs with
  | []     -> 0
  | b :: r -> count_var_list x b + count_var_lists x r

/// Whether `recurse` appears anywhere in a surface body (D-67).
///
/// Asked only to produce a better message: `define f { recurse }` has no
/// signature to check a self-call against, and "unknown word: recurse" would
/// send a reader looking for a missing import rather than a missing signature.
/// The elaborated form of the same question is `M05.ordered_at` (D-70), which
/// is what decides the `Rec` effect; this one runs earlier and decides nothing.
let rec mentions_recurse (t:sterm)
  : Tot bool (decreases %[(sterm_size t <: nat); 0]) =
  match t with
  | StWord w    -> w = "recurse"
  | StBlock ts  -> mentions_recurse_list ts
  | StCase bs   -> mentions_recurse_lists bs
  | StHandle _ _ i im b ->
    mentions_recurse_list i || mentions_recurse_impls im || mentions_recurse_list b
  | StWith _ b  -> mentions_recurse_list b
  | StTry b c   -> mentions_recurse_list b || mentions_recurse_list c
  | _           -> false

and mentions_recurse_list (ts:list sterm)
  : Tot bool (decreases %[sterms_size ts; 1]) =
  match ts with
  | []     -> false
  | t :: r -> mentions_recurse t || mentions_recurse_list r

and mentions_recurse_lists (bs:list (list sterm))
  : Tot bool (decreases %[sterm_lists_size bs; 1]) =
  match bs with
  | []      -> false
  | b :: r  -> mentions_recurse_list b || mentions_recurse_lists r

and mentions_recurse_impls (im:list (string & list sterm))
  : Tot bool (decreases %[simpls_size im; 1]) =
  match im with
  | []           -> false
  | (_, b) :: r  -> mentions_recurse_list b || mentions_recurse_impls r
