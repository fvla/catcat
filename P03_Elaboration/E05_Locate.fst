module E05_Locate

/// P03, module 05: `locate` — showing a word's source.
///
/// SUMMARY
///   Forth's `LOCATE`/`SEE`: name a word, get its definition back. Here that
///   means DECOMPILING the core term the word is bound to, because the core
///   term is what the word actually is. Nothing retains the source text.
///
/// WHY DECOMPILE RATHER THAN KEEP THE SOURCE
///   Two reasons, and the second is the one that matters.
///
///   1. Keeping source text means keeping it accurate, and every pass that
///      rewrites a term — macro expansion today, `specialize` from M6 on —
///      would have to maintain a parallel copy. The core term cannot go stale
///      relative to itself.
///   2. `locate` is then a *test of the elaborator*. Its output is surface
///      syntax that re-parses to the same core term, so a decompilation that
///      reads wrong is evidence the elaboration was wrong. That is worth more
///      than a pretty printer.
///
///   The round-trip is exact for everything the surface language can currently
///   spell. Where it cannot — deep stack access, which exists only because
///   `$x` locals were compiled away — the rendering is deliberately not valid
///   syntax (`pick.2`) rather than a plausible-looking lie.
///
/// THE `if` RECONSTRUCTION
///   `TBoolSum` immediately followed by a two-branch `TCase` is printed back as
///   `if { } then { … } else { … } endif`. The empty condition block is not a
///   cheat: the condition's code has already been emitted to the left, and
///   `cond if { } then { … } endif` is exactly how the surface form is written
///   in practice, so the printed text really does elaborate back to the term it
///   came from.
///
/// SOURCE OF TRUTH
///   `M05_Terms.term` for what can appear, `E03_Parser.macro_table` for the
///   macro renderings, `E04_Elaborate.nenv` for names.

open FStar.List.Tot
open M01_Kinds
open M03_Signatures
open M04_Effects
open M05_Terms
open R01_Runtime
open E02_Ast
open E03_Parser
open E04_Elaborate

(* ------------------------------------------------------------------------ *)
(* Rendering types                                                          *)
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

/// Each side is omitted rather than left blank when empty, so a constant reads
/// `( -- bool )` and not `(  -- bool )`.
let render_row (s:srow) : Tot string =
  let a = render_tys (rev s.pre) in
  let b = render_tys (rev s.post) in
  "( " ^ (if a = "" then "" else a ^ " ") ^ "-- "
       ^ (if b = "" then "" else b ^ " ") ^ ")"

(* ------------------------------------------------------------------------ *)
(* Names                                                                    *)
(* ------------------------------------------------------------------------ *)

/// The reverse of `lookup_name`. The name environment is a shadowing stack —
/// most recent first — so the first hit is the binding a program written now
/// would resolve to, which is the one worth printing.
let rec name_of (e:nenv) (w:word_id) : Tot (option string) (decreases e) =
  match e with
  | []     -> None
  | n :: r -> if n.n_id = w then Some n.n_name else name_of r w

/// An unnamed id prints as `#7`. That is not valid surface syntax, on purpose:
/// a word with no name in scope cannot be written, and printing an invented
/// name would produce text that does not mean what it says.
let show_word (e:nenv) (w:word_id) : Tot string =
  match name_of e w with
  | Some n -> n
  | None   -> "#" ^ string_of_int w

(* ------------------------------------------------------------------------ *)
(* Literals and stack operations                                            *)
(* ------------------------------------------------------------------------ *)

/// `f32`/`f64` are abstract in M01 — the specification never inspects a float —
/// so there is nothing to print but the type.
let show_lit (l:lit) : Tot string =
  match l with
  | LPrim PI8 v | LPrim PI16 v | LPrim PI32 v | LPrim PI64 v -> string_of_int v
  | LPrim PU8 v | LPrim PU16 v | LPrim PU32 v | LPrim PU64 v -> string_of_int v
  | LPrim PBool v -> if v then "true" else "false"
  | LPrim PUnit _ -> "unit"
  | LPrim PF32 _  -> "<f32>"
  | LPrim PF64 _  -> "<f64>"

/// `dup`, `pop` and `swap` are surface words and print as themselves. `pick`
/// and `roll` are not: they exist only as the compiled form of a `$x` local,
/// and the local's NAME is gone by then (D05 §3.4). `pick.2` says "two slots
/// down" and is deliberately unparseable, so nobody mistakes the output for
/// something they could have typed.
let show_sop (o:sop) : Tot string =
  match o with
  | SDup _      -> "dup"
  | SPop _      -> "pop"
  | SSwap _ _   -> "swap"
  | SPick a _   -> "pick." ^ string_of_int (length a)
  | SRoll a _   -> "roll." ^ string_of_int (length a)

(* ------------------------------------------------------------------------ *)
(* Terms                                                                    *)
(* ------------------------------------------------------------------------ *)

/// Juxtaposition with exactly one space, and none around an empty program.
let cons_sp (a b:string) : Tot string =
  if a = "" then b else if b = "" then a else a ^ " " ^ b

/// An empty block is `{ }`, the way it is written, not `{  }`.
let braces (s:string) : Tot string =
  if s = "" then "{ }" else "{ " ^ s ^ " }"

/// Decompile a term list, head first.
///
/// Working over a LIST rather than a term is what makes this one function
/// instead of two. `TSeq a b :: rest` becomes `a :: b :: rest`, which strictly
/// decreases `terms_size` because the `TSeq` node itself is dropped — so
/// flattening, sequencing and the two-item `if` pattern all live in the same
/// recursion and none of them needs a separate measure.
///
/// The ranks order `show_branches(1) > show_items(0)`: a branch list is
/// strictly smaller than the `TCase` that held it, while rendering one branch
/// is the same size and must therefore drop a rank.
let rec show_items (e:nenv) (ts:list term)
  : Tot string (decreases %[terms_size ts; 0]) =
  match ts with
  | [] -> ""
  | TNil :: rest      -> show_items e rest
  | TSeq a b :: rest  -> show_items e (a :: b :: rest)

  /// Normalise the SECOND element too, before any two-element pattern is
  /// tried. `seq_of` nests to the right, so `a b c` is `TSeq a (TSeq b …)` and
  /// a pair pattern that only flattened the head would never see `b` — which
  /// is exactly how the `if` reconstruction below silently failed to fire the
  /// first time. Both rewrites drop a node, so `terms_size` still decreases.
  | a :: TNil :: rest      -> show_items e (a :: rest)
  | a :: TSeq b c :: rest  -> show_items e (a :: b :: c :: rest)

  /// The `if` reconstruction. Branches are stored in TAG order — false first
  /// (D-33) — so the second one is `then` and the first is `else`.
  | TBoolSum :: TCase vs [f; t] :: rest ->
    if vs = bool_variants
    then cons_sp ("if { } then " ^ braces (show_items e [t])
                  ^ " else " ^ braces (show_items e [f]) ^ " endif")
                 (show_items e rest)
    else cons_sp "bool>sum" (show_items e (TCase vs [f; t] :: rest))

  | TCase _ bs :: rest ->
    cons_sp ("case" ^ show_branches e bs) (show_items e rest)
  | THandle eff impls body :: rest ->
    cons_sp ("handle !" ^ string_of_int eff ^ " {" ^ show_impls e impls
             ^ " } " ^ braces (show_items e [body]))
            (show_items e rest)
  | TSpecialize body :: rest ->
    cons_sp ("specialize " ^ braces (show_items e [body])) (show_items e rest)

  | TLit l :: rest    -> cons_sp (show_lit l) (show_items e rest)
  | TStack o :: rest  -> cons_sp (show_sop o) (show_items e rest)
  | TWord w :: rest   -> cons_sp (show_word e w) (show_items e rest)

  /// The remaining forms have no surface spelling yet. They print with a
  /// leading marker rather than a guess, so `locate` never claims a word can be
  /// written in a way it cannot.
  | TPack n _ _ :: rest    -> cons_sp ("pack@" ^ string_of_int n) (show_items e rest)
  | TUnpack n _ _ :: rest  -> cons_sp ("unpack@" ^ string_of_int n) (show_items e rest)
  | TInj _ tag :: rest     -> cons_sp ("inj." ^ string_of_int tag) (show_items e rest)
  | TBoolSum :: rest       -> cons_sp "bool>sum" (show_items e rest)
  | TBoxNew _ :: rest      -> cons_sp "box.new" (show_items e rest)
  | TBoxOpen _ :: rest     -> cons_sp "box.open" (show_items e rest)
  | TRcNew _ :: rest       -> cons_sp "rc.new" (show_items e rest)
  | TRcClone _ :: rest     -> cons_sp "rc.clone" (show_items e rest)
  | TRcDrop _ :: rest      -> cons_sp "rc.drop" (show_items e rest)
  | TRcRead _ :: rest      -> cons_sp "rc.read" (show_items e rest)
  | TRoll n _ :: rest      -> cons_sp ("roll@" ^ string_of_int n) (show_items e rest)
  | TUnroll n _ :: rest    -> cons_sp ("unroll@" ^ string_of_int n) (show_items e rest)

and show_branches (e:nenv) (bs:list term)
  : Tot string (decreases %[terms_size bs; 1]) =
  match bs with
  | []     -> ""
  | b :: r -> " " ^ braces (show_items e [b]) ^ show_branches e r

and show_impls (e:nenv) (is:list (op_id & term))
  : Tot string (decreases %[impls_size is; 1]) =
  match is with
  | []            -> ""
  | (o, t) :: r   -> " " ^ show_word e o ^ " " ^ braces (show_items e [t])
                     ^ show_impls e r

let show_term (e:nenv) (t:term) : Tot string = show_items e [t]

(* ------------------------------------------------------------------------ *)
(* Primitives                                                               *)
(* ------------------------------------------------------------------------ *)

/// What the machine will do, named. A primitive has no body to show, and
/// saying so is the honest answer — `locate +` should not print something that
/// looks like a definition.
let show_prim_op (o:prim_op) : Tot string =
  match o with
  | OAddI -> "integer add"    | OSubI -> "integer subtract"
  | OMulI -> "integer multiply" | ODivI -> "integer divide (Euclidean)"
  | OModI -> "integer remainder (Euclidean)"
  | OLtI  -> "integer less-than" | OLeI -> "integer less-or-equal"
  | OEqI  -> "integer equality"
  | ONot  -> "boolean negation" | OAnd -> "boolean and" | OOr -> "boolean or"

(* ------------------------------------------------------------------------ *)
(* Macros                                                                   *)
(* ------------------------------------------------------------------------ *)

let show_slot (s:E03_Parser.mslot) : Tot string =
  match s with
  | MsBlock     -> "{ }"
  | MsWord      -> "<word>"
  | MsKeyword k -> k

let rec show_slots (ss:list E03_Parser.mslot) : Tot string (decreases ss) =
  match ss with
  | []     -> ""
  | s :: r -> " " ^ show_slot s ^ show_slots r

/// One line per alternative, spelled out in full. A macro is a grammar
/// production (D-35), and the readable form of a production with keyed
/// alternatives is just the list of sentences it accepts.
let rec show_macro_alts (name:string) (pre:list E03_Parser.mslot) (bs:list mbranch)
  : Tot string (decreases bs) =
  match bs with
  | []     -> ""
  | b :: r -> "\n  " ^ name ^ show_slots pre ^ " " ^ b.mb_key ^ show_slots b.mb_slots
              ^ show_macro_alts name pre r

let show_macro (p:mprod) : Tot string =
  "macro " ^ p.mp_name
  ^ (if Nil? p.mp_branches
     then "\n  " ^ p.mp_name ^ show_slots p.mp_pre
     else show_macro_alts p.mp_name p.mp_pre p.mp_branches)

(* ------------------------------------------------------------------------ *)
(* locate                                                                   *)
(* ------------------------------------------------------------------------ *)

/// Look a name up wherever names can live and render what is there.
///
/// MACROS ARE CHECKED FIRST because that is the order the parser resolves in:
/// a leading word matching the macro table invokes the macro, whatever else is
/// bound to the name. Reporting the dictionary entry instead would tell the
/// user about a binding their program cannot reach.
let locate (e:nenv) (d:rdict) (x:string) : Tot string =
  match lookup_macro macro_table x with
  | Some p -> show_macro p
  | None ->
    match lookup_name e x with
    | None -> "error: no word named '" ^ x ^ "'"
    | Some n ->
      let hdr = x ^ " " ^ render_row n.n_sig in
      match dict_lookup d n.n_id with
      | Some (WPrim o) -> hdr ^ "\n  \\ primitive: " ^ show_prim_op o
      | Some (WOp eff) -> hdr ^ "\n  \\ operation of effect !" ^ string_of_int eff
      | Some (WDef t)  -> "define " ^ hdr ^ " {\n  " ^ show_term e t ^ "\n}"
      /// Reachable only if the name environment and the dictionary disagree,
      /// which would be a session bug rather than a user error. Say which.
      | None -> hdr ^ "\n  \\ internal error: bound to id "
                ^ string_of_int n.n_id ^ ", which the dictionary does not have"
