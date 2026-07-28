module R04_Erasure

open FStar.List.Tot
open M01_Kinds
open M02_Stacks
open M03_Signatures
open M05_Terms
open M06_Typing
open R01_Runtime
open R02_Machine

/// Cases are enumerated rather than wildcarded: `prim_rep p` differs per
/// constructor, so a catch-all would leave F* unable to see that the payload
/// is an integer.
let rec erase_value (#t:dtype) (v:value t) : Tot rvalue (decreases v) =
  match v with
  | VPrim #p x ->
    (match p with
     | PBool -> RBool x
     | PUnit -> RUnit
     | PF32  -> RBits 0
     | PF64  -> RBits 0
     | PI8   -> RInt x | PI16 -> RInt x | PI32 -> RInt x | PI64 -> RInt x
     | PU8   -> RInt x | PU16 -> RInt x | PU32 -> RInt x | PU64 -> RInt x)
  | VSeal n _ inner       -> RSeal n (erase_stack inner)
  | VSum tag payload      -> RSum tag (erase_stack payload)
  | VBox v                -> RBox (erase_value v)
  | VRc v                 -> RRc (erase_value v)
  /// `VName` wraps a value with a type-level-only incomplete-type annotation
  /// (D02/M01's `TName`): there is no `RName` runtime tag, so erasure just
  /// drops the wrapper and keeps the payload's representation.
  | VName v               -> erase_value v

and erase_stack (#s:seg) (st:vstack s) : Tot rstack (decreases st) =
  match st with
  | VNil          -> []
  | VCons v rest  -> erase_value v :: erase_stack rest

let rec lemma_erase_length (#s:seg) (st:vstack s)
  : Lemma (ensures length (erase_stack st) == length s) (decreases st) =
  match st with
  | VNil         -> ()
  | VCons _ rest -> lemma_erase_length rest

let rec lemma_erase_append (#a #r:seg) (x:vstack a) (y:vstack r)
  : Lemma (ensures erase_stack (vappend x y) == give (erase_stack x) (erase_stack y))
          (decreases x) =
  match x with
  | VNil         -> ()
  | VCons _ rest -> lemma_erase_append rest y
