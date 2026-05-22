module Catcat.Core

open FStar.HyperStack.ST
open FStar.List.Tot
open FStar.Parse

module HS = FStar.HyperStack

type stack = list int

let stack_rel : FStar.Preorder.preorder stack = fun _ _ -> True

noeq type machine = {
  stack_ref: mref stack stack_rel;
}

type word =
  | Push: value:int -> word

let read_word (token:string) : Tot (option word) =
  match int_of_string token with
  | Some value -> Some (Push value)
  | None -> None

let make_machine ()
  : ST machine
    (requires (fun _ -> True))
    (ensures (fun _ machine h1 -> HS.sel h1 machine.stack_ref == []))
=
  let stack_ref = ralloc HS.root [] in
  { stack_ref = stack_ref }

let eval_word (machine:machine) (opcode:word)
  : ST unit
    (requires (fun h0 -> machine.stack_ref `is_live_for_rw_in` h0))
    (ensures (fun h0 _ h1 ->
      match opcode with
      | Push value -> HS.sel h1 machine.stack_ref == value :: HS.sel h0 machine.stack_ref))
=
  match opcode with
  | Push value ->
      let current = !machine.stack_ref in
      machine.stack_ref := value :: current

let rec render_values (values:stack) : Tot string =
  match values with
  | [] -> ""
  | head :: tail -> render_values tail ^ " " ^ Prims.string_of_int head

let render_stack (values:stack) : Tot string =
  match values with
  | [] -> "ok"
  | _ -> "ok " ^ render_values values

let print_stack (machine:machine)
  : ST string
    (requires (fun h0 -> machine.stack_ref `is_live_for_rw_in` h0))
    (ensures (fun h0 rendered h1 ->
      h0 == h1 /\
      rendered == render_stack (HS.sel h0 machine.stack_ref)))
=
  let values = !machine.stack_ref in
  render_stack values
