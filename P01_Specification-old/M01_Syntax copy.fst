module M01_Syntax

open FStar.List.Tot

// Syntactic type definitions for AST
type dtype =
  | TInt

type value =
  | VInt: int -> value

type primitive =
  | PPlus
  | PMinus
  | PTimes

type word =
  | WPrimitive: primitive -> word
  | WLiteral: value -> word
  | WVar: string -> word

type program = list word

// Relations between types
let dtype_from_value (v: value) : dtype =
  match v with
  | VInt _ -> TInt

type value_of (t: dtype) = a:value { t == dtype_from_value a }


// List and stack types
type value_stack (types: list dtype) = a:list value { let (l, tail) = splitAt (length types) a in types == map dtype_from_value l }
type value_list (types: list dtype) = a:value_stack types { let (l, tail) = splitAt (length types) a in a == l }

// To convert between them...
let lift_list_to_stack (#types: list dtype) (l: value_list types)
  : GTot (value_stack types) =
  l

let lift_list_tail_to_stack (#types: list dtype) (l: value_list types) (tail: list value)
  : GTot (value_stack types) =
  assert ((l @ []) @ tail == l @ ([] @ tail));
  l @ tail

let rec lemma_splitAt_self (#a:Type) (l:list a)
  : Lemma (splitAt (length l) l == (l, [])) =
  match l with
  | [] -> ()
  | _::tail -> lemma_splitAt_self tail

let rec lemma_splitAt_append (#a:Type) (n:nat) (l:list a)
  : Lemma (let (first, second) = splitAt n l in l == first @ second) =
  match n, l with
  | 0, _ -> ()
  | _, [] -> ()
  | _, _::tail -> lemma_splitAt_append (n-1) (tail)

let lower_stack_to_list_tail (#types: list dtype) (stack: value_stack types)
  : GTot (result:(value_list types & list value) { stack == (fst result) @ (snd result) }) =
  let (l, tail) = splitAt (length types) stack in
  lemma_splitAt_self l;
  lemma_splitAt_append (length types) stack;
  (l, tail)

let split_stack (#types: list dtype) (stack: value_stack types)
  : GTot (value_stack types & list value) =
  let (l, tail) = lower_stack_to_list_tail stack in
  (lift_list_to_stack l, tail)

// Helpers
let rec lemma_append_splitAt (#a:Type) (l m:list a)
  : Lemma (splitAt (length l) (l @ m) == (l, m)) =
  match l with
  | [] -> ()
  | head::tail ->
    lemma_append_splitAt tail m

let append_to_stack (#types: list dtype) (l: list value) (stack: value_stack types)
  : GTot (value_stack types) =
  let (stack', tail) = split_stack stack in
  lemma_append_splitAt stack' (tail @ l);
  stack' @ tail @ l


// List and stack function types
type list_function_type (inputs outputs:list dtype) = value_list inputs -> GTot (value_list outputs)
type stack_function_type (inputs outputs:list dtype) =
  f:(value_stack inputs -> GTot (value_stack outputs)) {
    forall (l: value_list inputs) (tail: list value).
    let stack = lift_list_to_stack l in
    let stack' = stack @ tail in
    f stack @ tail == f stack'
  }

let lift_list_function_to_stack (#inputs #outputs:list dtype) (f:list_function_type inputs outputs)
  : GTot (stack_function_type inputs outputs) =
  let f_out (stack: value_stack inputs)
    : GTot (value_stack outputs) =
    let (stack', tail) = split_stack stack in
    lemma_splitAt_self stack';
    let (l, []) = lower_stack_to_list_tail stack' in
    let stack'' = lift_list_to_stack (f l) in
    lemma_append_splitAt stack'' tail;
    stack'' @ tail
  in
  f_out
