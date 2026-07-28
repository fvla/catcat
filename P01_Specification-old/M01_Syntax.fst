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
// type value_list (types: list dtype) = a:value_stack types { length a == length types }
type value_list (types: list dtype) = a:value_stack types { let (l, tail) = splitAt (length types) a in l == a }

// To convert between them...
let lift_list_to_stack (#types: list dtype) (l: value_list types)
  : GTot (value_stack types) =
  l

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

let splitAt_stack (#types: list dtype) (n:nat) (stack: value_stack types)
  : GTot (value_stack (fst (splitAt n types)) & value_stack (snd (splitAt n types))) =
  let (stem, tail) = splitAt n types in
  lemma_splitAt_self stem;
  lemma_splitAt_append n stem;
  (stem, tail)

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

let append_to_list (#types: list dtype) (tail: list value) (l: value_list types)
  : GTot (value_stack types) =
  lemma_append_splitAt l tail;
  l @ tail

let rec lemma_split_append_stack (#types: list dtype) (stack: value_stack types)
  : Lemma (stack == split_stack stack |> (fun (s, tail) -> append_to_stack tail s)) =
  match types with
  | [] -> ()
  | _::types' ->
    lemma_split_append_stack #types' (tl stack)


// List and stack function types
type list_function_type (inputs outputs:list dtype) = value_list inputs -> GTot (value_list outputs)
type stack_function_type (inputs outputs:list dtype) =
  stack:value_stack inputs -> GTot (o:value_stack outputs {
    snd (split_stack stack) == snd (split_stack o)
  })

let lift_list_function_to_stack (#inputs #outputs:list dtype) (f:list_function_type inputs outputs)
  : GTot (stack_function_type inputs outputs) =
  let f_out (stack: value_stack inputs)
    : GTot (o:value_stack outputs { snd (split_stack stack) == snd (split_stack o) }) =
    let (l, tail) = lower_stack_to_list_tail stack in
    let l' = f l in
    lemma_append_splitAt l' tail;
    append_to_list tail l'
  in
  f_out

let rec is_compatible_stack_types (a b:list dtype)
  : GTot bool =
  match a, b with
  | [], _ -> true
  | _, [] -> true
  | h1::t1, h2::t2 -> h1 = h2 && is_compatible_stack_types t1 t2

let rec extract_uncommon_suffixes (a b:list dtype { is_compatible_stack_types a b })
  : GTot (list dtype & list dtype) =
  match a, b with
  | [], _ -> (a, b)
  | _, [] -> (a, b)
  | h1::t1, h2::t2 -> extract_uncommon_suffixes t1 t2

let compose_stack_functions (#a #b #c #d:list dtype { is_compatible_stack_types b c }) (f:stack_function_type a b) (g:stack_function_type c d)
  : GTot (stack_function_type (a @ snd (extract_uncommon_suffixes b c)) (d @ fst (extract_uncommon_suffixes b c))) =
  fun x ->
    let (stem, tail) = splitAt (length a) x in
    let x' = (f stem) @ tail in
    x'
