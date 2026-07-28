module M02_Types

open FStar.List.Tot
open M01_Syntax
module TC = FStar.Tactics.Typeclasses

let (>>) f g x = g (f x)

// module StackIndexedMonad = {
//     type stack_function_type (inputs outputs: list dtype) =
//         (a:list dtype -> b:list dtype) {forall (tail: list dtype).}

//     // class indexed_monad (#index: Type) (m: index -> index -> Type -> Type) = {
//     //     [@@@TC.no_method]
//     //     laws : (forall (i j:index). monad (m i j));
//     // }
// }



// class stack_indexed_monad (m: list dtype -> list dtype -> Type) = {
//     return : #i:list dtype -> m [] i;
// }

// type parameter_dtype (t: list dtype) = x: list value { t = map dtype_from_value x }
// type function_dtype (t u: list dtype) = parameter_dtype t -> parameter_dtype u

// module StackIndexedMonad = {
//     type m (i j:list dtype) = list value
//     // return: #a:dtype -> a -> M [] [a] (fun stack -> a :: stack)
//     let return (a:list value) = 
// }


// type stack_function_dtype =
//     t:list dtype * u:list dtype * (a:list value -> b:list value) {
//     let _t = map dtype_from_value a in
//     let _u = map dtype_from_value b in
//     // The input lists a and b are stacks. The head of _t must match t, same with _u and u, and the rest must be preserved.
//     true
// }
