module M02_Types.StackIndexedMonad

open FStar.List.Tot
open M01_Syntax
module TC = FStar.Tactics.Typeclasses

let (>>) f g x = g (f x)
class stack_indexed_monad (m: Type -> Type) = {
    return : #a:Type -> a -> m a;
    bind   : #a:Type -> #b:Type -> #c:Type -> (a -> m b) -> (b -> m c) -> (a -> m c);

    [@@@TC.no_method]
    laws : squash (
        (forall (a b:Type) (h:a -> m b). bind return h == h) /\ // Left identity law
        (forall (a b:Type) (f:a -> m b). bind f return == f) /\ // Right identity law
        (forall (a b c d:Type) (f:a -> m b) (g:b -> m c) (h:c -> m d). bind (bind f g) h == bind f (bind g h)) // Associative law
    );
}
let lift #m (_m:stack_indexed_monad m) (#a #b:Type) (f:a -> b) : m a -> m b =
    let fm = f >> _m.return in
    (fun (x:m a) -> () |> bind (fun _ -> x) fm)


type function_type (inputs outputs:list dtype) = value_list inputs -> value_list outputs
type stack_function_type (inputs outputs:list dtype) = value_stack inputs -> value_stack outputs



let lift_list_to_stack_function (#inputs #outputs:list dtype) (f:function_type inputs outputs)
    : stack_function_type inputs outputs
    =
    f
