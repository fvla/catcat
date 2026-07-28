module M02_Types.Monad

open FStar.List.Tot
module TC = FStar.Tactics.Typeclasses

let (>>) f g x = g (f x)

// This code was written for practice with doing category theory in F*.
class monad (m: Type -> Type) = {
    return : #a:Type -> a -> m a;
    bind   : #a:Type -> #b:Type -> m a -> (a -> m b) -> m b;

    [@@@TC.no_method]
    left_id_law  : #a:Type -> #b:Type -> x:a -> h:(a -> m b) -> Lemma (bind (return x) h == h x);
    [@@@TC.no_method]
    right_id_law : #a:Type -> x:m a -> Lemma (bind x return == x);
    [@@@TC.no_method]
    assoc_law    : #a:Type -> #b:Type -> #c:Type -> x:m a -> f:(a -> m b) -> g:(b -> m c) -> Lemma (bind x (fun y -> bind (f y) g) == bind (bind x f) g);
}
let lift #m (_m:monad m) (#a #b:Type) (f:a -> b) : m a -> m b =
    (fun (x:m a) -> bind x (f >> _m.return))


// Helper lemmas for list_monad
let rec append_nil_right (#a:Type) (xs:list a)
    : Lemma (xs @ [] == xs) =
    match xs with
    | [] -> ()
    | _::tail -> append_nil_right tail

let rec concatMap_return (#a:Type) (xs:list a)
    : Lemma (concatMap (fun x -> [x]) xs == xs) =
    match xs with
    | [] -> ()
    | _::tail -> concatMap_return tail


let rec append_assoc (#a:Type) (xs ys zs:list a)
    : Lemma ((xs @ ys) @ zs == xs @ (ys @ zs)) =
    match xs with
    | [] -> ()
    | head::tail -> append_assoc tail ys zs

let rec concatMap_append (#a #b:Type) (xs ys:list a) (f:a -> list b)
    : Lemma (concatMap f (xs @ ys) == concatMap f xs @ concatMap f ys) =
    match xs with
    | [] -> ()
    | head::tail ->
        concatMap_append tail ys f;
        let (_xs, _ys, _zs) = (f head, concatMap f tail, concatMap f ys) in
        append_assoc _xs _ys _zs

let rec concatMap_assoc (#a #b #c:Type) (xs:list a) (f:a -> list b) (g:b -> list c)
    : Lemma (concatMap (fun y -> concatMap g (f y)) xs == concatMap g (concatMap f xs)) =
    match xs with
    | [] -> ()
    | head::tail ->
        concatMap_assoc tail f g;
        concatMap_append (f head) (concatMap f tail) g


instance list_monad : monad list = {
    return = (fun (#a:Type) (x:a) -> [x]);
    bind = (fun (#a #b:Type) x f -> concatMap f x);

    left_id_law = (fun (#a #b:Type) x h -> append_nil_right (h x));
    right_id_law = concatMap_return;
    assoc_law = concatMap_assoc;
}
