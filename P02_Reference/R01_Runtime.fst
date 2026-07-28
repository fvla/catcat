module R01_Runtime

open FStar.List.Tot
open M01_Kinds
open M04_Effects
open M05_Terms

let rec dict_lookup (d:rdict) (w:word_id) : Tot (option rword) (decreases d) =
  match d with
  | []            -> None
  | (w', rw) :: r -> if w' = w then Some rw else dict_lookup r w

let dict_extend (d:rdict) (w:word_id) (rw:rword) : Tot rdict = (w, rw) :: d

let rec take (n:nat) (s:rstack) : Tot (option (list rvalue & rstack)) (decreases n) =
  if n = 0 then Some ([], s)
  else match s with
       | []      -> None
       | v :: r  -> (match take (n - 1) r with
                     | None            -> None
                     | Some (vs, rest) -> Some (v :: vs, rest))

let rec lemma_take_give (n:nat) (s:rstack)
  : Lemma (ensures (match take n s with
                    | Some (vs, rest) -> give vs rest == s
                    | None            -> True))
          (decreases n) =
  if n = 0 then ()
  else match s with
       | []     -> ()
       | _ :: r -> lemma_take_give (n - 1) r
