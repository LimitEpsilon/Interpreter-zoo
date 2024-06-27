type nat = O | S of nat
type comparison = Eq | Lt | Gt

let id : 'a -> 'a = fun x -> x

type positive = XI of positive | XO of positive | XH

module Nat = struct
  (** val eqb : nat -> nat -> bool **)

  let rec eqb n m =
    match n with
    | O -> ( match m with O -> true | S _ -> false)
    | S n' -> ( match m with O -> false | S m' -> eqb n' m')
end

module Pos = struct
  (** val succ : positive -> positive **)

  let rec succ = function XI p -> XO (succ p) | XO p -> XI p | XH -> XO XH

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p -> (
        match y with
        | XI q -> compare_cont r p q
        | XO q -> compare_cont Gt p q
        | XH -> Gt)
    | XO p -> (
        match y with
        | XI q -> compare_cont Lt p q
        | XO q -> compare_cont r p q
        | XH -> Gt)
    | XH -> ( match y with XH -> r | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare = compare_cont Eq

  (** val max : positive -> positive -> positive **)

  let max p p' = match compare p p' with Gt -> p | _ -> p'

  (** val eqb : positive -> positive -> bool **)

  let rec eqb p q =
    match p with
    | XI p0 -> ( match q with XI q0 -> eqb p0 q0 | _ -> false)
    | XO p0 -> ( match q with XO q0 -> eqb p0 q0 | _ -> false)
    | XH -> ( match q with XH -> true | _ -> false)
end

(** val get_idx : nat -> 'a1 vec -> nat -> 'a1 **)

let rec get_idx l i =
  match l with
  | [] -> assert false (* absurd case *)
  | hd :: tl -> if i <= 0 then hd else get_idx tl (i - 1)
