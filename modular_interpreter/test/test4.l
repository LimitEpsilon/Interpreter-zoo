(let sum =
  fun f ->
    fun n ->
      match n { O -> f 0, S [n] -> add (f (S [n])) (sum f n) } ;;
let m = 3;;
let x = sum g m).x
