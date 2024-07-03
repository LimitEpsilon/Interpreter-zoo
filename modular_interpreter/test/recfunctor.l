(let add = fun m -> fun n -> match m { O -> n, S [m] -> S [add m n] } ;;
# recursive functor
let sum =
  fun n ->
    (let x = match n { O -> 0, S [n] -> S [add n (sum n).x] })
).(sum 3).x
