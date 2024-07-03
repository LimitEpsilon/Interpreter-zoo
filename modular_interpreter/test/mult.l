(let add =
  fun m ->
    fun n -> match m { O -> n, S [m] -> S [add m n] } ;;
let mult =
  fun m ->
    fun n -> match m { O -> O, S [m] -> add n (mult m n) }
).(mult 3 3)

