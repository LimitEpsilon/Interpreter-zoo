(let add =
  (let add =
    fun m -> fun n -> match m { O -> n, S [m] -> S [add m n] }
    ).add ;;
let mult =
  (let mult =
    fun m -> fun n -> match m { O -> O, S [m] -> add n (mult m n) }
    ).mult ;; Top
).(mult 3 3)

