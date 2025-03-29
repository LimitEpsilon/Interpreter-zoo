let y = 1 ;;
let x = y ;;
let add =
  fun m -> fun n ->
    match m { O -> n, S [m] -> S [add m n] } ;;
add x y
