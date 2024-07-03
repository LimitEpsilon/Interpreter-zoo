(let add = fun m -> fun n ->
  match n { O -> m, S [n] -> S [add m n] } ;;
let main = add (add (f x) 1) 2
).main
