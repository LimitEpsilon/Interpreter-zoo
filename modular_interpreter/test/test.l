(let Top =
  let Even =
    (let is_even = fun n -> match n { O -> true, S [n] -> Top.Odd.is_odd n }) ;;
  let Odd =
    (let is_odd = fun n -> match n { O -> false, S [n] -> Top.Even.is_even n })
).(Top.Even.is_even 4)
