(let Top =
  let Even =
    (let is_even = fun n -> match n { O -> 1, S [n] -> Top.Odd.is_odd n }) ;;
  let Odd =
    (let is_odd = fun n -> match n { O -> 0, S [n] -> Top.Even.is_even n })
).(Top.Even.is_even 4)
