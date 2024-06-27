(let stream = (1, stream) ;;
let hd = fun l -> match l { O -> (), (h, t) -> h } ;;
let tl = fun l -> match l { O -> (), (h, t) -> t } ;;
let nth = fun l -> fun n -> match n { O -> hd l, S [n] -> nth (tl l) n } ;;
Top).(nth stream 10)
