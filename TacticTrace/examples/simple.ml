let simple_tac = ALL_TAC;;
let rec repeat_tac n = if n = 0 then ALL_TAC else repeat_tac (n-1) THEN ALL_TAC;;
let tac1,tac2 = ALL_TAC,ALL_TAC;;
let tac_arg =
  fun (t:term) -> ALL_TAC;;

let thm = prove(`1=1`, simple_tac THEN repeat_tac 2 THEN tac1 THEN tac2 THEN tac_arg `1` THEN REFL_TAC);;
