let simple_conv t = NUM_REDUCE_CONV t;;
(* simple_conv2 won't appear as json trace because `e=e` is ignored by export fns *)
let simple_conv2 = fun (t:term) -> REFL t;;

let thm = prove(`1+1=2`, CONV_TAC (LAND_CONV simple_conv2) THEN ACCEPT_TAC (simple_conv `1+1`));;
