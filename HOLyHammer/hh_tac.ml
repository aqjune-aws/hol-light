(* hh_tac module: Tactics useful in transforming a problem to TPTP format *)

(* Given a predicate as an argument of another predicate, the
  conversion PRED_ARG_CONV changes it to an equivalent expression
  that has the predicate only at top level, so it can be encoded
  as TPTP; for example:
    P(!x. Q x)    Is rewritten to   ?v. (v <=> !x. Q x) /\ P v   *)
let PRED_ARG_THM = MESON [] `!f a. f a <=> (?v. (v <=> a) /\ f v)`;;

let must_pred tm =
  is_forall tm || is_exists tm || is_conj tm || is_disj tm ||
  is_imp tm || is_eq tm || is_neg tm || is_abs tm;;

let rec PRED_ARG_TM build_tm t =
  if must_pred t then
    let v = `dumvar:bool` in
    BETA_RULE (SPEC t (SPEC (mk_abs (v, build_tm v)) PRED_ARG_THM))
  else
    let f, a = dest_comb t in
    if find_terms must_pred a <> [] then
      let build_tm subt = build_tm (mk_comb (f, subt)) in
      PRED_ARG_TM build_tm a
    else
      let build_tm subt = build_tm (mk_comb (subt, a)) in
      PRED_ARG_TM build_tm f
;;

let rec PRED_ARG_CONV tm =
  if is_forall tm || is_exists tm then BINDER_CONV PRED_ARG_CONV tm else
  if is_conj tm || is_disj tm || is_imp tm then BINOP_CONV PRED_ARG_CONV tm else
  if is_neg tm then RAND_CONV PRED_ARG_CONV tm else
  if is_eq tm then
    let l, r = dest_eq tm in
    if must_pred l || must_pred r then BINOP_CONV PRED_ARG_CONV tm
    else
      if find_terms must_pred l <> [] then
        let build_tm subt = mk_eq (subt, r) in
        (PRED_ARG_TM build_tm THENC PRED_ARG_CONV) l
      else if find_terms must_pred r <> [] then
        let build_tm subt = mk_eq (l, subt) in
        (PRED_ARG_TM build_tm THENC PRED_ARG_CONV) r
      else REFL tm
  else if find_terms must_pred tm = [] then REFL tm
  else let l, r = dest_comb tm in
  if find_terms must_pred l <> [] then
    let build_tm subt = mk_comb (subt, r) in
    (PRED_ARG_TM build_tm THENC PRED_ARG_CONV) l
  else if find_terms must_pred r <> [] then
    let build_tm subt = mk_comb (l, subt) in
    (PRED_ARG_TM build_tm THENC PRED_ARG_CONV) r
  else REFL tm;;

(* Depth conversion that runs at most once per depth *)
let rec TOP_SWEEP_QCONV conv tm =
  let COMB_QCONV conv tm =
    let l,r = dest_comb tm in
    try let th1 = conv l in
    try let th2 = conv r in MK_COMB(th1,th2)
    with Failure _ -> AP_THM th1 r
    with Failure _ -> AP_TERM l (conv r) in
  let SUB_QCONV conv tm =
    if is_abs tm then ABS_CONV conv tm
    else COMB_QCONV conv tm in
  let THENQC conv1 conv2 tm =
    try let th1 = conv1 tm in
    try let th2 = conv2(rand(concl th1)) in TRANS th1 th2
    with Failure _ -> th1
    with Failure _ -> conv2 tm in
  THENQC (TRY_CONV conv) (SUB_QCONV (TOP_SWEEP_QCONV conv)) tm;;

(* Removes simple lambda-equalities before doing proper lambda-lifting *)
let ELIM_LAMBDA_EQ tm =
  let (l, r) = dest_eq tm in
  (if is_abs l || is_abs r then
  (ONCE_REWRITE_CONV [FUN_EQ_THM] THENC TOP_DEPTH_CONV BETA_CONV)
  else ALL_CONV) tm;;

(* FOL_TAC2 Tries to do more intelligent folification than FOL_TAC:
   - better computation of minimum needed arguments
   - does not use identity of the system to work with theorems that talk about I.
   - handles both the assumptions and the goal
 *)
let replace_smaller_assoc key newmin l =
  if List.mem_assoc key l then
    if newmin < assoc key l then
      (key, newmin) :: (List.remove_assoc key l)
    else l
  else (key, newmin) :: l;;

let rec fold_apps fn bnd tm sofar =
  try let l,r = try dest_forall tm with Failure _ ->
                try dest_exists tm with Failure _ ->
                    dest_abs tm in
      fold_apps fn (l :: bnd) r sofar
  with Failure _ -> try
      let l,r = try dest_conj tm with Failure _ ->
                try dest_disj tm with Failure _ ->
                try dest_eq tm with Failure _ ->
                    dest_imp tm in
      fold_apps fn bnd r (fold_apps fn bnd l sofar)
  with Failure _ -> try
      let tm = dest_neg tm in fold_apps fn bnd tm sofar
  with Failure _ ->
      let hop, args = strip_comb tm in
      let sofar = if is_abs hop then fold_apps fn bnd hop sofar else sofar in
      itlist (fold_apps fn bnd) args (fn bnd hop args sofar);;

let get_minarg tm sofar =
  let get_minarg_fold bnd hop args (cmin, vmin) =
    let len = length args in
    if is_var hop then if mem hop bnd then (cmin, vmin)
    else (cmin, replace_smaller_assoc (fst (dest_var hop)) len vmin)
    else (replace_smaller_assoc (fst (dest_const hop)) len cmin, vmin) in
  fold_apps get_minarg_fold [] tm sofar;;

let happ_def = new_definition `(happ : ((A -> B) -> A -> B)) = I`;;
let happ_conv_th = prove (`!(f:A->B) x. f x = happ f x`,
  REWRITE_TAC[happ_def; I_THM]);;

let happ_conv = REWR_CONV happ_conv_th;;
let rec happ_n_conv n tm =
  if n = 1 then happ_conv tm
  else (RATOR_CONV (happ_n_conv (n - 1)) THENC happ_conv) tm;;
let fol_conv_assoc op (cmin,vmin) =
  if is_const op then assoc (fst (dest_const op)) cmin else
  if is_var op then try assoc (fst (dest_var op)) vmin with _ -> 0 else failwith "fol_conv_assoc";;
let rec FOL_CONV ((cmin,vmin) as data) tm =
  try let l,r = try dest_forall tm with _ -> try dest_exists tm with _ -> dest_abs tm in
    BINDER_CONV (FOL_CONV (cmin, List.remove_assoc (fst (dest_var l)) vmin)) tm
  with _ ->
  if is_conj tm || is_disj tm || is_imp tm || is_eq tm then BINOP_CONV (FOL_CONV data) tm else
  if is_neg tm then RAND_CONV (FOL_CONV data) tm else
  let op,args = strip_comb tm in
  let th = rev_itlist (C (curry MK_COMB)) (map (FOL_CONV data) args) (REFL op) in
  let tm' = rand(concl th) in
  let n = length args - fol_conv_assoc op data in
  if n = 0 then th
  else TRANS th (happ_n_conv n tm');;

let get_mindata (asms, gl) =
  let (cmin, vmin) = itlist get_minarg (gl :: asms) ([],[]) in
  let correct_min (c, min1) =
    let ty = get_const_type c in
    let min2 = length (fst (splitlist dest_fun_ty ty)) in
    (c, min min1 min2)
  in
  let cmin = map correct_min cmin in (cmin, vmin)
;;

let FOL_CONV2 tm =
  let mindata = get_mindata ([], tm) in
  FOL_CONV mindata tm;;

let FOL_TAC2 ((ps,gl) as gs) =
  let mindata = get_mindata (map (concl o snd) ps, gl) in
  (CONV_TAC (FOL_CONV mindata) THEN
  RULE_ASSUM_TAC (CONV_RULE (FOL_CONV mindata))) gs;;

(* Combined FOLification *)
let FOL_IT_TAC = CONV_TAC PRED_ARG_CONV THEN RULE_ASSUM_TAC(CONV_RULE PRED_ARG_CONV) THEN FOL_TAC2;;

(* Escapes characters not accepted by the TPTP format *)
let escaped s =
  let n = ref 0 in
  for i = 0 to String.length s - 1 do
    n := !n + (match String.get s i with
    | '_' | '+' | '-' | '*' | '/' | '\\' | '!' | '?' | ',' | '@'
    | '<' | '>' | '$' | '%' | '\'' | '=' | '.' | '~' -> 2 | c -> 1)
  done;
  if !n = String.length s then s else begin
    let s' = Bytes.create !n in
    n := 0;
    for i = 0 to String.length s - 1 do begin
      match String.get s i with
      | '_' -> Bytes.set s' !n 'u'; incr n; Bytes.set s' !n '_'
      | '+' -> Bytes.set s' !n 'p'; incr n; Bytes.set s' !n '_'
      | '-' -> Bytes.set s' !n 'm'; incr n; Bytes.set s' !n '_'
      | '*' -> Bytes.set s' !n 't'; incr n; Bytes.set s' !n '_'
      | '/' -> Bytes.set s' !n 's'; incr n; Bytes.set s' !n '_'
      | '\\'-> Bytes.set s' !n 'b'; incr n; Bytes.set s' !n '_'
      | '!' -> Bytes.set s' !n 'e'; incr n; Bytes.set s' !n '_'
      | '?' -> Bytes.set s' !n 'q'; incr n; Bytes.set s' !n '_'
      | ',' -> Bytes.set s' !n 'c'; incr n; Bytes.set s' !n '_'
      | '@' -> Bytes.set s' !n 'h'; incr n; Bytes.set s' !n '_'
      | '<' -> Bytes.set s' !n 'l'; incr n; Bytes.set s' !n '_'
      | '>' -> Bytes.set s' !n 'g'; incr n; Bytes.set s' !n '_'
      | '$' -> Bytes.set s' !n 'd'; incr n; Bytes.set s' !n '_'
      | '%' -> Bytes.set s' !n 'r'; incr n; Bytes.set s' !n '_'
      | '=' -> Bytes.set s' !n 'a'; incr n; Bytes.set s' !n '_'
      | '\''-> Bytes.set s' !n 'i'; incr n; Bytes.set s' !n '_'
      | '.' -> Bytes.set s' !n 'o'; incr n; Bytes.set s' !n '_'
      | '~' -> Bytes.set s' !n 'w'; incr n; Bytes.set s' !n '_'
      | c -> Bytes.set s' !n c
    end; incr n; done;
    Bytes.to_string s'
  end;;

(* Less explosive version of POLY_ASSUME_TAC *)
let rec fold_cs fn tm sofar =
  try let l,r = try dest_forall tm with Failure _ ->
                try dest_exists tm with Failure _ ->
                    dest_abs tm in fold_cs fn r sofar
  with Failure _ -> try
      let l,r = try dest_conj tm with Failure _ ->
                try dest_disj tm with Failure _ ->
                    dest_imp tm in
      fold_cs fn r (fold_cs fn l sofar)
  with Failure _ -> try
      let tm = dest_neg tm in fold_cs fn tm sofar
  with Failure _ -> if is_eq tm then (* eq is last *)
      let (c, [l; r]) = strip_comb tm in
      fn (dest_const c) (fold_cs fn r (fold_cs fn l sofar))
  else try
      let l, r = dest_comb tm in
      fold_cs fn r (fold_cs fn l sofar)
  with Failure _ ->
    if is_var tm then sofar else fn (dest_const tm) sofar;;


let insts_as gcs tm =
  let fold_fun (n, ty) insts =
    try
      let tys = List.assoc n gcs in
      let inst_fun gty inst =
        try [type_match ty gty inst] with _ -> [] in
      let gty_fun gty = List.concat (map (inst_fun gty) insts) in
      let ret = List.concat (map gty_fun tys) in
      if ret = [] then insts else ret
    with Not_found -> insts
  in
  fold_cs fold_fun tm [[]]
;;

let rec uniq' eq = fun l ->
  match l with
    x::(y::_ as t) -> let t' = uniq' eq t in
    if eq x y then t' else
    if t'==t then l else x::t'
  | _ -> l;;

let polymorph gcs th =
  let tyins = insts_as gcs (concl th) in
  let setify' le eq s = uniq' eq (sort le s) in
  let ths' =
    setify' (fun th th' -> dest_thm th <= dest_thm th')
            equals_thm (mapfilter (C INST_TYPE th) tyins) in
  if ths' = [] then ([th])
  else ths';;

let gl_constants tms =
  let fold_fun (n, ty) cs =
    try (n, (insert ty (List.assoc n cs))) :: (List.remove_assoc n cs)
    with Not_found -> (n, [ty]) :: cs
  in
  let consts = itlist (fun tm sofar -> fold_cs fold_fun tm sofar) tms [] in
  filter (fun (n, tys) -> length (tyvars (get_const_type n)) > 0) (setify consts)
;;

let POLY_ASSUME_TAC names ths (asl,w as gl) =
  let gcs = gl_constants (w :: map (concl o snd) asl) in
  let ths = map (polymorph gcs) ths in
  let ths2 = List.combine names ths in
  let map_fun (n, ts) =
    if List.length ts = 1 then [(n, List.hd ts)] else
    let fold_fun (cno, clst) t =
      (cno + 1, (n ^ "_monomorphized" ^ string_of_int cno, t) :: clst) in
    snd (List.fold_left fold_fun (0, []) ts)
  in
  let ths3 = List.map map_fun ths2 in
  let ths4 = List.concat ths3 in
(*  let names, ths' = List.split ths4 in*)
  MAP_EVERY (fun (n, th) -> LABEL_TAC (escaped n) th) ths4 gl;;

let LABEL_ASSUME_TAC names ths =
  MAP_EVERY (fun (n, th) -> LABEL_TAC (escaped n) th) (zip names ths);;

(* LAMBDA_ELIM_CONV2 does less explosive lambda-lifting than LAMBDA_ELIM_CONV
   for universally quantified theorems; all the quantified variables do not
   need to be arguments of function that replaces the lambda expression. *)
let LAMBDA_ELIM_CONV2 =
  let HALF_MK_ABS_CONV =
    let pth = prove
     (`(s = \x. t x) <=> (!x. s x = t x)`,
      REWRITE_TAC[FUN_EQ_THM]) in
    let rec conv vs tm =
      if vs = [] then REFL tm else
      (GEN_REWRITE_CONV I [pth] THENC BINDER_CONV(conv (tl vs))) tm in
    conv in
  let rec find_lambda tm =
    if is_abs tm then tm
    else if is_var tm || is_const tm then failwith "find_lambda"
    else if is_abs tm then tm else
    if is_forall tm || is_exists tm || is_uexists tm
    then find_lambda (body(rand tm)) else
    let l,r = dest_comb tm in
    try find_lambda l with Failure _ -> find_lambda r in
  let rec ELIM_LAMBDA conv tm =
    try conv tm with Failure _ ->
    if is_abs tm then ABS_CONV (ELIM_LAMBDA conv) tm
    else if is_var tm || is_const tm then REFL tm else
    if is_forall tm || is_exists tm || is_uexists tm
    then BINDER_CONV (ELIM_LAMBDA conv) tm
    else COMB_CONV (ELIM_LAMBDA conv) tm in
  let APPLY_PTH =
    let pth = prove
     (`(!a. (a = c) ==> (P = Q a)) ==> (P <=> !a. (a = c) ==> Q a)`,
      SIMP_TAC[LEFT_FORALL_IMP_THM; EXISTS_REFL]) in
    MATCH_MP pth in
  let LAMB2_CONV tm =
    let atm = find_lambda tm in
    let v,bod = dest_abs atm in
    let vs = subtract (frees atm) (frees tm) in
    let vs' = vs @ [v] in
    let aatm = list_mk_abs(vs,atm) in
    let f = genvar(type_of aatm) in
    let eq = mk_eq(f,aatm) in
    let th1 = SYM(RIGHT_BETAS vs (ASSUME eq)) in
    let th2 = ELIM_LAMBDA(GEN_REWRITE_CONV I [th1]) tm in
    let th3 = APPLY_PTH (GEN f (DISCH_ALL th2)) in
    CONV_RULE(RAND_CONV(BINDER_CONV(LAND_CONV (HALF_MK_ABS_CONV vs')))) th3 in
  let rec conv tm =
    try (LAMB2_CONV THENC conv) tm with Failure _ -> REFL tm in
  conv;;
