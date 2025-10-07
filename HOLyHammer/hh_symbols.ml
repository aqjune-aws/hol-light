#load "str.cma";;
module Sm = Map.Make(struct type t = string let compare = compare end);;
module Tmm = Map.Make(struct type t = term let compare = compare end);;
let os = output_string;;

let print_to_lstring printer =
  let sbuff = ref "" in
  let output s m n = if s <> "\n" then sbuff := (!sbuff)^(String.sub s m n) else ()
  and flush() = () in
  let fmt = make_formatter output flush in
  pp_set_max_boxes fmt 1; pp_set_margin fmt 1000000000; pp_set_max_indent fmt 1000000000;
  fun i -> ignore(printer fmt i); ignore(pp_print_flush fmt ()); let s = !sbuff in sbuff := ""; s
;;
let lstring_of_type = print_to_lstring pp_print_type;;
let lstring_of_term = print_to_lstring pp_print_term;;
let lstring_of_thm = print_to_lstring pp_print_thm;;

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

let funtys_of_tm tm =
  let mergel l = setify (List.concat l) in
  let tys tm = map type_of (find_terms (fun x -> is_var x || is_const x) tm) in
  let rec funtypes t =
    if is_vartype t then [] else
    let (s, l) = dest_type t in
    mergel ([s]::(map funtypes l)) in
  mergel (map funtypes (tys tm))
;;

let rec rename_bnds map min tm prfun =
  try let l, r = dest_abs tm in
    let _, ty = dest_var l in
    let nl = mk_var (prfun min ty, ty) in
    mk_abs (nl, rename_bnds (Tmm.add l nl (Tmm.remove l map)) (min + 1) r prfun)
  with _ -> try let l, r = dest_comb tm in
    mk_comb (rename_bnds map min l prfun, rename_bnds map min r prfun)
  with _ -> try Tmm.find tm map with _ -> tm
;;
let rename_all tm prfun =
  let fs = frees tm in
  let tys = map (snd o dest_var) fs in
  let s = Array.to_list (Array.init (length fs) (fun i -> prfun i (List.nth tys i))) in
  let nfs = map mk_var (zip s tys) in
  rename_bnds Tmm.empty (length fs) (vsubst (zip nfs fs) tm) prfun
;;
let get_subterms tm prfun =
  let fold_apps_fn _ hop args ts =
    Sm.add (lstring_of_term (rename_all (list_mk_comb (hop, args)) prfun)) () ts
  in map fst (Sm.bindings (fold_apps fold_apps_fn [] tm Sm.empty))
;;

let prfun0 min ty = "A0";;
let prfun min ty = "A" ^ string_of_int min;;
let prfunt min ty = "A" ^ lstring_of_type ty;;

let retyvar tm =
  let tvs = type_vars_in_term tm in
  let ins = List.map (fun x -> (`:A`,x)) tvs in
  inst ins tm
;;

let get_symbols tm =
  let cns = find_terms (fun x -> is_const x) tm in
  let names = subtract (setify (map (fst o dest_const) cns)) ["!";"?";"/\\";"\\/";"==>"] in
  let tys = funtys_of_tm tm in
  let subs0 = get_subterms tm prfun0 in
  let subss = get_subterms tm prfun in
  let subst = get_subterms (retyvar tm) prfunt in
  let subsd = get_subterms tm prfunt in
  let r0 = List.rev_append tys (List.rev_append names subs0) in
  let rs = List.rev_append tys (List.rev_append names subss) in
  let rt = List.rev_append tys (List.rev_append names subst) in
  let rd = List.rev_append tys (List.rev_append names subsd) in
  ((r0, rs), (rt, rd))
;;

let get_symbolst tm = fst (snd (get_symbols tm));;

let name2pairs acc (name, th) =
  if is_conj (concl th) then
    let fold_fun (no, acc) th = (no + 1, (name ^ "_conjunct" ^ (string_of_int no), th) :: acc) in
    snd (List.fold_left fold_fun (0, acc) (CONJUNCTS th))
  else (name, th) :: acc
;;

let write_symbols_theorems () =
  let hash = Hashtbl.create 17000 in
  let all_thms = List.fold_left name2pairs [] !theorems in
  List.iter (fun (a, b) -> Hashtbl.add hash b a) all_thms;
  let regex = Str.regexp "_conjunct" in
  let best_name l =
    if List.length l = 1 then List.hd l else
    let nodot = List.filter (fun s -> not (String.contains s '.')) l in
    let l = if List.length nodot > 0 then nodot else l in
    if List.length l = 1 then List.hd l else
    let nocon = List.filter (fun s -> try ignore (Str.search_forward regex s 0);
      false with Not_found -> true) l in
    let l = if List.length nocon > 0 then nocon else l in
    List.hd l
  in
  let names = Hashtbl.create 17000 in
  Hashtbl.iter (fun k _ -> Hashtbl.replace names k (best_name (Hashtbl.find_all hash k))) hash;
  let thms = Hashtbl.fold (fun k n l -> (n, k) :: l) names [] in
  let (oc0,ocs,oct,ocd,ocu) =
    open_out "HOLyHammer/syms0",open_out "HOLyHammer/symss",open_out "HOLyHammer/symst",
    open_out "HOLyHammer/symsd",open_out "HOLyHammer/symsu" in
  let out_oc oc thn l =
    os oc thn; output_char oc ':';
    if l <> [] then (
    output_char oc '\"';
    os oc (String.concat "\", \"" l);
    os oc "\"\n") else output_char oc '\n' in
  let out_tm (thn, th) =
    let (asms, gl) = dest_thm th in
    let tm = itlist (curry mk_imp) asms gl in
    let ((s0,ss),(st,sd)) = get_symbols tm in
    out_oc oc0 thn s0;
    out_oc ocs thn ss;
    out_oc oct thn st;
    out_oc ocd thn sd;
    out_oc ocu thn (setify (List.concat [s0; ss; st]));
  in
  List.iter out_tm (thms);
  close_out oc0; close_out ocs; close_out oct; close_out ocd; close_out ocu;
  let conjs = List.filter (fun (_, th) -> is_conj (concl th)) !theorems in
  let oc = open_out "HOLyHammer/theorems" in
  output_value oc (List.map (fun (n,t) -> (n,dest_thm t)) (conjs @ thms));
  close_out oc;
  let oc = open_out "HOLyHammer/conjs" in
  let iter_fun (n, th) =
    let ns = setify (List.map (Hashtbl.find names) (CONJUNCTS th)) in
    os oc n; os oc ":"; os oc (String.concat " " ns); os oc "\n"
  in
  List.iter iter_fun conjs;
  close_out oc
;;


