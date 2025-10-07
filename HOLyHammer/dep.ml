let facts = Hashtbl.create 10000;;
let facts_rev = Hashtbl.create 10000;;
let unprovable = Hashtbl.create 10000;;
let space = Str.regexp " ";;
let colon = Str.regexp ":";;
let unprove s = (s = "-");;

let addfact s n =
  (if unprove s then Hashtbl.replace unprovable n () else ());
  if Hashtbl.mem facts_rev n then () else
  try if Hashtbl.find facts s = n then () else failwith ("factrepeat: " ^ s)
  with Not_found ->
    if s <> "-" then Hashtbl.replace facts s n else ();
    if Hashtbl.mem facts_rev n then () else Hashtbl.add facts_rev n s in
let inc = open_in "facts.lst" in
begin try while true do
  let l = Str.split space (input_line inc) in
  let no = int_of_string (List.nth l 1) in
  addfact (List.hd l) no
done with End_of_file -> close_in inc end;;

let conj_hash = Hashtbl.create 10000;;
let inc = open_in "conjs" in
begin try while true do
  let l = input_line inc in
  let [t; r] = Str.split colon l in
  let ts = Str.split space r in
  Hashtbl.replace conj_hash t ts
done with End_of_file -> close_in inc end;;

let tyno = ref 0;;
let tmno = ref 0;;
let thno = ref 0;;
let ios s = abs(int_of_string s);;

let process thth thtm tmtm thty tmty tyty = function
  ('R', [t]) -> incr thno; thtm (ios t)
| ('B', [t]) -> incr thno; thtm (ios t)
| ('T', [p; q]) -> incr thno; thth (ios p); thth (ios q)
| ('C', [p; q]) -> incr thno; thth (ios p); thth (ios q)
| ('L', [t; p]) -> incr thno; thth (ios p); thtm (ios t)
| ('H', [t]) -> incr thno; thtm (ios t)
| ('E', [p; q]) -> incr thno; thth (ios p); thth (ios q)
| ('D', [p; q]) -> incr thno; thth (ios p); thth (ios q)
| ('Q', ((h :: t) as l)) -> incr thno; thth (ios (List.hd (List.rev l)));
    List.iter thty (List.map ios (List.tl (List.rev l)))
| ('S', ((h :: t) as l)) -> incr thno; thth (ios (List.hd (List.rev l)));
    List.iter thtm (List.map ios (List.tl (List.rev l)))
| ('A', [_; t]) -> incr thno; thtm (ios t)
| ('F', [_; t]) -> incr thno; thtm (ios t)
| ('Y', [_; _; _; t; s; p]) -> incr thno; thth (ios p); thtm (ios t); thtm (ios s)
| ('1', [p]) -> incr thno; thth (ios p)
| ('2', [p]) -> incr thno; thth (ios p)
| ('t', [_]) -> incr tyno
| ('a', (h :: t)) -> incr tyno; List.iter tyty (List.map ios t)
| ('v', [_; ty]) -> incr tmno; tmty (ios ty)
| ('c', [_; ty]) -> incr tmno; tmty (ios ty)
| ('f', [t; s]) -> incr tmno; tmtm (ios t); tmtm (ios s)
| ('l', [t; s]) -> incr tmno; tmtm (ios t); tmtm (ios s)
| (c, l) -> failwith ((String.make 1 c) ^ (String.concat " " l))
;;

let max = Hashtbl.fold (fun _ i m -> max i m) facts 0;;
(*print_int max;;*)
let thth = Array.init (max + 2) (fun _ -> []);;

let rec merge l1 l2 =
  match l1, l2 with
  | [], l2 -> l2
  | l1, [] -> l1
  | h1 :: t1, h2 :: t2 ->
      if h1 = h2 then h1 :: merge t1 t2 else
      if h1 < h2 then h1 :: merge t1 l2
                 else h2 :: merge l1 t2
;;

(* s is smaller than thno *)
let addthth s =
  if Hashtbl.mem facts_rev s then
    thth.(!thno) <- merge [s] (thth.(!thno))
  else
    thth.(!thno) <- merge (thth.(s)) (thth.(!thno));;

let process_all thth thtm tmtm thty tmty tyty =
  tyno := 0; tmno := 0; thno := 0;
  let inc = open_in "proofs" in
  try while true do
      let c = input_char inc in
      let s = input_line inc in
      process thth thtm tmtm thty tmty tyty (c, (Str.split space s));
      if !thno > max then raise End_of_file
    done
  with End_of_file -> close_in inc;;

process_all addthth (fun _ -> ()) (fun _ -> ()) (fun _ -> ()) (fun _ -> ()) (fun _ -> ());;

let oc = open_out "deps.all";;

let fof_no_need = ref (List.map (Hashtbl.find facts)
  ["T_DEF";"AND_DEF";"IMP_DEF";"FORALL_DEF";"EXISTS_DEF"; "OR_DEF";"F_DEF";"NOT_DEF"]);;
(*List.iter (fun s -> Hashtbl.add unprovable s ()) (List.map (Hashtbl.find facts) 
  ["TRUTH"; "NOT_CLAUSES_conjunct2"; "NOT_CLAUSES_conjunct1"]);;*)

let subtract l1 l2 = List.filter (fun x -> not (List.mem x l2)) l1;;

let don = Hashtbl.create 100;;
for i = 1 to max do
  try
    let name = Hashtbl.find facts_rev i in
    if unprove name then raise Not_found else (); (* Not really named *)
    if Hashtbl.mem don name then raise Not_found else (); (* Already written *)
    let odeps = subtract (thth.(i)) !fof_no_need in
    if odeps = [] && not (Hashtbl.mem unprovable i) then fof_no_need := i :: !fof_no_need else ();
    let deps = List.map (Hashtbl.find facts_rev) odeps in
    let rec unfold n = try List.concat (List.map unfold (Hashtbl.find conj_hash n)) with Not_found -> [n] in
    let deps =
      if List.fold_left (fun sofar n -> sofar || unprove n) (Hashtbl.mem unprovable i) deps then ["-"]
      else List.fold_left (fun sofar n -> unfold n @ sofar) [] deps
    in
    let lhs =
      try
        let cnjs = Hashtbl.find conj_hash name in
        let after = List.filter (fun ci -> (try Hashtbl.find facts ci > i with Not_found -> false) && not (Hashtbl.mem don ci)) cnjs in
        let noex = List.filter (fun ci -> not (Hashtbl.mem facts ci) && not (Hashtbl.mem don ci)) cnjs in
        List.iter (fun ci -> Hashtbl.add don ci ()) (after @ noex);
        after @ noex
      with Not_found -> [name] in
    List.iter (fun l -> output_string oc l; output_char oc ':';
      output_string oc (String.concat " " deps); output_char oc '\n') lhs
  with Not_found -> ()
done;;
close_out oc;;
