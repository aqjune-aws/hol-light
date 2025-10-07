#load "unix.cma";;
#load "str.cma";;

let th_no, no_th, deps, th_num =
  let inc = open_in "HOLyHammer/deps.all" in
  let splrxp = Str.regexp "[: ]" in
  let th_no = Hashtbl.create 1000
  and no_th = Hashtbl.create 1000
  and deps = Hashtbl.create 1000
  and nextth = ref 0 in
  begin try while true do
    let l = input_line inc in
    match Str.split splrxp l with
      [] -> failwith "HOLyHammer/deps.all incorrect!"
    | h :: d ->
      Hashtbl.replace th_no h !nextth;
      Hashtbl.replace no_th !nextth h;
      let d = if d = ["-"] then [] else d in
      let ds = List.map (fun s -> try Hashtbl.find th_no s with Not_found ->
        failwith ("HOLyHammer/deps.all dependency before item: " ^ s)) d in
      Hashtbl.replace deps !nextth ds;
      incr nextth
  done with End_of_file -> close_in inc end;
  (Hashtbl.find th_no, Hashtbl.find no_th, Hashtbl.find deps, !nextth)
;;

let sym_no, syms =
  let sym_no = Hashtbl.create 10000 in
  let syms = Hashtbl.create 10000 in
  let inc = open_in "HOLyHammer/symst" in
  let splrxp = Str.regexp "\", \"" in
  let nextsym = ref 1000000 in
  let find_sym s =
    try Hashtbl.find sym_no s
    with Not_found -> Hashtbl.add sym_no s !nextsym;
      incr nextsym; (!nextsym - 1)
  in
  begin try while true do
    let l = input_line inc in
    let co = String.index l ':' in
    let thn = String.sub l 0 co in
    let th = try th_no thn with Not_found ->
      failwith ("HOLyHammer/symst: missing dep: " ^ thn) in
    let s2 = String.sub l (co + 2) (String.length l - co - 3) in
    let ss = List.map find_sym (Str.split splrxp s2) in
    Hashtbl.replace syms th ss
  done with End_of_file -> close_in inc end;
  (Hashtbl.find sym_no, Hashtbl.find syms)
;;

let unfind_thm =
  let hash = Hashtbl.create 10000 in
  List.iter (fun (n,t) -> if not (is_conj (concl t)) then
      Hashtbl.add hash t n) !theorems;
  (fun s -> Hashtbl.find_all hash s);;

let unfind_thm_best s =
  let l = unfind_thm s in
  List.fold_left (fun a e -> try ignore (th_no e); e :: a with Not_found -> a) [] l
;;

let regexp = Str.regexp "\(.*\)_conjunct\(.*\)";;
let find_thm n =
  if Str.string_match regexp n 0 then
    let th = List.assoc (Str.matched_group 1 n) !theorems in
    List.nth (CONJUNCTS th) (int_of_string (Str.matched_group 2 n))
  else List.assoc n !theorems;;

(* For atp dependencies with different chosen names; try to find those theorems *)
let th_no_fix s =
  try th_no s with Not_found ->
  match unfind_thm_best (find_thm s) with
    [s] -> th_no s
  | _ -> raise Not_found
;;

let adeps =
  let hsh = Hashtbl.create 10000 in
  try
    let inc = open_in "HOLyHammer/atpdeps" in
    let splrxp = Str.regexp " " in
    let num = ref 0 and uses = ref 0 in
    begin try while true do
      let l = input_line inc in
      try
        incr num;
        let co = String.index l ':' in
        let s = th_no_fix (String.sub l 0 co) in
        let s2 = String.sub l (co + 1) (String.length l - co - 1) in
        let ss = List.map th_no_fix (Str.split splrxp s2) in
        Hashtbl.replace hsh s ss; incr uses
      with Not_found -> ()
    done with End_of_file -> close_in inc end;
    Printf.printf "Found %i atpdeps; usable: %i\n%!" !num !uses;
    Hashtbl.find hsh
  with Sys_error _ -> Hashtbl.find hsh;;

let fix_adeps fnamel fname =
  let a = Array.init th_num (fun _ -> []) in
  let splrxp = Str.regexp " " in
  let read_fname fname =
    let inc = open_in fname in
    try while true do
    let l = input_line inc in
    try
      let co = String.index l ':' in
      let s = th_no_fix (String.sub l 0 co) in
      let s2 = String.sub l (co + 1) (String.length l - co - 1) in
      let ss = List.map th_no_fix (Str.split splrxp s2) in
      if List.filter (fun n -> n >= s) ss = [] then
      a.(s) <- ss :: a.(s)
    with Not_found -> ()
    done with End_of_file -> close_in inc
  in
  List.iter read_fname fnamel;
  let oc = open_out fname in
  for i = 0 to th_num - 1 do
    let write_line l =
      output_string oc (no_th i); output_char oc ':';
      output_string oc (String.concat " " (List.map no_th l));
      output_char oc '\n';
    in
    List.iter write_line a.(i)
  done;
  close_out oc
;;


let output_int oc n = output_string oc (string_of_int n);;
let rec oss oc = function
  [] -> () | [h] -> output_int oc h | h :: t -> output_int oc h; output_char oc ','; oss oc t;;

let process_deps fname pfun =
  let oc = open_out fname in
  for r = 0 to th_num - 1 do
    oss oc (pfun r); output_string oc ":\n"; flush oc
  done;
  close_out oc;;

let process_hum r = List.rev_append (syms r) (r :: (deps r));;
let process_atp r = List.rev_append (syms r) (r :: (try adeps r with Not_found -> []));;

let testsyms = ["num"; "fun"; "bool"; "_0"; "NUMERAL"; "BIT1"; "="; "+"; "0"; "1"; "BIT1 _0"; "_0"];;

let recvstrfrom inc =
  let len = input_binary_int inc in
  let s = String.init len (fun _ -> input_char inc) in
  s
;;

let recvlstfrom inc max =
  let len = input_binary_int inc in
  let rec more n max =
    if (0 >= n) || (max = 0) then [] else
      let l = input_line inc in
      try
        let cp = String.index l ':' in
        int_of_string (String.sub l 0 cp) :: more (n - String.length l - 1) (max - 1)
      with Not_found | Failure "int_of_string" -> more (n - String.length l - 1) max
  in more len max
;;

Sys.signal Sys.sighup Sys.Signal_ignore;;
Sys.signal Sys.sigpipe Sys.Signal_ignore;;

unset_jrh_lexer;;
let unix_pfinet = Unix.PF_INET;;
let unix_sockstream = Unix.SOCK_STREAM;;
let unix_addrinet (a, b) = Unix.ADDR_INET (a,b);;
let unix_wnohang = Unix.WNOHANG;;
let unix_uninet (Unix.ADDR_INET (a,b)) = (a,b);;
set_jrh_lexer;;

let asksnown port max symnos =
  let ssock = Unix.socket unix_pfinet unix_sockstream 0 in
  Unix.connect ssock (unix_addrinet (Unix.inet_addr_of_string "127.0.0.1", port));
  let sinc, soutc = Unix.in_channel_of_descr ssock, Unix.out_channel_of_descr ssock in
  let params = "-o allboth" in let plen = String.length params in
  set_binary_mode_out soutc true;
  output_binary_int soutc plen; output_string soutc params; flush soutc;
  ignore (recvstrfrom sinc);
  let msgo = String.concat "," (List.map string_of_int symnos) ^ ":" in
  output_binary_int soutc (String.length msgo);
  output_string soutc msgo; flush soutc;
  let ret = recvlstfrom sinc max in
  output_binary_int soutc 0; flush soutc;
  (try Unix.close ssock with _ -> ());
  ret
;;
