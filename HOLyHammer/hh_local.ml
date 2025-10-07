(* Given a list of jobs to run (('a -> unit) -> 'b),
  a timeout (float) and a function to report progress ('a -> unit)
  returns the result (Some) of first one that finishes within
  this timeout and kills the rest or returns None if none
  finished in time or all failed. Additionally the job may
  call the function 'progress' in the original process and
  every second pr_fun is called. *)
type ('a, 'b) sum = Inl of 'a | Inr of 'b | Err of int;;

let subprocesses = ref [];;

let handle_term _ =
  List.iter (fun i -> try Unix.kill i Sys.sigterm with _ -> ()) !subprocesses; exit 0;;
Sys.set_signal Sys.sigterm (Sys.Signal_handle handle_term);;

let run_parallel (progress_fn : 'a -> unit) (sec_fn : unit -> unit)
    time (lst : (('a -> unit) -> 'b) list) =
  let piper, pipew = Unix.pipe () in
  let start f =
    let pid = Unix.fork () in
    let oc = Unix.out_channel_of_descr pipew in
    if pid = 0 then begin try
      Unix.close piper;
      let progress_sub_fn a =
        output_value oc (Inl a); flush oc
      in
      let ret = f progress_sub_fn in
      output_value oc (Inr ret);
      flush oc;
      exit 0
    with _ ->
      try output_value oc (Err (Unix.getpid ())); flush oc; exit 0
      with _ -> exit 0
    end; pid
  in
  subprocesses := List.map start lst;
  Unix.close pipew;
  let rec select desc time =
    if time <= 0. then 0. else
    let (r, _, _) = Unix.select [desc] [] [] 1. in
    if r <> [] then time else (sec_fn (); select desc (time -. 1.))
  in
  Unix.set_nonblock piper;
  let inc = Unix.in_channel_of_descr piper in
  let rec ret time =
    if !subprocesses = [] then None else
    let interp time = function
      | Inl pr -> progress_fn pr; ret time
      | Inr ret -> Some (ret)
      | Err pid ->
          subprocesses := List.filter (fun i -> i <> pid) !subprocesses;
          ignore (Unix.waitpid [] pid);
          ret time
    in
    try interp time (input_value inc) with Sys_blocked_io | Unix.Unix_error _ ->
    let ntime = select piper time in
    if ntime > 0. then interp ntime (input_value inc) else None
  in
  let ret = ret time in
  List.iter (fun i -> try Unix.kill i Sys.sigterm with _ -> ()) !subprocesses;
  Unix.close piper;
  List.iter (fun i -> try ignore (Unix.waitpid [] i) with _ -> ()) !subprocesses;
  subprocesses := [];
  (ret : 'b option)
;;

let run_prover fname prover =
  let cmd = match prover with
    1 -> "vampire --mode casc -t 30 --proof tptp --output_axiom_names on " ^ fname
  | 2 -> "z3 -tptp DISPLAY_UNSAT_CORE=true -T:30 " ^ fname
  | 3 -> "eproof --cpu-limit=30 --tstp-format " ^ fname
  | _ -> "HOLyHammer/runepar.pl 30 0 " ^ fname ^ " 2 1"
  in
  let fnameo = fname ^ string_of_int prover ^ "o" in
  let cmd = cmd ^ " > " ^ fnameo ^ " 2> /dev/null" in
  ignore (Sys.command cmd);
  let ret = Sys.command ("grep -q 'status Theorem' " ^ fnameo) in
  if ret <> 0 then failwith "No proof" else
  let cmd = (if prover = 2 then "HOLyHammer/depsz3.sh " else "HOLyHammer/deps.sh ") ^ fnameo ^ " > " ^ fnameo ^ "d" in
  ignore (Sys.command cmd);
  string_list_of_string (string_of_file (fnameo ^ "d")) ' '
;;

let hh_advice port max prover (asm, gl) _ =
  let syms = get_symbolst (itlist (curry mk_imp) asm gl) in
  let symnos = List.fold_left (fun acc s -> try sym_no s :: acc with Not_found -> acc) [] syms in
  let advnames = List.map no_th (asksnown port max symnos) in
  let advths = List.map find_thm advnames in
  let (premnames, _) = List.fold_left (fun (l, no) _ ->
    (("GOALPREMISE" ^ string_of_int no) :: l, no + 1)) ([], 0) asm in
  let adv2t = List.map (fun x -> mk_fthm ([], x)) asm in
  let rname = Printf.sprintf "atp%i%i%i%i" port max prover (Hashtbl.hash (asm, gl)) in
  let fname = Filename.temp_file rname ".p" in
  write_atp_proof fname (adv2t @ advths, premnames @ advnames) "advised" gl;
  run_prover fname prover
;;

let count_time stime =
  Printf.sprintf "%.2f" (Unix.gettimeofday () -. stime);;

let prove_asm_gl ((asm, gl), tac)=
  let gl = itlist (curry mk_imp) asm gl in
  prove(gl, EVERY (replicate DISCH_TAC (length asm)) THEN tac)
;;

let hh_decision_procedure ((asm, gl) as tm2) =
  let stime = Unix.gettimeofday () in
  let jobs = [(fun _ -> ignore (prove_asm_gl(tm2, CONV_TAC TAUT)); "CONV_TAC TAUT");
    (fun _ -> ignore(prove_asm_gl(tm2, INT_ARITH_TAC)); "INT_ARITH_TAC");
    (fun _ -> ignore(prove_asm_gl(tm2, SIMP_TAC[ARITH])); "SIMP_TAC[ARITH]")] in
  let jobs = if asm = [] then jobs else
    (fun _ -> ignore(prove_asm_gl(tm2, ASM_INT_ARITH_TAC)); "ASM_INT_ARITH_TAC") :: jobs in
  match run_parallel (fun () -> ()) (fun () -> ()) 30. jobs with
    Some s -> ("* Replaying: SUCCESS (" ^ count_time stime ^ "s): " ^ s)
  | None -> failwith "hh_decision_procedure failed";;

let rec hh_minimize res sec_fn (asm, gl) =
  let fname = "/tmp/atpm" ^ string_of_int (Hashtbl.hash (res, asm, gl)) ^ ".p" in
  let adv = rev (List.fold_left (fun l n -> try (find_thm n, n) :: l with Not_found ->
    if String.length n > 11 && String.sub n 0 11 = "GOALPREMISE" then
      let i = int_of_string (String.sub n 11 (String.length n - 11)) in
      (mk_fthm ([], (List.nth asm i)), n) :: l else failwith "minimize bug!")
      [] res) in
  write_atp_proof fname (List.split adv) "minim" gl;
  let minimize_prover p _ =
    let ret = run_prover fname p in
    let len = length ret in
    if len < length res then ret else failwith "same"
  in
  match run_parallel (fun () -> ()) (fun () -> Printf.printf ".%!") 10.
    [minimize_prover 0; minimize_prover 1; minimize_prover 3] with
    | None -> res
    | Some ret -> hh_minimize ret (fun () -> Printf.printf ".%!") (asm, gl)
;;

let clean_name s = Str.global_replace (Str.regexp "_conjunct[0-9]*") "" s;;
let clean_names l = uniq (sort (fun x y -> compare x y > 0) (List.map clean_name l));;

let hh_replay ret sec_fn (asm, gl) =
  let pnames, tnames = List.partition
    (fun n -> String.length n > 11 && String.sub n 0 11 = "GOALPREMISE") ret in
  let tnames = clean_names tnames in
  let tnameb = "[" ^ String.concat ";" tnames ^ "]" in
  let ths = List.map find_thm tnames in
  let jobs =
    [(fun _ -> ignore(prove_asm_gl((asm,gl), REWRITE_TAC ths)); ("REWRITE_TAC" ^ tnameb));
     (fun _ -> ignore(prove_asm_gl((asm,gl), SIMP_TAC ths)); ("SIMP_TAC" ^ tnameb));
     (fun _ -> verbose:=false;ignore(prove_asm_gl((asm,gl), MESON_TAC ths)); ("MESON_TAC" ^ tnameb))] in
  let jobs = if pnames = [] then jobs else jobs @
    [(fun _ -> ignore(prove_asm_gl((asm,gl), ASM_REWRITE_TAC ths)); ("ASM_REWRITE_TAC" ^ tnameb));
     (fun _ -> ignore(prove_asm_gl((asm,gl), ASM_SIMP_TAC ths)); ("ASM_SIMP_TAC" ^ tnameb));
     (fun _ -> verbose:=false;ignore(prove_asm_gl((asm,gl), ASM_MESON_TAC ths)); ("ASM_MESON_TAC" ^ tnameb))] in
  match run_parallel (fun () -> ()) sec_fn 10. jobs with
    None -> failwith "Reconstruction failed"
  | Some s -> s
;;

let hh_advices gs prfun =
  match run_parallel (fun () -> ()) (fun () -> ()) 30.
    [hh_advice 60000 128 0 gs; hh_advice 60000 92 1 gs; hh_advice 60000 64 2 gs;
     hh_advice 60001 128 0 gs; hh_advice 60001 92 1 gs; hh_advice 60001 64 2 gs]
  with None -> failwith "No advice"
     | Some lret ->
       prfun ("ATP success: " ^ (String.concat " " lret) ^ "\n");
       let mret = hh_minimize lret (fun () -> Printf.printf ".%!") gs in
       if mret <> lret then prfun ("Minimized: " ^ String.concat " " mret ^ "\n");
       let repl = hh_replay mret (fun () -> Printf.printf ".%!") gs in
       "Reconstructed: " ^ repl
;;

let (HH_ADVICE_TAC : tactic) = fun (ps, gl) ->
  let gs = (map (concl o snd) ps, gl) in
  match run_parallel (fun s -> Printf.printf "%s%!" s) (fun () -> Printf.printf ".%!") 120.
    [hh_advices gs; fun _ -> hh_decision_procedure gs] with
    None -> failwith "No more advice"
  | Some s -> Printf.printf "%s\n%!" s; raise Exit
;;
