(** Main module *)

open Syntax
open TySyntax
open TyConstraintSolver
open SimpleTyping
open Convert
open CollectConstraint
open Emit
open Z3Syntax
open Z3Syntax2
open CHCcollectConstraint
open CHCemit
open Ownership

let rec main_int_sub_declare oc all_cs bool_id n iter = 
  if n < 0 then 
    ()
  else
    (let (id_count, varown_count, fvs, sls) = all_cs_to_smtlib all_cs n in
    print_declare oc id_count fvs n;
    print_declare_varown oc varown_count fvs n;
    output_string oc "\n";
    main_int_sub_declare oc all_cs bool_id (n-1) iter)

let rec main_int_sub oc all_cs bool_id n iter = 
  if n < 0 then 
    ()
  else
    (let (id_count, varown_count, fvs, sls) = all_cs_to_smtlib all_cs n in
    print_smtlibs oc sls bool_id fvs (-1) iter; 
    output_string oc "\n\n";
    main_int_sub oc all_cs bool_id (n-1) iter)

(** First phase of the ownershipip inference:
    Generates n_1, ..., n_k and checks the validity of \exists y . phi(n_1, y) /\ ... /\ phi(n_k, y) *)
let main_int file iter = 
  let oc_r1 = open_in file in
  let prog = Parser.program Lexer.read (Lexing.from_channel oc_r1) in
  close_in oc_r1;
  let (fdefs, _) = prog in
  let n = List.length fdefs in 
    infer_prog prog;
    let prog' = convert prog in
    let all_cs = collect_prog prog' in 
  
  let oc1 = open_out "experiment/out_int.smt2" in
  main_int_sub_declare oc1 all_cs false n iter;
  main_int_sub oc1 all_cs false n iter;
  output_string oc1 "(check-sat)\n";
  output_string oc1 "(get-model)\n";
  close_out oc1

(** Second phase of the ownershipip inference:
    Checks the validity of \forall x phi(x, a), where a is the witeness for \exist y obtasined in the first phase. *)
let main_fv file =
  let oc_r1 = open_in file  in
  let oc_r2 = open_in "experiment/result_int" in
  let prog = Parser.program Lexer.read (Lexing.from_channel oc_r1) in
  let z3res = Z3Parser.result Z3Lexer.read (Lexing.from_channel oc_r2) in
  close_in oc_r1; close_in oc_r2;
  let (fdefs, _) = prog in
  let n = List.length fdefs in 
    infer_prog prog;
    let prog' = convert prog in
    let all_cs = collect_prog prog' in 
    
  let oc = open_out "experiment/out_fv.smt2" in
    main_int_sub_declare oc all_cs true n 0;
  main_int_sub oc all_cs true n 0;
  print_z3result oc z3res;
  output_string oc "\n\n";
  output_string oc "(check-sat)\n";
  output_string oc "(get-model)\n";
  close_out oc

  
let rec main_chc_sub_declare oc all_chcs n = 
  if n < 0 then 
    ()
  else
    (let oc_r2 = open_in "experiment/result" in
    let z3res = Z3Parser2.result Z3Lexer2.read (Lexing.from_channel oc_r2) in
        close_in oc_r2;
    
    let (id_count, varpred_count, fvs, sls) = all_cs_to_smtlib_chc all_chcs n in
    let args_own_sls = ownexp_to_ownchc varpred_count n in
    let own_sls = collect_ownchc z3res n in 

    print_declare_chc_int oc !intpred_env n;
    print_declare_chc oc id_count n;
    print_declare_varpred oc varpred_count n;
    output_string oc "\n";
    main_chc_sub_declare oc all_chcs (n-1))

let rec main_chc_sub oc all_chcs n = 
  if n < 0 then 
    ()
  else
    (let oc_r2 = open_in @@ "experiment/result" in
    let z3res = Z3Parser2.result Z3Lexer2.read (Lexing.from_channel oc_r2) in
        close_in oc_r2;
    
    let (id_count, varpred_count, fvs, sls) = all_cs_to_smtlib_chc all_chcs n in
    let args_own_sls = ownexp_to_ownchc varpred_count n in
    let own_sls = collect_ownchc z3res n in 

    print_smtlibs oc sls true fvs n 0; 
    output_string oc "\n";
    print_smtlibs oc args_own_sls true fvs n 0; 
    output_string oc "\n";
    print_smtlibs oc own_sls true fvs n 0; 
    output_string oc "\n\n";
    main_chc_sub oc all_chcs (n-1))

(** Main procedure for the refinement inference *)
let main_chc file =
  let oc_r1 = open_in file  in
  let prog = Parser.program Lexer.read (Lexing.from_channel oc_r1) in
  close_in oc_r1; 

  let (fdefs, _) = prog in
  let n = List.length fdefs in 
    infer_prog prog;
    let prog' = convert prog in
    let all_chcs = chc_collect_prog prog' in 
    
  let oc = open_out "experiment/out_chc.smt2" in
    output_string oc "(set-logic HORN)\n\n\n";
  main_chc_sub_declare oc all_chcs n;
  main_chc_sub oc all_chcs n;
  output_string oc "(check-sat)\n";
  output_string oc "(get-model)\n";
  close_out oc

let _ = 
  let input1 = Sys.argv.(1) in
  let input2 = Sys.argv.(2) in
  let input3 = Sys.argv.(3) in
  match input1 with
  | "int" -> main_int input2 (int_of_string input3)
  | "fv" -> main_fv input2
  | "chc" -> main_chc input2
  | _ -> ()
