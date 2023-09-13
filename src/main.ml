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

let main_int file iter = 
  let oc_r1 = open_in file in
  let prog = Parser.program Lexer.read (Lexing.from_channel oc_r1) in
  close_in oc_r1;
  let (fdefs, _) = prog in
  let n = List.length fdefs in 
  (* print_program prog; print_newline (); print_newline (); *)
  infer_prog prog;
  (* print_all_tyenv !all_tyenv; print_newline (); print_newline (); *)
  let prog' = convert prog in
  (* print_program prog'; print_newline (); print_newline (); *)
  let all_cs = collect_prog prog' in 
  (* print_all_constraints all_cs; print_newline (); print_newline (); *)

  let oc1 = open_out "experiment/out_int.smt2" in
  main_int_sub_declare oc1 all_cs false n iter;
  main_int_sub oc1 all_cs false n iter;
  output_string oc1 "(check-sat)\n";
  output_string oc1 "(get-model)\n";
  close_out oc1

  (* let oc2 = open_out "experiment/out_fv_pre.smt2" in
  main_int_sub_declare oc2 all_cs true n iter;
  main_int_sub oc2 all_cs true n iter;
  output_string oc2 "(check-sat)\n";
  output_string oc2 "(get-model)\n";
  close_out oc2; *)

  (* let oc3 = open_out "experiment/out_int2.smt2" in
  main_int_sub_declare oc3 all_cs false n iter;
  main_int_sub oc3 all_cs false n iter;
  output_string oc3 "(check-sat)\n";
  close_out oc3; *)

  (* print_string "ownership_pre: " *)


let main_fv file =
  let oc_r1 = open_in file  in
  let oc_r2 = open_in "experiment/result_int" in
  let prog = Parser.program Lexer.read (Lexing.from_channel oc_r1) in
  let z3res = Z3Parser.result Z3Lexer.read (Lexing.from_channel oc_r2) in
  close_in oc_r1; close_in oc_r2;
  let (fdefs, _) = prog in
  let n = List.length fdefs in 
  (* print_program prog; print_newline (); print_newline (); *)
  infer_prog prog;
  (* print_all_tyenv !all_tyenv; print_newline (); print_newline (); *)
  let prog' = convert prog in
  (* print_program prog'; print_newline (); print_newline (); *)
  let all_cs = collect_prog prog' in 
  (* print_all_constraints all_cs; print_newline (); print_newline (); *)
  
  let oc = open_out "experiment/out_fv.smt2" in
  (* let oc2 = open_out "experiment/out_fv2.smt2" in *)
  main_int_sub_declare oc all_cs true n 0;
  main_int_sub oc all_cs true n 0;
  print_z3result oc z3res;
  output_string oc "\n\n";
  output_string oc "(check-sat)\n";
  output_string oc "(get-model)\n";
  close_out oc

  (* main_int_sub_declare oc2 all_cs true n 0;
  main_int_sub oc2 all_cs true n 0;
  print_z3result oc2 z3res;
  output_string oc2 "\n\n";
  output_string oc2 "(check-sat)\n";
  close_out oc2; *)

  (* print_string "ownership: " *)

let rec main_chc_sub_declare oc all_chcs n = 
  if n < 0 then 
    ()
  else
    (let oc_r2 = open_in "experiment/result" in
    let z3res = Z3Parser2.result Z3Lexer2.read (Lexing.from_channel oc_r2) in
    (* print_ownerships stdout z3res; *)
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
    (* print_ownerships stdout z3res; *)
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

let main_chc file =
  let oc_r1 = open_in file  in
  let prog = Parser.program Lexer.read (Lexing.from_channel oc_r1) in
  close_in oc_r1; 

  let (fdefs, _) = prog in
  let n = List.length fdefs in 
  (* print_program prog; print_newline (); print_newline (); *)
  infer_prog prog;
  (* print_all_tyenv !all_tyenv; print_newline (); print_newline (); *)
  let prog' = convert prog in
  (* print_program prog'; print_newline (); print_newline (); *)
  let all_chcs = chc_collect_prog prog' in 
  (* print_all_chcs all_chcs; print_newline (); print_newline (); *)
  (* List.iter (fun (id, ann) -> print_string id; print_string ": "; print_annotation ann; print_newline ()) !fn_env_chc; *)

  let oc = open_out "experiment/out_chc.smt2" in
  (* let oc2 = open_out "experiment/out_chc2.smt2" in *)
  output_string oc "(set-logic HORN)\n\n\n";
  main_chc_sub_declare oc all_chcs n;
  main_chc_sub oc all_chcs n;
  output_string oc "(check-sat)\n";
  output_string oc "(get-model)\n";
  close_out oc

  (* output_string oc2 "(set-logic HORN)\n\n\n";
  main_chc_sub_declare oc2 all_chcs n;
  main_chc_sub oc2 all_chcs n;
  output_string oc2 "(check-sat)\n";
  close_out oc2; *)

  (* print_string "refinement: " *)


let _ = 
  let input1 = Sys.argv.(1) in
  let input2 = Sys.argv.(2) in
  let input3 = Sys.argv.(3) in
  match input1 with
  | "int" -> main_int input2 (int_of_string input3)
  | "fv" -> main_fv input2
  | "chc" -> main_chc input2
  | _ -> ()