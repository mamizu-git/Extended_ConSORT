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

let rec main_int_sub oc all_cs bool_id n = 
  if n < 0 then 
    ()
  else
    (let (id_count, fvs, sls) = all_cs_to_smtlib all_cs n in
    print_declare oc id_count fvs n;
    output_string oc "\n";
    print_smtlibs oc sls bool_id fvs (-1); 
    output_string oc "\n\n";
    main_int_sub oc all_cs bool_id (n-1))

let main_int n = 
  let oc_r1 = open_in "../experiment/test.imp" in
  let prog = Parser.program Lexer.read (Lexing.from_channel oc_r1) in
  close_in oc_r1;
  (* print_program prog; print_newline (); print_newline (); *)
  infer_prog prog;
  (* print_all_tyenv !all_tyenv; print_newline (); print_newline (); *)
  let prog' = convert prog in
  (* print_program prog'; print_newline (); print_newline (); *)
  let all_cs = collect_prog prog' in 
  (* print_all_constraints all_cs; print_newline (); print_newline (); *)

  let oc1 = open_out "../experiment/out_int.smt2" in
  main_int_sub oc1 all_cs false n;
  output_string oc1 "(check-sat)\n";
  output_string oc1 "(get-model)\n";
  close_out oc1;

  let oc2 = open_out "../experiment/out_fv_pre.smt2" in
  main_int_sub oc2 all_cs true n;
  output_string oc2 "(check-sat)\n";
  output_string oc2 "(get-model)\n";
  close_out oc2

let main_fv n =
  let oc_r1 = open_in "../experiment/test.imp" in
  let oc_r2 = open_in "../experiment/result_int" in
  let prog = Parser.program Lexer.read (Lexing.from_channel oc_r1) in
  let z3res = Z3Parser.result Z3Lexer.read (Lexing.from_channel oc_r2) in
  close_in oc_r1; close_in oc_r2;
  (* print_program prog; print_newline (); print_newline (); *)
  infer_prog prog;
  (* print_all_tyenv !all_tyenv; print_newline (); print_newline (); *)
  let prog' = convert prog in
  (* print_program prog'; print_newline (); print_newline (); *)
  let all_cs = collect_prog prog' in 
  (* print_all_constraints all_cs; print_newline (); print_newline (); *)
  let (id_count, fvs, sls) = all_cs_to_smtlib all_cs n in
  
  let oc = open_out "../experiment/out_fv.smt2" in
  main_int_sub oc all_cs true n;
  print_z3result oc z3res;
  output_string oc "\n\n";
  output_string oc "(check-sat)\n";
  output_string oc "(get-model)\n";
  close_out oc

let rec main_chc_sub oc all_chcs n = 
  if n < 0 then 
    ()
  else
    (let oc_r2 = open_in @@ "../experiment/result" in
    let z3res = Z3Parser2.result Z3Lexer2.read (Lexing.from_channel oc_r2) in
    (* print_ownerships stdout z3res; *)
    close_in oc_r2;
    
    let (id_count, varpred_count, fvs, sls) = all_cs_to_smtlib_chc all_chcs n in
    let args_own_sls = ownexp_to_ownchc varpred_count n in
    let own_sls = collect_ownchc z3res n in 

    print_declare_chc oc id_count varpred_count n;
    output_string oc "\n";
    print_smtlibs oc sls true fvs n; 
    output_string oc "\n";
    print_smtlibs oc args_own_sls true fvs n; 
    output_string oc "\n";
    print_smtlibs oc own_sls true fvs n; 
    output_string oc "\n\n";
    main_chc_sub oc all_chcs (n-1))

let main_chc n =
  let oc_r1 = open_in "../experiment/test.imp" in
  let prog = Parser.program Lexer.read (Lexing.from_channel oc_r1) in
  close_in oc_r1; 

  (* print_program prog; print_newline (); print_newline (); *)
  infer_prog prog;
  (* print_all_tyenv !all_tyenv; print_newline (); print_newline (); *)
  let prog' = convert prog in
  (* print_program prog'; print_newline (); print_newline (); *)
  let all_chcs = chc_collect_prog prog' in 
  (* print_all_chcs all_chcs; print_newline (); print_newline (); *)
  (* List.iter (fun (id, ann) -> print_string id; print_string ": "; print_annotation ann; print_newline ()) !fn_env_chc; *)

  let oc = open_out "../experiment/out_chc.smt2" in
  output_string oc "(set-logic HORN)\n\n\n";
  main_chc_sub oc all_chcs n;
  output_string oc "(check-sat)\n";
  output_string oc "(get-model)\n";
  close_out oc


let _ = 
  let input1 = Sys.argv.(1) in
  let input2 = Sys.argv.(2) in
  match input1 with
  | "int" -> main_int (int_of_string input2)
  | "fv" -> main_fv (int_of_string input2)
  | "chc" -> main_chc (int_of_string input2)
  | _ -> ()