open Syntax
open CHCcollectConstraint
open TySyntax
open SimpleTyping
open Elim

let id_count_chc = ref []

let new_id id l =
  try
    let i = lookup id !id_count_chc in
    if i = l then ()
    else id_count_chc := (id, l) :: !id_count_chc
  with 
    Unbound -> id_count_chc := (id, l) :: !id_count_chc

let rec print_id_count_chc id_count_chc = 
  match id_count_chc with
  | [] -> print_newline ()
  | (id, l) :: id_count_chc' -> print_string ("(" ^ id ^ ", "); print_int l; print_string ") "; print_id_count_chc id_count_chc'

let rec lookup_pre id env = 
  match env with
  | [] -> raise Unbound
  | (x, _) :: nenv -> if id = x then lookup id nenv else lookup_pre id nenv

let ptrpred id i_sl n_sl =
  PtrPred(id, lookup id !id_count_chc, i_sl, n_sl)

let ptrpred_p id i_sl n_sl =
  PtrPred(id, lookup_pre id !id_count_chc, i_sl, n_sl)

let find_subst ftid_ft e = 
  match ftid_ft with
  | (RawId id, FTInt _) -> []
  | (HashId id, FTInt _) -> [(id, e)]
  | (RawId id, FTRef _) -> []
  | _ -> raise ConstrError


let rec emit_chc fvs c =
  match c with
  | CHCIf (e,cs1,cs2,l) -> 
    let ss1 = List.concat (List.map (emit_chc fvs) cs1) in
    let ss1' = List.map (fun s -> Imply(exp_to_smtlib e, s)) ss1 in
    let ss2 = List.concat (List.map (emit_chc fvs) cs2) in
    let ss2' = List.map (fun s -> Imply(Not(exp_to_smtlib e), s)) ss2 in
    ss1' @ ss2'
  | CHCLetInt (id,e,l) -> 
    new_id id l;
    (match e with
     | EDeref id' -> 
       intpred_env := (id, []) :: !intpred_env;
       [Imply(ptrpred id' (Id "0") (FV "n"), IntPred(id, ["v"]))]
     | EApp (id',es) -> 
       let (ftid_fts1, ftid_fts2, ft_r) = lookup id' !fn_env_chc in
       let subst = List.concat (List.map2 find_subst ftid_fts1 es) in
       let g1 ftid_ft e = 
         match ftid_ft with
         | (RawId _, FTRef ((FTInt sl),_,_,_)) -> 
           let FV id_e = exp_to_smtlib e in
           let n_sl = smtlib_subst subst sl in
           let fvs = lookup "m" !intpred_env in 
           [Imply(Ands([ptrpred id_e (FV "i") (FV "n"); IntPred("m", "m" :: fvs)]), n_sl)] (* "m" の扱い*)
         | (RawId _, FTInt sl) -> 
           let FV id_e = exp_to_smtlib e in
           let fvs = lookup id_e !intpred_env in 
           [Imply(IntPred(id_e, "v" :: fvs), sl)] (* "v" の扱い*)
         | (HashId _, FTInt sl) -> 
           let FV id_e = exp_to_smtlib e in
           let fvs = lookup id_e !intpred_env in 
           [Imply(IntPred(id_e, "v" :: fvs), sl)] (* "v" の扱い*)
         | _ -> raise ConstrError
       in
       let ss1 = List.concat (List.map2 g1 ftid_fts1 es) in
       let g2 ftid_ft e = 
         match ftid_ft with
         | (RawId _, FTRef ((FTInt sl),_,_,_)) -> 
           let FV id_e = exp_to_smtlib e in
           let n_sl = smtlib_subst subst sl in
           let fvs = lookup "m" !intpred_env in 
           new_id id_e l;
           [Imply(Ands([n_sl; IntPred("m", "m" :: fvs)]), ptrpred id_e (FV "i") (FV "n"))] (**)
         | (RawId _, FTInt sl) -> 
           let FV id_e = exp_to_smtlib e in
           []
         | (HashId _, FTInt sl) -> 
           let FV id_e = exp_to_smtlib e in
           []
         | _ -> raise ConstrError
       in
       let ss2 = List.concat (List.map2 g2 ftid_fts2 es) in
       let sl_ret = 
         match ft_r with
         | FTInt sl -> intpred_env := (id, []) :: !intpred_env; Imply(sl, IntPred(id, ["v"])) 
         | _ -> raise ConstrError
       in
       sl_ret :: ss1 @ ss2
     | e -> 
       let fvs = fvs_of_exp e in
       let rec find_hash fvs h r = 
         (match fvs with
          | fv :: rest -> 
            if fv = "n" then find_hash rest ["n"] r else find_hash rest h (fv::r) (* "n" の扱い　*)
          | [] -> (h, r)) 
       in
       let (hash_fvs, fvs) = find_hash fvs [] [] in
       intpred_env := (id, hash_fvs) :: !intpred_env;
       List.iter (fun fv -> intpred_env := (fv, []) :: !intpred_env) fvs;
       [Imply(Ands(Eq(Id("v"), exp_to_smtlib e) :: (List.map (fun fv -> IntPred(fv, [fv])) fvs)), IntPred(id, "v" :: hash_fvs))])
  | CHCLet (id1,id2,l) -> 
    new_id id1 l; new_id id2 l;
    [Imply(ptrpred_p id2 (FV "i") (FV "n"), ptrpred id2 (FV "i") (FV "n"));
     Imply(ptrpred_p id2 (FV "i") (FV "n"), ptrpred id1 (FV "i") (FV "n"))]
  (* | CLetDeref (id1,id2,l) -> 
    (print_string ("CLetDeref(" ^ id1 ^ ", ");
     print_string id2;
     print_string " | ";
     print_int l;
     print_string ")") *)
  | CHCLetAddPtr (id1,id2,i,l) -> 
    new_id id1 l; new_id id2 l;
    [Imply(ptrpred_p id2 (FV "i") (FV "n"), ptrpred id2 (FV "i") (FV "n"));
     Imply(ptrpred_p id2 (FV "i") (FV "n"), ptrpred id1 (Sub((FV "i"), (Id (string_of_int i)))) (FV "n"))] 
  | CHCMkArray (id,i,l) -> (* i いらない *)
    new_id id l;
    [Imply(Id "true", ptrpred id (FV "i") (FV "n"))]
  | CHCAssignInt (id,e,l) -> 
    new_id id l;
    (match e with
     | EDeref id' -> (* 到達しないはず *)
       [Imply(And(Imply(Eq((FV "i"), (Id "0")), ptrpred id' (Id "0") (FV "n")), 
                  Imply(Not(Eq((FV "i"), (Id "0"))), ptrpred_p id (FV "i") (FV "n"))),
              ptrpred id (FV "i") (FV "n"))]
     (* | EApp (id',es) ->  *)
     | EVar x ->
       [Imply(And(Imply(Eq((FV "i"), (Id "0")), IntPred(x, ["v"])), 
                  Imply(Not(Eq((FV "i"), (Id "0"))), ptrpred_p id (FV "i") (FV "n"))),
              ptrpred id (FV "i") (FV "n"))]
     | e -> (* EConstInt のみ？ *)
       [Imply(And(Imply(Eq((FV "i"), (Id "0")), Eq(Id("v"), exp_to_smtlib e)), 
                  Imply(Not(Eq((FV "i"), (Id "0"))), ptrpred_p id (FV "i") (FV "n"))),
              ptrpred id (FV "i") (FV "n"))])
  (* | CAssignRef (id1,id2,l) -> 
    (print_string ("CAssignRef(" ^ id1 ^ ", ");
     print_string id2;
     print_string " | ";
     print_int l;
     print_string ")") *)
  | CHCAlias (id1,id2,l) -> 
    new_id id1 l; new_id id2 l;
    [Imply(And(ptrpred_p id2 (FV "i") (FV "n"), ptrpred_p id1 (FV "i") (FV "n")), ptrpred id2 (FV "i") (FV "n"));
     Imply(And(ptrpred_p id2 (FV "i") (FV "n"), ptrpred_p id1 (FV "i") (FV "n")), ptrpred id1 (FV "i") (FV "n"))]
  (* | CAliasDeref (id1,id2,l) -> 
    (print_string ("CAliasDeref(" ^ id1 ^ ", ");
     print_string id2;
     print_string " | ";
     print_int l;
     print_string ")") *)
  | CHCAliasAddPtr (id1,id2,i,l) -> 
    new_id id1 l; new_id id2 l;
    [Imply(And(ptrpred_p id2 (FV "i") (FV "n"), ptrpred_p id1 (Sub((FV "i"), (Id (string_of_int i)))) (FV "n")), ptrpred id2 (FV "i") (FV "n"));
     Imply(And(ptrpred_p id2 (FV "i") (FV "n"), ptrpred_p id1 (Sub((FV "i"), (Id (string_of_int i)))) (FV "n")), ptrpred id1 (Sub((FV "i"), (Id (string_of_int i)))) (FV "n"))]
  | CHCAssert (e,l) -> 
    let fvs = fvs_of_exp e in
    if fvs = [] then
      [exp_to_smtlib e]
    else
      (List.iter (fun fv -> intpred_env := (fv, []) :: !intpred_env) fvs;
      [Imply(Ands(List.map (fun fv -> IntPred(fv, [fv])) fvs), exp_to_smtlib e)])
  | CHCApp (id_fn,es,l) -> 
    let (ftid_fts1, ftid_fts2, ft_r) = lookup id_fn !fn_env_chc in
    let subst = List.concat (List.map2 find_subst ftid_fts1 es) in
    let g1 ftid_ft e = 
      match ftid_ft with
      | (RawId _, FTRef ((FTInt sl),_,_,_)) -> 
        let FV id_e = exp_to_smtlib e in
        let n_sl = smtlib_subst subst sl in
        let fvs = lookup "m" !intpred_env in 
        [Imply(Ands([ptrpred id_e (FV "i") (FV "n"); IntPred("m", "m" :: fvs)]), n_sl)] (* "m" の扱い*)
      | (RawId _, FTInt sl) -> 
        let FV id_e = exp_to_smtlib e in
        let fvs = lookup id_e !intpred_env in 
        [Imply(IntPred(id_e, "v" :: fvs), sl)] (* "v" の扱い*)
      | (HashId _, FTInt sl) -> 
        let FV id_e = exp_to_smtlib e in
        let fvs = lookup id_e !intpred_env in 
        [Imply(IntPred(id_e, "v" :: fvs), sl)] (* "v" の扱い*)
      | _ -> raise ConstrError
    in
    let ss1 = List.concat (List.map2 g1 ftid_fts1 es) in
    let g2 ftid_ft e = 
      match ftid_ft with
      | (RawId _, FTRef ((FTInt sl),_,_,_)) -> 
        let FV id_e = exp_to_smtlib e in
        let n_sl = smtlib_subst subst sl in
        let fvs = lookup "m" !intpred_env in 
        new_id id_e l;
        [Imply(Ands([n_sl; IntPred("m", "m" :: fvs)]), ptrpred id_e (FV "i") (FV "n"))] (**)
      | (RawId _, FTInt sl) -> 
        let FV id_e = exp_to_smtlib e in
        []
      | (HashId _, FTInt sl) -> 
        let FV id_e = exp_to_smtlib e in
        []
      | _ -> raise ConstrError
    in
    let ss2 = List.concat (List.map2 g2 ftid_fts2 es) in
    ss1 @ ss2
    (* ss1 *)

let find_fv ftid_ft = 
  match ftid_ft with
  | (HashId id, _) -> [id]
  | _ -> []

let find_id ftid_ft = 
  match ftid_ft with
  | (RawId id, FTRef _) -> [id]
  | (RawId id, FTInt _) -> [id]
  | (HashId id, FTInt _) -> [id]
  | _ -> [] 

let rec assoc_ft id ftid_fts = 
  match ftid_fts with
  | (RawId id_ft, FTRef ((FTInt sl),_,_,_)) :: ftid_fts' when id_ft = id -> (sl, "ref")
  | (RawId id_ft, FTInt sl) :: ftid_fts' when id_ft = id -> (sl, "int")
  | (HashId id_ft, FTInt sl) :: ftid_fts' when id_ft = id -> (sl, "int")
  | _ :: ftid_fts' -> assoc_ft id ftid_fts'
  | [] -> raise Not_found

let ics_to_smtlib ics =
  let (id, cs, e_rets) = ics in
  let (ftid_fts1, ftid_fts2, ft_r) = lookup id !fn_env_chc in
  let fvs = List.concat (List.map find_fv ftid_fts1) in
  (* List.iter print_string fvs; *)
  let ids =  List.concat (List.map find_id ftid_fts1) in
  (* List.iter print_string ids; *)
  id_count_chc := List.map (fun id -> (id, 0)) ids;
  intpred_env := [];
  let g1 id = 
    let (sl,ft) = assoc_ft id ftid_fts1 in 
    match ft with
    | "ref" -> 
      [Imply(sl, ptrpred id (FV "i") (FV "n"))] (**)
    | "int" -> 
      intpred_env := (id, []) :: !intpred_env;
      [Imply(sl, IntPred(id, ["v"]))]
    | _ -> raise ConstrError
  in
  let s1 = List.concat (List.map g1 ids) in
  let ss = List.concat (List.map (emit_chc fvs) cs) in
  let g2 id = 
    let (sl,ft) = assoc_ft id ftid_fts2 in 
    match ft with
    | "ref" -> 
      [Imply(ptrpred id (FV "i") (FV "n"), sl)] (**)
    | "int" -> 
      []
    | _ -> raise ConstrError
  in
  let s2 = List.concat (List.map g2 ids) in
  let g3 ft_r e_ret = 
    try 
      let e_sl = exp_to_smtlib e_ret in
      (match ft_r, e_sl with
      | FTInt sl, FV id_e -> 
        intpred_env := (id_e, []) :: !intpred_env;
        [Imply(IntPred(id_e, ["v"]), sl)]
      | FTInt sl, Id i -> 
        [Imply(Eq(FV "v", Id i), sl)] 
      | _ -> raise ConstrError)
    with ElimError -> []
  in
  let s3 = List.concat (List.map (g3 ft_r) e_rets) in
  (s1 @ ss @ s2 @ s3, !id_count_chc, fvs)
  (* (ss, !id_count_chc, fvs) *)
  

let all_cs_to_smtlib_chc all_cs n =
  (* List.concat (List.map ics_to_smtlib all_cs) *)
  let (ss, id_count_chc, fvs) = ics_to_smtlib (List.nth all_cs n) in
  (* print_declare id_count_chc fvs; *)
  (id_count_chc, fvs, ss)
  
    