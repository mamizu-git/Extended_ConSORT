open Syntax
open CHCcollectConstraint
open TySyntax
open SimpleTyping
open Util

let id_count_chc = ref []

let rec lookup_ifel id ifel env =
  match env with
  | [] -> raise Unbound
  | (x, (l, lst)) :: nenv -> if id = x && ifel = lst then l else lookup_ifel id ifel nenv

let new_id id l ifel =
  try
    let i = lookup_ifel id ifel !id_count_chc in
    if i = l then ()
    else id_count_chc := (id, (l, ifel)) :: !id_count_chc
  with 
    Unbound -> id_count_chc := (id, (l, ifel)) :: !id_count_chc

let rec print_id_count_chc id_count_chc = 
  match id_count_chc with
  | [] -> print_newline ()
  | (id, (l, ifel)) :: id_count_chc' -> print_string ("(" ^ id ^ ", "); print_int l; print_string (ifel_to_str ifel); print_string ") "; print_id_count_chc id_count_chc'

let rec lookup_pre_ifel id ifel env = 
  match env with
  | [] -> raise Unbound
  | (x, _) :: nenv -> if id = x then lookup_ifel id ifel nenv else lookup_pre_ifel id ifel nenv

let ptrpred id i_sl n_sl ifel =
  PtrPred(id, (string_of_int (lookup_ifel id ifel !id_count_chc)) ^ (ifel_to_str ifel), i_sl, n_sl)

let ptrpred_p id i_sl n_sl ifel =
  PtrPred(id, (string_of_int (lookup_pre_ifel id ifel !id_count_chc)) ^ (ifel_to_str ifel), i_sl, n_sl)

let find_subst ftid_ft e = 
  match ftid_ft with
  | (RawId id, FTInt _) -> []
  | (HashId id, FTInt _) -> [(id, e)]
  | (RawId id, FTRef _) -> []
  | _ -> raise ConstrError

let varpred_count = ref []

let my_string_of_int i = 
  if i >= 0 then string_of_int i 
  else "(" ^ string_of_int i ^ ")"

let rec find_id_count ifel id_count res = 
  match id_count with
  | [] -> res
  | (x, (_,lst)) :: id_count' -> 
    if List.mem x res || ifel <> lst then 
      find_id_count ifel id_count' res 
    else 
      find_id_count ifel id_count' (x :: res)
 
let rec union_list ls1 ls2 = 
  match ls1 with
  | [] -> ls2
  | x :: ls1' -> if List.mem x ls2 then union_list ls1' ls2 else union_list ls1' (x :: ls2)

let rec emit_chc fvs fun_num ifel c =
  match c with
  | CHCIf (e,cs1,cs2,l) -> 
    let ids_pre = find_id_count ifel !id_count_chc [] in 
    List.iter (fun id -> new_id id l ("if" :: ifel); new_id id l ("el" :: ifel)) ids_pre;
    let ss_pre = 
      List.concat (List.map 
        (fun id -> 
          [Imply(ptrpred id (FV "i") (FV "n") ifel, ptrpred id (FV "i") (FV "n") ("if" :: ifel));
           Imply(ptrpred id (FV "i") (FV "n") ifel, ptrpred id (FV "i") (FV "n") ("el" :: ifel))]
        ) ids_pre) in
    let ss1 = List.concat (List.map (emit_chc fvs fun_num ("if" :: ifel)) cs1) in
    let ss1' = List.map (fun s -> Imply(exp_to_smtlib e, s)) ss1 in
    let ss2 = List.concat (List.map (emit_chc fvs fun_num ("el" :: ifel)) cs2) in
    let ss2' = List.map (fun s -> Imply(Not(exp_to_smtlib e), s)) ss2 in
    let ids_post_if = find_id_count ("if" :: ifel) !id_count_chc [] in
    let ids_post_el = find_id_count ("el" :: ifel) !id_count_chc [] in
    let ids_post = union_list ids_post_if ids_post_el in
    List.iter (fun id -> new_id id (l+1) ifel) ids_post; 
    let ss_post_if = 
      List.map 
        (fun s -> Imply(exp_to_smtlib e, s))
        (List.map 
          (fun id -> 
            Imply(ptrpred id (FV "i") (FV "n") ("if" :: ifel), ptrpred id (FV "i") (FV "n") ifel)
          ) ids_post_if) in
    let ss_post_el = 
      List.map 
        (fun s -> Imply(Not(exp_to_smtlib e), s))
        (List.map 
          (fun id -> 
            Imply(ptrpred id (FV "i") (FV "n") ("el" :: ifel), ptrpred id (FV "i") (FV "n") ifel)
          ) ids_post_el) in
    ss_pre @ ss1' @ ss2' @ ss_post_if @ ss_post_el
  | CHCLetInt (id,e,l) -> 
    (match e with
     | EDeref id' -> 
       intpred_env := (id, []) :: !intpred_env;
       [Imply(ptrpred id' (Id "0") (FV "n") ifel, IntPred(id, ["v"]))]
     | EApp (id',es) -> 
       let (ftid_fts1, ftid_fts2, ft_r) = lookup id' !fn_env_chc in
       let subst = List.concat (List.map2 find_subst ftid_fts1 es) in
       let g1 ftid_ft e = 
         match ftid_ft with
         | (RawId id_arg, FTRef ((FTInt VarPred),el,eh,f)) -> 
          let FV id_e = exp_to_smtlib e in
          let fvs = lookup "m" !intpred_env in 
          let num = lookup id' fun_num in
          varpred_count := (PtrVarPred(num, id_arg, "b", (FV "i"), (FV "n")), (el,eh,f)) :: !varpred_count;
          [Imply(Ands([ptrpred id_e (FV "i") (FV "n") ifel; IntPred("m", "m" :: fvs)]), PtrVarPred(num, id_arg, "b", (FV "i"), (FV "m")))]
        | (RawId id_arg, FTInt VarPred) -> 
          let FV id_e = exp_to_smtlib e in
          let fvs = lookup id_e !intpred_env in 
          intpred_env := (id_arg, []) :: !intpred_env; 
          let num = lookup id' fun_num in
          [Imply(IntPred(id_e, "v" :: fvs), IntVarPred(num, id_arg, ["v"]))] 
        | (HashId id_arg, FTInt VarPred) -> 
          let FV id_e = exp_to_smtlib e in
          let fvs = lookup id_e !intpred_env in 
          intpred_env := (id_arg, []) :: !intpred_env; 
          let num = lookup id' fun_num in
          [Imply(IntPred(id_e, "v" :: fvs), IntVarPred(num, id_arg, ["v"]))] 
         | (RawId _, FTRef ((FTInt sl),_,_,_)) -> 
           let FV id_e = exp_to_smtlib e in
           let n_sl = smtlib_subst subst sl in
           let fvs = lookup "m" !intpred_env in 
           [Imply(Ands([ptrpred id_e (FV "i") (FV "n") ifel; IntPred("m", "m" :: fvs)]), n_sl)]
         | (RawId _, FTInt sl) -> 
           let FV id_e = exp_to_smtlib e in
           let fvs = lookup id_e !intpred_env in 
           [Imply(IntPred(id_e, "v" :: fvs), sl)]
         | (HashId _, FTInt sl) -> 
           let FV id_e = exp_to_smtlib e in
           let fvs = lookup id_e !intpred_env in 
           [Imply(IntPred(id_e, "v" :: fvs), sl)]
         | _ -> raise ConstrError
       in
       let ss1 = List.concat (List.map2 g1 ftid_fts1 es) in
       let g2 ftid_ft e = 
         match ftid_ft with
         | (RawId id_arg, FTRef ((FTInt VarPred),el,eh,f)) -> 
           let FV id_e = exp_to_smtlib e in
           let fvs = lookup "m" !intpred_env in 
           new_id id_e l ifel;
           let num = lookup id' fun_num in
           varpred_count := (PtrVarPred(num, id_arg, "e", (FV "i"), (FV "n")), (el,eh,f)) :: !varpred_count;
           [Imply(Ands([PtrVarPred(num, id_arg, "e", (FV "i"), (FV "m")); IntPred("m", "m" :: fvs)]), ptrpred id_e (FV "i") (FV "n") ifel)] 
         | (RawId _, FTRef ((FTInt sl),_,_,_)) -> 
           let FV id_e = exp_to_smtlib e in
           let n_sl = smtlib_subst subst sl in
           let fvs = lookup "m" !intpred_env in 
           new_id id_e l ifel;
           [Imply(Ands([n_sl; IntPred("m", "m" :: fvs)]), ptrpred id_e (FV "i") (FV "n") ifel)] 
         | (RawId _, FTInt _) -> 
           []
         | (HashId _, FTInt _) -> 
           []
         | _ -> raise ConstrError
       in
       let ss2 = List.concat (List.map2 g2 ftid_fts2 es) in
       let find_fv' ftid_ft e = 
         match ftid_ft, e with
         | (HashId id, _), EVar x -> [x]
         | _ -> []
       in
       let fvs' = List.concat (List.map2 find_fv' ftid_fts1 es) in
       let sl_ret = 
         match ft_r with
         | FTInt VarPred -> 
           intpred_env := (id, []) :: !intpred_env;
           let num = lookup id' fun_num in
           Imply(Ands(IntVarPred(num, "ret", id :: fvs') :: (List.map (fun fv -> IntPred(fv, fv :: (lookup fv !intpred_env))) fvs')), IntPred(id, [id])) 
         | FTInt sl -> 
           intpred_env := (id, []) :: !intpred_env; 
           Imply(sl, IntPred(id, [id])) 
         | _ -> raise ConstrError
       in
       sl_ret :: ss1 @ ss2
     | EConstRandInt ->
       intpred_env := (id, []) :: !intpred_env;
       [Imply((Id "true"), IntPred(id, [id]))]
     | e -> 
       let fvs = fvs_of_exp e in
       let rec find_hash fvs h r = 
         (match fvs with
          | fv :: rest -> 
            if fv = "n" then find_hash rest ["n"] r else find_hash rest h (fv::r) 
          | [] -> (h, r)) 
       in
       let (hash_fvs, fvs) = find_hash fvs [] [] in
       intpred_env := (id, hash_fvs) :: !intpred_env;
       List.iter (fun fv -> intpred_env := (fv, []) :: !intpred_env) fvs;
       [Imply(Ands(Eq(Id("v"), exp_to_smtlib e) :: (List.map (fun fv -> IntPred(fv, fv :: (lookup fv !intpred_env))) fvs)), IntPred(id, "v" :: hash_fvs))])
  | CHCLet (id1,id2,l) -> 
    new_id id1 l ifel; new_id id2 l ifel;
    [Imply(ptrpred_p id2 (FV "i") (FV "n") ifel, ptrpred id2 (FV "i") (FV "n") ifel);
     Imply(ptrpred_p id2 (FV "i") (FV "n") ifel, ptrpred id1 (FV "i") (FV "n") ifel)]
  | CHCLetAddPtr (id1,id2,e,l) -> 
    new_id id1 l ifel; new_id id2 l ifel;
    (match e with
     | EConstInt i ->
       [Imply(ptrpred_p id2 (FV "i") (FV "n") ifel, ptrpred id2 (FV "i") (FV "n") ifel);
        Imply(ptrpred_p id2 (FV "i") (FV "n") ifel, ptrpred id1 (Sub((FV "i"), (Id (my_string_of_int i)))) (FV "n") ifel)]
     | EVar x -> 
       [Imply(ptrpred_p id2 (FV "i") (FV "n") ifel, ptrpred id2 (FV "i") (FV "n") ifel);
        Imply(IntPred(x, [x;"n"]), Imply(ptrpred_p id2 (FV "i") (FV "n") ifel, ptrpred id1 (Sub((FV "i"), (FV x))) (FV "n") ifel))] 
    )
  | CHCLetSubPtr (id1,id2,e,l) -> 
    new_id id1 l ifel; new_id id2 l ifel;
    (match e with
     | EConstInt i ->
       [Imply(ptrpred_p id2 (FV "i") (FV "n") ifel, ptrpred id2 (FV "i") (FV "n") ifel);
        Imply(ptrpred_p id2 (FV "i") (FV "n") ifel, ptrpred id1 (Add((FV "i"), (Id (my_string_of_int i)))) (FV "n") ifel)]
     | EVar x -> 
       [Imply(ptrpred_p id2 (FV "i") (FV "n") ifel, ptrpred id2 (FV "i") (FV "n") ifel);
        Imply(IntPred(x, [x;"n"]), Imply(ptrpred_p id2 (FV "i") (FV "n") ifel, ptrpred id1 (Add((FV "i"), (FV x))) (FV "n") ifel))] 
    )
  | CHCMkArray (id,i,l) -> 
    new_id id l ifel;
    [Imply(Id "true", ptrpred id (FV "i") (FV "n") ifel)]
  | CHCAssignInt (id,e,l) -> 
    new_id id l ifel;
    (match e with
     | EVar x ->
       let vars = lookup x !intpred_env in
       [Imply(And(Imply(Eq((FV "i"), (Id "0")), IntPred(x, "v" :: vars)), 
                  Imply(Not(Eq((FV "i"), (Id "0"))), ptrpred_p id (FV "i") (FV "n") ifel)),
              ptrpred id (FV "i") (FV "n") ifel)]
     | e ->
       [Imply(And(Imply(Eq((FV "i"), (Id "0")), Eq(Id("v"), exp_to_smtlib e)), 
                  Imply(Not(Eq((FV "i"), (Id "0"))), ptrpred_p id (FV "i") (FV "n") ifel)),
              ptrpred id (FV "i") (FV "n") ifel)])
  | CHCAlias (id1,id2,l) -> 
    new_id id1 l ifel; new_id id2 l ifel;
    [Imply(And(ptrpred_p id2 (FV "i") (FV "n") ifel, ptrpred_p id1 (FV "i") (FV "n") ifel), ptrpred id2 (FV "i") (FV "n") ifel);
     Imply(And(ptrpred_p id2 (FV "i") (FV "n") ifel, ptrpred_p id1 (FV "i") (FV "n") ifel), ptrpred id1 (FV "i") (FV "n") ifel)]
  | CHCAliasAddPtr (id1,id2,e,l) -> 
    new_id id1 l ifel; new_id id2 l ifel;
    (match e with
     | EConstInt i ->
       [Imply(And(ptrpred_p id2 (FV "i") (FV "n") ifel, ptrpred_p id1 (Sub((FV "i"), (Id (my_string_of_int i)))) (FV "n") ifel), ptrpred id2 (FV "i") (FV "n") ifel);
        Imply(And(ptrpred_p id2 (FV "i") (FV "n") ifel, ptrpred_p id1 (Sub((FV "i"), (Id (my_string_of_int i)))) (FV "n") ifel), ptrpred id1 (Sub((FV "i"), (Id (my_string_of_int i)))) (FV "n") ifel)]   
     | EVar x ->
       [Imply(IntPred(x, [x;"n"]), Imply(And(ptrpred_p id2 (FV "i") (FV "n") ifel, ptrpred_p id1 (Sub((FV "i"), (FV x))) (FV "n") ifel), ptrpred id2 (FV "i") (FV "n") ifel));
        Imply(IntPred(x, [x;"n"]), Imply(And(And(ptrpred_p id2 (FV "i") (FV "n") ifel, ptrpred_p id1 (Sub((FV "i"), (FV x))) (FV "n") ifel), IntPred(x, [x;"n"])), ptrpred id1 (Sub((FV "i"), (FV x))) (FV "n") ifel))] 
    )

  | CHCAssert (e,l) -> 
    let fvs = fvs_of_exp e in
    if fvs = [] then
      [exp_to_smtlib e]
    else
      [Imply(Ands(List.map (fun fv -> let vars = lookup fv !intpred_env in IntPred(fv, fv :: vars)) fvs), exp_to_smtlib e)]

let find_fv ftid_ft = 
  match ftid_ft with
  | (HashId id, _) -> [id]
  | _ -> []

let find_ref_id ftid_ft = 
  match ftid_ft with
  | (RawId id, FTRef _) -> [id]
  | _ -> [] 

let find_id ftid_ft = 
  match ftid_ft with
  | (RawId id, FTRef _) -> [id]
  | (RawId id, FTInt _) -> [id]
  | (HashId id, FTRef _) -> [id]
  | _ -> [] 

let rec assoc_ft id ftid_fts = 
  match ftid_fts with
  | (RawId id_ft, FTRef ((FTInt sl),el,eh,f)) :: ftid_fts' when id_ft = id -> (sl, FTRef ((FTInt sl),el,eh,f))
  | (RawId id_ft, FTInt sl) :: ftid_fts' when id_ft = id -> (sl, FTInt sl)
  | (HashId id_ft, FTInt sl) :: ftid_fts' when id_ft = id -> (sl, FTInt sl)
  | _ :: ftid_fts' -> assoc_ft id ftid_fts'
  | [] -> raise Not_found

let ics_to_smtlib ics fun_num =
  let (id', cs, e_rets) = ics in
  let (ftid_fts1, ftid_fts2, ft_r) = lookup id' !fn_env_chc in
  let fvs = List.concat (List.map find_fv ftid_fts1) in
  let ref_ids =  List.concat (List.map find_ref_id ftid_fts1) in
  let ids =  List.concat (List.map find_id ftid_fts1) in
  id_count_chc := List.map (fun id -> (id, (1,[]))) ref_ids;
  intpred_env := [];
  varpred_count := [];
  let g1 id = 
    let (sl,ft) = assoc_ft id ftid_fts1 in 
    match sl, ft with
    | VarPred, FTRef (_,el,eh,f) -> 
      let num = lookup id' fun_num in
      varpred_count := (PtrVarPred(num, id, "b", (FV "i"), (FV "n")), (el,eh,f)) :: !varpred_count;
      [Imply(PtrVarPred(num, id, "b", (FV "i"), (FV "n")), ptrpred id (FV "i") (FV "n") [])] 
    | VarPred, FTInt _ -> 
      intpred_env := (id, []) :: !intpred_env;
      []
    | _, FTRef _ -> 
      [Imply(sl, ptrpred id (FV "i") (FV "n") [])] 
    | _, FTInt _ -> 
      intpred_env := (id, []) :: !intpred_env;
      [Imply(sl, IntPred(id, ["v"]))]
    | _ -> raise ConstrError
  in
  let s1 = List.concat (List.map g1 ids) in
  let ss = List.concat (List.map (emit_chc fvs fun_num []) cs) in
  let g2 id = 
    let (sl,ft) = assoc_ft id ftid_fts2 in 
    match sl, ft with
    | VarPred, FTRef (_,el,eh,f) -> 
      let num = lookup id' fun_num in
      varpred_count := (PtrVarPred(num, id, "e", (FV "i"), (FV "n")), (el,eh,f)) :: !varpred_count;
      [Imply(ptrpred id (FV "i") (FV "n") [], PtrVarPred(num, id, "e", (FV "i"), (FV "n")))] 
    | VarPred, FTInt _ -> 
      []
    | _, FTRef _ -> 
      [Imply(ptrpred id (FV "i") (FV "n") [], sl)] 
    | _, FTInt _ -> 
      [Imply(IntPred(id, ["v"]), sl)]
    | _ -> raise ConstrError
  in
  let s2 = List.concat (List.map g2 ids) in
  let g3 ft_r (cond, e_ret) = 
    try 
      let cond_sl = Ands(cond) in
      let e_sl = exp_to_smtlib e_ret in
      (match ft_r, e_sl with
      | FTInt VarPred, FV id_e -> 
        intpred_env := (id_e, []) :: !intpred_env;
        let num = lookup id' fun_num in
        varpred_count := (IntVarPred(num, "ret", fvs), (EConstUnit, EConstUnit, 0.)) :: !varpred_count;
        [Imply(cond_sl, Imply(IntPred(id_e, [id_e]), IntVarPred(num, "ret", id_e :: fvs)))]
      | FTInt VarPred, Id i -> 
        let num = lookup id' fun_num in
        varpred_count := (IntVarPred(num, "ret", fvs), (EConstUnit, EConstUnit, 0.)) :: !varpred_count;
        [Imply(cond_sl, Imply(Eq(FV "v", Id i), IntVarPred(num, "ret", "v" :: fvs)))] 
      | FTInt sl, FV id_e -> 
        intpred_env := (id_e, []) :: !intpred_env;
        [Imply(cond_sl, Imply(IntPred(id_e, [id_e]), sl))]
      | FTInt sl, Id i -> 
        [Imply(cond_sl, Imply(Eq(FV "v", Id i), sl))] 
      | _ -> raise ConstrError)
    with ElimError -> []
  in
  let s3 = List.concat (List.map (g3 ft_r) e_rets) in
  (s1 @ ss @ s2 @ s3, !id_count_chc, !varpred_count, fvs)
  
let rec fun_number all_cs cnt res =
  match all_cs with
  | [] -> res
  | ics :: all_cs' -> 
    let (id,_,_) = ics in
    fun_number all_cs' (cnt+1) ((id, cnt) :: res)

let all_cs_to_smtlib_chc all_cs n =
  let fun_num = fun_number all_cs 0 [] in
  let (ss, id_count_chc, varpred_count, fvs) = ics_to_smtlib (List.nth all_cs n) fun_num in
  (id_count_chc, varpred_count, fvs, ss)
  
    