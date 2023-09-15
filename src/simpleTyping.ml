(** Molude for type inference of simple types *)
open Syntax
open TySyntax
open TyConstraintSolver

let all_tyenv = ref []

let rec infer_exp tyenv exp = 
  match exp with
  | ELet (id,e1,e2) ->
    let (t1,c1) = infer_exp tyenv e1 in
    tyenv := (id,t1) :: !tyenv;
    let (t2,c2) = infer_exp tyenv e2 in
    (t2, c1 @ c2)
  | EIf (e1,e2,e3) ->
    let (t1,c1) = infer_exp tyenv e1 in
    let (t2,c2) = infer_exp tyenv e2 in
    let (t3,c3) = infer_exp tyenv e3 in
    (t2, (t1, TyBool) :: (t2, t3) :: c1 @ c2 @ c3)
  | EMkarray (id,i,e) ->
    let nt = TyRef (TyVar (new_tyvar ())) in
    tyenv := (id,nt) :: !tyenv;
    let (t,c) = infer_exp tyenv e in
    (t, c)
  | EAssign (id,e1,e2) ->
    let t = lookup id !tyenv in
    let (t1,c1) = infer_exp tyenv e1 in
    let (t2,c2) = infer_exp tyenv e2 in
    (t2, (t, TyRef (t1)) :: c1 @ c2)
  | EAlias (e1,e2,e3) ->
    let (t1,c1) = infer_exp tyenv e1 in
    let (t2,c2) = infer_exp tyenv e2 in
    let (t3,c3) = infer_exp tyenv e3 in
    let nt = TyRef (TyVar (new_tyvar ())) in
    (t3, (t1, nt) :: (t1, t2) :: c1 @ c2 @ c3)
  | EAssert (e1,e2) ->
    let (t1,c1) = infer_exp tyenv e1 in
    let (t2,c2) = infer_exp tyenv e2 in
    (t2, (t1, TyBool) :: c1 @ c2)
  | ESeq (e1,e2) ->
    let (t1,c1) = infer_exp tyenv e1 in
    let (t2,c2) = infer_exp tyenv e2 in
    (t2, (t1, TyUnit) :: c1 @ c2)
  | EDeref id ->
    let t_id = lookup id !tyenv in
    let nt = TyVar (new_tyvar ()) in
    (nt, [(TyRef nt, t_id)])
  | EApp (id,es) ->
    let TyFun (t_args, t_ret) = lookup id !tyenv in
    let tcs = List.map (infer_exp tyenv) es in
    let ts = List.map fst tcs in
    let cs = List.concat (List.map snd tcs) in
    let cs_arg = List.map2 (fun x y -> (x,y)) t_args ts in
    (t_ret, cs_arg @ cs)
  | EEq (e1,e2) ->
    let (t1,c1) = infer_exp tyenv e1 in
    let (t2,c2) = infer_exp tyenv e2 in
    (TyBool, (t1, TyInt) :: (t2, TyInt) :: c1 @ c2)
  | ELt (e1,e2) ->
    let (t1,c1) = infer_exp tyenv e1 in
    let (t2,c2) = infer_exp tyenv e2 in
    (TyBool, (t1, TyInt) :: (t2, TyInt) :: c1 @ c2)
  | EGt (e1,e2) ->
    let (t1,c1) = infer_exp tyenv e1 in
    let (t2,c2) = infer_exp tyenv e2 in
    (TyBool, (t1, TyInt) :: (t2, TyInt) :: c1 @ c2)
  | ELeq (e1,e2) ->
    let (t1,c1) = infer_exp tyenv e1 in
    let (t2,c2) = infer_exp tyenv e2 in
    (TyBool, (t1, TyInt) :: (t2, TyInt) :: c1 @ c2)
  | EGeq (e1,e2) ->
    let (t1,c1) = infer_exp tyenv e1 in
    let (t2,c2) = infer_exp tyenv e2 in
    (TyBool, (t1, TyInt) :: (t2, TyInt) :: c1 @ c2)
  | ENeq (e1,e2) ->
    let (t1,c1) = infer_exp tyenv e1 in
    let (t2,c2) = infer_exp tyenv e2 in
    (TyBool, (t1, TyInt) :: (t2, TyInt) :: c1 @ c2)
  | EAnd (e1,e2) ->
    let (t1,c1) = infer_exp tyenv e1 in
    let (t2,c2) = infer_exp tyenv e2 in
    (TyBool, (t1, TyBool) :: (t2, TyBool) :: c1 @ c2)
  | EOr (e1,e2) ->
    let (t1,c1) = infer_exp tyenv e1 in
    let (t2,c2) = infer_exp tyenv e2 in
    (TyBool, (t1, TyBool) :: (t2, TyBool) :: c1 @ c2)
  | ENot e ->
    let (t,c) = infer_exp tyenv e in
    (TyBool, (t, TyBool) :: c)
  | EAdd (e1,e2) ->
    let (t1,c1) = infer_exp tyenv e1 in 
    let (t2,c2) = infer_exp tyenv e2 in
    let a = new_tyvar () in
    (TyVar a, (t1, TyVar a) :: (t2, TyInt) :: c1 @ c2)
  | ESub (e1,e2) ->
    let (t1,c1) = infer_exp tyenv e1 in 
    let (t2,c2) = infer_exp tyenv e2 in
    let a = new_tyvar () in
    (TyVar a, (t1, TyVar a) :: (t2, TyInt) :: c1 @ c2)
  | EMul (e1,e2) ->
    let (t1,c1) = infer_exp tyenv e1 in
    let (t2,c2) = infer_exp tyenv e2 in
    (TyInt, (t1, TyInt) :: (t2, TyInt) :: c1 @ c2)
  | EDiv (e1,e2) ->
    let (t1,c1) = infer_exp tyenv e1 in
    let (t2,c2) = infer_exp tyenv e2 in
    (TyInt, (t1, TyInt) :: (t2, TyInt) :: c1 @ c2)
  | EConstUnit ->
    (TyUnit, [])
  | EConstFail ->
    (TyUnit, [])
  | EConstInt i ->
    (TyInt, [])
  | EConstRandInt ->
    (TyInt, [])
  | EConstTrue ->
    (TyBool, [])
  | EConstFalse ->
    (TyBool, [])
  | EVar x ->
    (lookup x !tyenv, [])
  | _ -> raise TyError

let rec convert_ft ann =
  let (ftid_fts, _, ft) = ann in
  let fts = List.map snd ftid_fts in 
  let t_ids = List.map convert_sub fts in
  let t_ret = convert_sub ft in
  TyFun (t_ids, t_ret)
and convert_sub ft =
  match ft with
  | FTInt _ -> TyInt
  | FTRef (ft', _, _, _) -> TyRef(convert_sub ft')

let infer_fdef fun_tyenv fdef = 
  let (id, ids, ann, e) = fdef in
  let TyFun (t_ids, t_ret) = convert_ft ann in 
  let fun_tyenv' = (id, convert_ft ann) :: fun_tyenv in 
  let args_tyenv = (List.map2 (fun x y -> (x, y)) ids t_ids) @ fun_tyenv' in 
  let tyenv = ref args_tyenv in
  let (t, c) = infer_exp tyenv e in 
  let s = ty_unify ((t, t_ret) :: c) in
  let t' = ty_subst s t in
  assert(t' = t_ret);
  let tyenv' = List.map (fun (id,ty) -> (id, ty_subst s ty)) !tyenv in
  all_tyenv := (id, tyenv') :: !all_tyenv;
  fun_tyenv'

let infer_prog prog = 
  let (fdefs, e) = prog in
  let fun_tyenv = List.fold_left infer_fdef [] fdefs in
  let tyenv = ref fun_tyenv in
  let (t, c) = infer_exp tyenv e in
  let s = ty_unify c in
  let t' = ty_subst s t in
  assert(t' = TyUnit);
  let tyenv' = List.map (fun (id,ty) -> (id, ty_subst s ty)) !tyenv in
  all_tyenv := ("main", tyenv') :: !all_tyenv
