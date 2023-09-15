open Syntax
open TySyntax
open SimpleTyping

exception ElimError

let rec elim_v env f_id args exp = 
  match exp with
  | ELetInt (id,e1,e2) -> 
    ELetInt(id, elim_v env f_id args e1, elim_v env f_id args e2)
  | ELetVarPtr (id1,id2,e) ->
    ELetVarPtr(id1, id2, elim_v env f_id args e)
  | ELetDerefPtr (id1,id2,e) ->
    ELetDerefPtr(id1, id2, elim_v env f_id args e)
  | ELetAddPtr (id1,id2,e1,e2) ->
    ELetAddPtr(id1, id2, elim_v env f_id args e1, elim_v env f_id args e2)
  | ELetSubPtr (id1,id2,e1,e2) ->
    ELetSubPtr(id1, id2, elim_v env f_id args e1, elim_v env f_id args e2)
  | EIf (e1,e2,e3) ->
    EIf(elim_v env f_id args e1, elim_v env f_id args e2, elim_v env f_id args e3)
  | EMkarray (id,i,e) ->
    EMkarray(id, i, elim_v env f_id args e)
  | EAssign (id1,e1,e2) ->
    EAssign(id1, elim_v env f_id args e1, elim_v env f_id args e2)
  | EAssignInt (id,e1,e2) ->
    EAssignInt(id, elim_v env f_id args e1, elim_v env f_id args e2)
  | EAssignPtr (id1,id2,e) ->
    EAssignPtr(id1, id2, elim_v env f_id args e)
  | EAlias (e1,e2,e3) ->
    EAlias(elim_v env f_id args e1, elim_v env f_id args e2, elim_v env f_id args e3) 
  | EAliasVarPtr (id1,id2,e) ->
    EAliasVarPtr(id1, id2, elim_v env f_id args e)
  | EAliasDerefPtr (id1,id2,e) ->
    EAliasDerefPtr(id1, id2, elim_v env f_id args e)
  | EAliasAddPtr (id1,id2,i,e) ->
    EAliasAddPtr(id1, id2, i, elim_v env f_id args e)
  | EAssert (e1,e2) ->
    EAssert(elim_v env f_id args e1, elim_v env f_id args e2)
  | ESeq (e1,e2) ->
    ESeq(elim_v env f_id args e1, elim_v env f_id args e2)
  | EApp (id,es) ->
    EApp(id, List.map (elim_v env f_id args) es)
  | EEq (e1,e2) ->
    EEq(elim_v env f_id args e1, elim_v env f_id args e2)
  | ELt (e1, e2) ->
    ELt(elim_v env f_id args e1, elim_v env f_id args e2)
  | EGt (e1, e2) ->
    EGt(elim_v env f_id args e1, elim_v env f_id args e2)
  | ELeq (e1, e2) ->
    ELeq(elim_v env f_id args e1, elim_v env f_id args e2)
  | EGeq (e1, e2) ->
    EGeq(elim_v env f_id args e1, elim_v env f_id args e2)
  | ENeq (e1, e2) ->
    ENeq(elim_v env f_id args e1, elim_v env f_id args e2)
  | EAnd (e1,e2) ->
    EAnd(elim_v env f_id args e1, elim_v env f_id args e2)
  | EOr (e1,e2) ->
    EOr(elim_v env f_id args e1, elim_v env f_id args e2)
  | ENot e ->
    ENot (elim_v env f_id args e)
  | EAdd (e1,e2) -> 
    EAdd(elim_v env f_id args e1, elim_v env f_id args e2)
  | ESub (e1,e2) -> 
    ESub(elim_v env f_id args e1, elim_v env f_id args e2)
  | EMul (e1,e2) -> 
    EMul(elim_v env f_id args e1, elim_v env f_id args e2)
  | EDiv (e1,e2) -> 
    EDiv(elim_v env f_id args e1, elim_v env f_id args e2)
  | EVar x -> 
    if List.mem x args then 
      EVar x
    else if lookup x (lookup f_id !all_tyenv) = TyInt then
      lookup x env
    else 
      EVar x
  | _ -> exp

let rec exp_subst subst exp = 
  match exp with
  | ELetInt (id,e1,e2) -> 
    ELetInt(id, exp_subst subst e1, exp_subst subst e2)
  | ELetVarPtr (id1,id2,e) ->
    ELetVarPtr(id1, id2, exp_subst subst e)
  | ELetDerefPtr (id1,id2,e) ->
    ELetDerefPtr(id1, id2, exp_subst subst e)
  | ELetAddPtr (id1,id2,e1,e2) ->
    ELetAddPtr(id1, id2, exp_subst subst e1, exp_subst subst e2)
  | ELetSubPtr (id1,id2,e1,e2) ->
    ELetSubPtr(id1, id2, exp_subst subst e1, exp_subst subst e2)
  | EIf (e1,e2,e3) ->
    EIf(exp_subst subst e1, exp_subst subst e2, exp_subst subst e3)
  | EMkarray (id,i,e) ->
    EMkarray(id, i, exp_subst subst e)
  | EAssign (id1,e1,e2) ->
    EAssign(id1, exp_subst subst e1, exp_subst subst e2)
  | EAssignInt (id,e1,e2) ->
    EAssignInt(id, exp_subst subst e1, exp_subst subst e2)
  | EAssignPtr (id1,id2,e) ->
    EAssignPtr(id1, id2, exp_subst subst e)
  | EAlias (e1,e2,e3) ->
    EAlias(exp_subst subst e1, exp_subst subst e2, exp_subst subst e3) 
  | EAliasVarPtr (id1,id2,e) ->
    EAliasVarPtr(id1, id2, exp_subst subst e)
  | EAliasDerefPtr (id1,id2,e) ->
    EAliasDerefPtr(id1, id2, exp_subst subst e)
  | EAliasAddPtr (id1,id2,i,e) ->
    EAliasAddPtr(id1, id2, i, exp_subst subst e)
  | EAssert (e1,e2) ->
    EAssert(exp_subst subst e1, exp_subst subst e2)
  | ESeq (e1,e2) ->
    ESeq(exp_subst subst e1, exp_subst subst e2)
  | EApp (id,es) ->
    EApp(id, List.map (exp_subst subst) es)
  | EEq (e1,e2) ->
    EEq(exp_subst subst e1, exp_subst subst e2)
  | ELt (e1, e2) ->
    ELt(exp_subst subst e1, exp_subst subst e2)
  | EGt (e1, e2) ->
    EGt(exp_subst subst e1, exp_subst subst e2)
  | ELeq (e1, e2) ->
    ELeq(exp_subst subst e1, exp_subst subst e2)
  | EGeq (e1, e2) ->
    EGeq(exp_subst subst e1, exp_subst subst e2)
  | ENeq (e1, e2) ->
    ENeq(exp_subst subst e1, exp_subst subst e2)
  | EAnd (e1,e2) ->
    EAnd(exp_subst subst e1, exp_subst subst e2)
  | EOr (e1,e2) ->
    EOr(exp_subst subst e1, exp_subst subst e2)
  | ENot e ->
    ENot (exp_subst subst e)
  | EAdd (e1,e2) -> 
    EAdd(exp_subst subst e1, exp_subst subst e2)
  | ESub (e1,e2) -> 
    ESub(exp_subst subst e1, exp_subst subst e2)
  | EMul (e1,e2) -> 
    EMul(exp_subst subst e1, exp_subst subst e2)
  | EDiv (e1,e2) -> 
    EDiv(exp_subst subst e1, exp_subst subst e2)
  | EVar x -> 
    (try 
       lookup x subst
     with
       Unbound -> exp)
  | _ -> exp

let rec exp_to_smtlib exp = 
  match exp with 
  | EEq (e1,e2) ->
    let s1 = exp_to_smtlib e1 in
    let s2 = exp_to_smtlib e2 in
    Eq(s1, s2)
  | ELt (e1, e2) ->
    let s1 = exp_to_smtlib e1 in
    let s2 = exp_to_smtlib e2 in
    Lt(s1, s2)
  | EGt (e1, e2) ->
    let s1 = exp_to_smtlib e1 in
    let s2 = exp_to_smtlib e2 in
    Gt(s1, s2)
  | ELeq (e1, e2) ->
    let s1 = exp_to_smtlib e1 in
    let s2 = exp_to_smtlib e2 in
    Leq(s1, s2)
  | EGeq (e1, e2) ->
    let s1 = exp_to_smtlib e1 in
    let s2 = exp_to_smtlib e2 in
    Geq(s1, s2)
  | ENeq (e1, e2) ->
    let s1 = exp_to_smtlib e1 in
    let s2 = exp_to_smtlib e2 in
    Not(Eq(s1, s2))
  | EAnd (e1,e2) ->
    let s1 = exp_to_smtlib e1 in
    let s2 = exp_to_smtlib e2 in
    And(s1, s2)
  | EOr (e1,e2) ->
    let s1 = exp_to_smtlib e1 in
    let s2 = exp_to_smtlib e2 in
    Or(s1, s2)
  | ENot e ->
    let s = exp_to_smtlib e in
    Not s
  | EAdd (e1,e2) -> 
    let s1 = exp_to_smtlib e1 in
    let s2 = exp_to_smtlib e2 in
    Add(s1, s2)
  | ESub (e1,e2) -> 
    let s1 = exp_to_smtlib e1 in
    let s2 = exp_to_smtlib e2 in
    Sub(s1, s2)
  | EMul (e1,e2) -> 
    let s1 = exp_to_smtlib e1 in
    let s2 = exp_to_smtlib e2 in
    Mul(s1, s2)
  | EDiv (e1,e2) -> 
    let s1 = exp_to_smtlib e1 in
    let s2 = exp_to_smtlib e2 in
    Div(s1, s2)
  | EConstInt i ->
    if i >= 0 then
      Id (string_of_int i)
    else 
      Id ("(- " ^ string_of_int (-i) ^ ")")
  | EVar x -> 
    FV x
  | _ -> raise ElimError

let rec fvs_of_exp exp = 
  match exp with
  | EEq (e1,e2) ->
    let fvs1 = fvs_of_exp e1 in
    let fvs2 = fvs_of_exp e2 in
    fvs1 @ fvs2
  | ELt (e1, e2) ->
    let fvs1 = fvs_of_exp e1 in
    let fvs2 = fvs_of_exp e2 in
    fvs1 @ fvs2
  | EGt (e1, e2) ->
    let fvs1 = fvs_of_exp e1 in
    let fvs2 = fvs_of_exp e2 in
    fvs1 @ fvs2
  | ELeq (e1, e2) ->
    let fvs1 = fvs_of_exp e1 in
    let fvs2 = fvs_of_exp e2 in
    fvs1 @ fvs2
  | EGeq (e1, e2) ->
    let fvs1 = fvs_of_exp e1 in
    let fvs2 = fvs_of_exp e2 in
    fvs1 @ fvs2
  | ENeq (e1, e2) ->
    let fvs1 = fvs_of_exp e1 in
    let fvs2 = fvs_of_exp e2 in
    fvs1 @ fvs2
  | EAnd (e1,e2) ->
    let fvs1 = fvs_of_exp e1 in
    let fvs2 = fvs_of_exp e2 in
    fvs1 @ fvs2
  | EOr (e1,e2) ->
    let fvs1 = fvs_of_exp e1 in
    let fvs2 = fvs_of_exp e2 in
    fvs1 @ fvs2
  | ENot e ->
    let fvs = fvs_of_exp e in
    fvs
  | EAdd (e1,e2) -> 
    let fvs1 = fvs_of_exp e1 in
    let fvs2 = fvs_of_exp e2 in
    fvs1 @ fvs2
  | ESub (e1,e2) -> 
    let fvs1 = fvs_of_exp e1 in
    let fvs2 = fvs_of_exp e2 in
    fvs1 @ fvs2
  | EMul (e1,e2) -> 
    let fvs1 = fvs_of_exp e1 in
    let fvs2 = fvs_of_exp e2 in
    fvs1 @ fvs2
  | EDiv (e1,e2) -> 
    let fvs1 = fvs_of_exp e1 in
    let fvs2 = fvs_of_exp e2 in
    fvs1 @ fvs2
  | EConstInt i -> []
  | EVar x -> [x]
  | _ -> []

let rec ret_of_exp cond exp = 
  match exp with
  | ELetInt (id,e1,e2) -> 
    ret_of_exp cond e2
  | ELetVarPtr (id1,id2,e) ->
    ret_of_exp cond e
  | ELetDerefPtr (id1,id2,e) ->
    ret_of_exp cond e
  | ELetAddPtr (id1,id2,e1,e2) ->
    ret_of_exp cond e2
  | ELetSubPtr (id1,id2,e1,e2) ->
    ret_of_exp cond e2
  | EIf (e1,e2,e3) ->
    let cond_sl = exp_to_smtlib e1 in
    ret_of_exp (cond_sl :: cond) e2 @ ret_of_exp (Not(cond_sl) :: cond) e3
  | EMkarray (id,i,e) ->
    ret_of_exp cond e
  | EAssign (id1,e1,e2) ->
    ret_of_exp cond e2
  | EAssignInt (id,e1,e2) ->
    ret_of_exp cond e2
  | EAssignPtr (id1,id2,e) ->
    ret_of_exp cond e
  | EAlias (e1,e2,e3) ->
    ret_of_exp cond e3
  | EAliasVarPtr (id1,id2,e) ->
    ret_of_exp cond e
  | EAliasDerefPtr (id1,id2,e) ->
    ret_of_exp cond e
  | EAliasAddPtr (id1,id2,i,e) ->
    ret_of_exp cond e
  | EAssert (e1,e2) ->
    ret_of_exp cond e2
  | ESeq (e1,e2) ->
    ret_of_exp cond e2
  | _ -> [(cond, exp)]

let rec smtlib_subst subst st = 
  match st with
  | Or (st1,st2) ->
    Or(smtlib_subst subst st1, smtlib_subst subst st2)
  | And (st1,st2) ->
    And(smtlib_subst subst st1, smtlib_subst subst st2)
  | Imply (st1,st2) ->
    Imply(smtlib_subst subst st1, smtlib_subst subst st2)
  | Not st ->
    Not (smtlib_subst subst st)
  | Eq (st1,st2) ->
    Eq(smtlib_subst subst st1, smtlib_subst subst st2)
  | Lt (st1,st2) ->
    Lt(smtlib_subst subst st1, smtlib_subst subst st2)
  | Gt (st1,st2) ->
    Gt(smtlib_subst subst st1, smtlib_subst subst st2)
  | Leq (st1,st2) ->
    Leq(smtlib_subst subst st1, smtlib_subst subst st2)
  | Geq (st1,st2) ->
    Geq(smtlib_subst subst st1, smtlib_subst subst st2)
  | Add (st1,st2) ->
    Add(smtlib_subst subst st1, smtlib_subst subst st2)
  | Sub (st1,st2) ->
    Sub(smtlib_subst subst st1, smtlib_subst subst st2)
  | Mul (st1,st2) ->
    Mul(smtlib_subst subst st1, smtlib_subst subst st2)
  | Div (st1,st2) ->
    Div(smtlib_subst subst st1, smtlib_subst subst st2)
  | FV x -> 
    (try 
       exp_to_smtlib (lookup x subst)
     with
       Unbound -> st)
  | _ -> st