open Syntax
open TySyntax
open SimpleTyping

exception ConvertError

let rec g f_id exp = 
  match exp with
  | ELet (id,e1,e2) ->
    if lookup id (lookup f_id !all_tyenv) = TyInt then
      ELetInt(id, g f_id e1, g f_id e2)
    else 
      (match e1 with
       | EVar id1 -> ELetVarPtr(id, id1, g f_id e2)
       | EDeref id1 -> ELetDerefPtr(id, id1, g f_id e2)
       | EAdd (EVar id1, EConstInt i) -> ELetAddPtr(id, id1, i, g f_id e2) 
       | ESub (EVar id1, EConstInt i) -> ELetAddPtr(id, id1, -i, g f_id e2)
       | _ -> raise ConvertError)
  | EAssign (id,e1,e2) ->
    if lookup id (lookup f_id !all_tyenv) = TyRef (TyInt) then 
      EAssignInt(id, g f_id e1, g f_id e2)
    else
      let EVar id1 = e1 in (* cannot deal with "p := q + 1" *)
      EAssignPtr(id, id1, g f_id e2)
  | EAlias (e1,e2,e3) -> 
    let EVar id1 = e1 in
    (match e2 with
     | EVar id2 -> EAliasVarPtr(id1, id2, g f_id e3)
     | EDeref id2 -> EAliasDerefPtr(id1, id2, g f_id e3)
     | EAdd (EVar id2, EConstInt i) -> EAliasAddPtr(id1, id2, i, g f_id e3)
     | ESub (EVar id2, EConstInt i) -> EAliasAddPtr(id1, id2, -i, g f_id e3)
     | _ -> raise ConvertError)
  | EIf (e1,e2,e3) -> EIf(g f_id e1, g f_id e2, g f_id e3)
  | EMkarray (id,i,e) -> EMkarray(id, i, g f_id e)
  | EAssert (e1,e2) -> EAssert(g f_id e1, g f_id e2)
  | ESeq (e1,e2) -> ESeq(g f_id e1, g f_id e2)
  | EApp (id,es) -> EApp(id, List.map (g f_id) es)
  | EEq (e1,e2) -> EEq(g f_id e1, g f_id e2)
  | ELt (e1,e2) -> ELt(g f_id e1, g f_id e2)
  | EGt (e1,e2) -> EGt(g f_id e1, g f_id e2)
  | ELeq (e1,e2) -> ELeq(g f_id e1, g f_id e2)
  | EGeq (e1,e2) -> EGeq(g f_id e1, g f_id e2)
  | ENeq (e1,e2) -> ENeq(g f_id e1, g f_id e2)
  | EAnd (e1,e2) -> EAnd(g f_id e1, g f_id e2)
  | EOr (e1,e2) -> EOr(g f_id e1, g f_id e2)
  | ENot e -> ENot(g f_id e)
  | EAdd (e1,e2) -> EAdd(g f_id e1, g f_id e2)
  | ESub (e1,e2) -> ESub(g f_id e1, g f_id e2)
  | EMul (e1,e2) -> EMul(g f_id e1, g f_id e2)
  | EDiv (e1,e2) -> EDiv(g f_id e1, g f_id e2)
  | _ -> exp

let convert prog = 
  let (fdefs, e) = prog in
  let fdefs' = List.map (fun (id,ids,ann,e) -> (id, ids, ann, g id e)) fdefs in
  let e' = g "main" e in
  (fdefs', e')