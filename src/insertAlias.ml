open Syntax
open TySyntax
open SimpleTyping

exception InsertError

let flag = true

let rec insert_sub alias exp =
  match exp with
  | ELet (id,e1,e2) -> ELet(id, e1, insert_sub alias e2)
  | ELetInt(id,e1,e2) -> ELetInt(id, e1, insert_sub alias e2)
  | ELetVarPtr (id1,id2,e) -> ELetVarPtr(id1, id2, insert_sub alias e)
  | ELetDerefPtr (id1,id2,e) -> ELetDerefPtr(id1, id2, insert_sub alias e)
  | ELetAddPtr (id1,id2,e1,e2) -> ELetAddPtr(id1, id2, e1, insert_sub alias e2)
  | ELetSubPtr (id1,id2,e1,e2) -> ELetSubPtr(id1, id2, e1, insert_sub alias e2)
  | EIf (e1,e2,e3) -> EIf(e1, insert_sub alias e2, insert_sub alias e3)
  | EMkarray (id,i,e) -> EMkarray(id, i, insert_sub alias e)
  | EAssign(id,e1,e2) -> EAssign (id, e1, insert_sub alias e2)
  | EAssignInt(id,e1,e2) -> EAssignInt (id, e1, insert_sub alias e2)
  | EAssignPtr(id1,id2,e) -> EAssignPtr (id1, id2, insert_sub alias e)
  | EAssert (e1,e2) -> EAssert(e1, insert_sub alias e2)
  | ESeq (e1,e2) -> ESeq(e1, insert_sub alias e2)
  | _ -> alias exp

let rec insert_alias exp = 
  match exp with
  | ELetVarPtr (id1,id2,e) ->
    let alias e' = EAliasVarPtr(id1,id2,e') in 
    ELetVarPtr(id1, id2, insert_sub alias (insert_alias e))
  | ELetDerefPtr (id1,id2,e) ->
    let alias e' = EAliasDerefPtr(id1,id2,e') in 
    ELetDerefPtr(id1, id2, insert_sub alias (insert_alias e))
  | ELetAddPtr (id1,id2,e1,e2) -> 
    let alias e' = EAliasAddPtr(id1,id2,e1,e') in 
    ELetAddPtr(id1, id2, e1, insert_sub alias (insert_alias e2))
  | ELetSubPtr (id1,id2,e1,e2) -> 
    let alias e' = EAliasAddPtr(id2,id1,e1,e') in 
    ELetSubPtr(id1, id2, e1, insert_sub alias (insert_alias e2)) 
  | ELet (id,e1,e2) -> ELet (id, insert_alias e1, insert_alias e2)
  | ELetInt(id,e1,e2) -> ELetInt (id, insert_alias e1, insert_alias e2)
  | EIf (e1,e2,e3) -> EIf(insert_alias e1, insert_alias e2, insert_alias e3)
  | EMkarray (id,i,e) -> EMkarray(id, i, insert_alias e)
  | EAssign(id,e1,e2) -> EAssign (id, insert_alias e1, insert_alias e2)
  | EAssignInt(id,e1,e2) -> EAssignInt (id, insert_alias e1, insert_alias e2)
  | EAssignPtr(id1,id2,e) -> EAssignPtr (id1, id2, insert_alias e)
  | EAssert (e1,e2) -> EAssert(insert_alias e1, insert_alias e2)
  | ESeq (e1,e2) -> ESeq(insert_alias e1, insert_alias e2)
  | EApp (id,es) -> EApp(id, List.map (insert_alias) es)
  | EEq (e1,e2) -> EEq(insert_alias e1, insert_alias e2)
  | ELt (e1,e2) -> ELt(insert_alias e1, insert_alias e2)
  | EGt (e1,e2) -> EGt(insert_alias e1, insert_alias e2)
  | ELeq (e1,e2) -> ELeq(insert_alias e1, insert_alias e2)
  | EGeq (e1,e2) -> EGeq(insert_alias e1, insert_alias e2)
  | ENeq (e1,e2) -> ENeq(insert_alias e1, insert_alias e2)
  | EAnd (e1,e2) -> EAnd(insert_alias e1, insert_alias e2)
  | EOr (e1,e2) -> EOr(insert_alias e1, insert_alias e2)
  | ENot e -> ENot(insert_alias e)
  | EAdd (e1,e2) -> EAdd(insert_alias e1, insert_alias e2)
  | ESub (e1,e2) -> ESub(insert_alias e1, insert_alias e2)
  | EMul (e1,e2) -> EMul(insert_alias e1, insert_alias e2)
  | EDiv (e1,e2) -> EDiv(insert_alias e1, insert_alias e2)
  | _ -> exp

let f prog = 
  let (fdefs, e) = prog in
  let fdefs' = List.map (fun (id,ids,ann,e) -> (id, ids, ann, insert_alias e)) fdefs in
  let e' = insert_alias e in
  if flag then 
    (fdefs', e')
  else
    (fdefs, e)