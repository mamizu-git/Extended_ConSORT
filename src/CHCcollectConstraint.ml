open Syntax
open TySyntax
open SimpleTyping
open Elim

exception ConstrError

let fn_env_chc : (id * ((ftype_id * ftype) list * (ftype_id * ftype) list * ftype)) list ref = ref []

let rec chc_collect_exp env f_id args l exp =
  match exp with
  | EIf (e1,e2,e3) ->
    let c1 = chc_collect_exp env f_id args l e1 in (* needless? *)
    let c2 = chc_collect_exp env f_id args (l+1) e2 in
    let c3 = chc_collect_exp env f_id args (l+1) e3 in
    (* let e1' = elim_v env f_id args e1 in *)
    CHCIf(e1, c2, c3, l) :: c1
  | ELetInt (id,e1,e2) ->
    (* let e1' = elim_v env f_id args e1 in *)
    (* let env' = (id, e1') :: env in *)
    (* let c1 = chc_collect_exp env' f_id args l e1' in *)
    let c2 = chc_collect_exp env f_id args (l+1) e2 in
    CHCLetInt(id, e1, l) :: c2
    (* c1 @ c2 *)
  | ELetVarPtr (id1,id2,e) ->
    let c = chc_collect_exp env f_id args (l+1) e in
    CHCLet(id1, id2, l) :: c
  | ELetDerefPtr (id1,id2,e) ->
    let c = chc_collect_exp env f_id args (l+1) e in
    CHCLetDeref(id1, id2, l) :: c
  | ELetAddPtr (id1,id2,e1,e2) ->
    let c1 = chc_collect_exp env f_id args l e1 in
    let c2 = chc_collect_exp env f_id args (l+1) e2 in
    CHCLetAddPtr(id1, id2, e1, l) :: c1 @ c2
  | ELetSubPtr (id1,id2,e1,e2) ->
    let c1 = chc_collect_exp env f_id args l e1 in
    let c2 = chc_collect_exp env f_id args (l+1) e2 in
    CHCLetSubPtr(id1, id2, e1, l) :: c1 @ c2
  | EMkarray (id,i,e) ->
    let c = chc_collect_exp env f_id args (l+1) e in
    CHCMkArray(id, i, l) :: c
  | EAssignInt (id,e1,e2) ->
    (* let e1' = elim_v env f_id args e1 in *)
    (* let c1 = chc_collect_exp env f_id args l e1' in *)
    let c2 = chc_collect_exp env f_id args (l+1) e2 in
    CHCAssignInt(id, e1, l) :: c2
  | EAssignPtr (id1,id2,e) ->
    let c = chc_collect_exp env f_id args (l+1) e in
    CHCAssignRef(id1, id2, l) :: c
  | EAliasVarPtr (id1,id2,e) -> 
    let c = chc_collect_exp env f_id args (l+1) e in
    CHCAlias(id1, id2, l) :: c
  | EAliasDerefPtr (id1,id2,e) -> 
    let c = chc_collect_exp env f_id args (l+1) e in
    CHCAliasDeref(id1, id2, l) :: c
  | EAliasAddPtr (id1,id2,e1,e2) -> 
    let c1 = chc_collect_exp env f_id args l e1 in
    let c2 = chc_collect_exp env f_id args (l+1) e2 in
    CHCAliasAddPtr(id1, id2, e1, l) :: c1 @ c2
  | EAssert (e1,e2) ->
    (* let c1 = chc_collect_exp env f_id args l e1 in *)
    let c2 = chc_collect_exp env f_id args (l+1) e2 in
    CHCAssert(e1, l) :: c2
  | ESeq (e1,e2) ->
    let c1 = chc_collect_exp env f_id args l e1 in
    let c2 = chc_collect_exp env f_id args (l+1) e2 in
    c1 @ c2
  (* | EDeref id ->
    [CDeref(id, l)] *)
  | EApp (id,es) ->
    let cs = List.concat (List.map (chc_collect_exp env f_id args l) es) in
    (* let TyFun (t_args, _) = lookup id (lookup "main" !all_tyenv) in
    let g t e =
      match t, e with
      | TyRef _, EVar id -> AId id
      | TyInt, _ -> AExp (elim_v env f_id args e)
      | _ -> raise ConstrError
    in
    let args = List.map2 g t_args es in *)
    CHCApp(id, es, l) :: cs
  | _ -> []

let elim_hash ftid =
  match ftid with
  | RawId id -> id
  | HashId id -> id

let chc_collect_fdef fdef =
  let (id, ids, ann, e) = fdef in
  let (ftid_fts1, ftid_fts2, ft) = ann in
  let args = List.map elim_hash (List.map fst ftid_fts1) in 
  let e_rets = ret_of_exp e in
  fn_env_chc := (id, (ftid_fts1, ftid_fts2, ft)) :: !fn_env_chc;
  (id, chc_collect_exp [] id args 1 e, e_rets)

let chc_collect_prog prog = 
  let (fdefs, e) = prog in
  let ics = List.map chc_collect_fdef fdefs in
  fn_env_chc := ("main", ([], [], FTInt(Id "true"))) :: !fn_env_chc;
  let ic = ("main", chc_collect_exp [] "main" [] 1 e, []) in
  let all_cs = ic :: ics in
  all_cs

