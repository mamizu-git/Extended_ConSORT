open Syntax
open TySyntax
open SimpleTyping
open Elim

exception ConstrError

let fn_env : (id * ((ftype_id * ftype) list * (ftype_id * ftype) list)) list ref = ref []

let rec collect_exp env f_id args l exp =
  match exp with
  | EIf (e1,e2,e3) ->
    let c1 = collect_exp env f_id args l e1 in (* needless? *)
    let c2 = collect_exp env f_id args (l+1) e2 in
    let c3 = collect_exp env f_id args (l+1) e3 in
    let e1' = elim_v env f_id args e1 in
    CIf(e1', c2, c3, l) :: c1
  | ELetInt (id,e1,e2) ->
    let e1' = elim_v env f_id args e1 in
    let env' = (id, e1') :: env in
    let c1 = collect_exp env' f_id args l e1' in
    let c2 = collect_exp env' f_id args (l+1) e2 in
    c1 @ c2
  | ELetVarPtr (id1,id2,e) ->
    let c = collect_exp env f_id args (l+1) e in
    CLet(id1, id2, l) :: c
  | ELetDerefPtr (id1,id2,e) ->
    let c = collect_exp env f_id args (l+1) e in
    CLetDeref(id1, id2, l) :: c
  | ELetAddPtr (id1,id2,i,e) ->
    let c = collect_exp env f_id args (l+1) e in
    CLetAddPtr(id1, id2, i, l) :: c
  | EMkarray (id,i,e) ->
    let c = collect_exp env f_id args (l+1) e in
    CMkArray(id, i, l) :: c
  | EAssignInt (id,e1,e2) ->
    let c1 = collect_exp env f_id args l e1 in
    let c2 = collect_exp env f_id args (l+1) e2 in
    CAssignInt(id, l) :: c1 @ c2
  | EAssignPtr (id1,id2,e) ->
    let c = collect_exp env f_id args (l+1) e in
    CAssignRef(id1, id2, l) :: c
  | EAliasVarPtr (id1,id2,e) -> 
    let c = collect_exp env f_id args (l+1) e in
    CAlias(id1, id2, l) :: c
  | EAliasDerefPtr (id1,id2,e) -> 
    let c = collect_exp env f_id args (l+1) e in
    CAliasDeref(id1, id2, l) :: c
  | EAliasAddPtr (id1,id2,i,e) -> 
    let c = collect_exp env f_id args (l+1) e in
    CAliasAddPtr(id1, id2, i, l) :: c
  | EAssert (e1,e2) ->
    let c1 = collect_exp env f_id args l e1 in
    let c2 = collect_exp env f_id args (l+1) e2 in
    c1 @ c2
  | ESeq (e1,e2) ->
    let c1 = collect_exp env f_id args l e1 in
    let c2 = collect_exp env f_id args (l+1) e2 in
    c1 @ c2
  | EDeref id ->
    [CDeref(id, l)]
  | EApp (id,es) ->
    let cs = List.concat (List.map (collect_exp env f_id args l) es) in
    let TyFun (t_args, _) = lookup id (lookup "main" !all_tyenv) in
    let g t e =
      match t, e with
      | TyRef _, EVar id -> AId id
      | TyInt, _ -> AExp (elim_v env f_id args e)
      | _ -> raise ConstrError
    in
    let args = List.map2 g t_args es in
    CApp(id, args, l) :: cs
  | _ -> []

let elim_hash ftid =
  match ftid with
  | RawId id -> id
  | HashId id -> id

let collect_fdef fdef =
  let (id, ids, ann, e) = fdef in
  let (ftid_fts1, ftid_fts2, ft) = ann in
  let args = List.map elim_hash (List.map fst ftid_fts1) in 
  fn_env := (id, (ftid_fts1, ftid_fts2)) :: !fn_env;
  (id, collect_exp [] id args 1 e)

let collect_prog prog = 
  let (fdefs, e) = prog in
  let ics = List.map collect_fdef fdefs in
  fn_env := ("main", ([], [])) :: !fn_env;
  let ic = ("main", collect_exp [] "main" [] 1 e) in
  let all_cs = ic :: ics in
  all_cs

