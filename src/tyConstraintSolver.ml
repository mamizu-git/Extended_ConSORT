open TySyntax

exception TyError

type subst = (tyvar * ty) list
type constraints = (ty * ty) list

let rec ty_subst s ty =
  match ty with
  | TyRef t -> 
    let t' = ty_subst s t in
    TyRef t'
  | TyFun (t_ids,t_ret) -> 
    let t_ids' = List.map (ty_subst s) t_ids in
    let t_ret' = ty_subst s t_ret in
    TyFun(t_ids', t_ret')
  | TyVar a -> 
    (try
       lookup a s
     with Unbound ->
       ty)
  | _ -> ty

let rec occur_check a ty = 
  match ty with
  | TyRef t -> occur_check a t
  | TyFun (t_ids,t_ret) -> (List.fold_left (fun b ty -> b || occur_check a ty) false t_ids) || occur_check a t_ret
  | TyVar a' -> a = a'
  | _ -> false

let rec include_var ty = 
  match ty with
  | TyRef t -> include_var t
  | TyFun (t_ids,t_ret) -> (List.fold_left (fun b ty -> b || include_var ty) false t_ids) || include_var t_ret
  | TyVar _ -> true
  | _ -> false

let rec ty_unify c = 
  match c with
  | (s,t)::c' when s = t -> 
    ty_unify c'
  | (TyRef t1, TyRef t2)::c' -> 
    ty_unify ((t1, t2) :: c')
  | (TyFun (ts1,t1), TyFun (ts2,t2))::c' -> 
    ty_unify ((t1,t2) :: (List.map2 (fun x y -> (x,y)) ts1 ts2) @ c')
  | (TyVar a, t)::c' | (t, TyVar a)::c' ->
    if occur_check a t then 
      raise TyError
    else if include_var t then
      ty_unify (c'@[(t, TyVar a)])
    else 
      let sub_c' = List.map (fun (t1,t2) -> (ty_subst [(a,t)] t1, ty_subst [(a,t)] t2)) c' in
      (a, t) :: ty_unify sub_c'
  | [] -> []
  | _ -> raise TyError