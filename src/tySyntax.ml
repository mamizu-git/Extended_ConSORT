exception Unbound
exception TyError

type tyvar = int 

type ty =
  | TyUnit
  | TyInt
  | TyBool
  | TyRef of ty
  | TyFun of ty list * ty
  | TyVar of tyvar

let tyvar_count = ref 0

let new_tyvar () = tyvar_count := !tyvar_count + 1; !tyvar_count

let rec lookup x env =
  try List.assoc x env with Not_found -> raise Unbound

let rec print_type ty =
  match ty with
  | TyUnit -> print_string "unit"
  | TyInt -> print_string "int"
  | TyBool -> print_string "bool"
  | TyRef t -> print_type t; print_string " ref"
  | TyFun (ts,t1) -> print_string "("; print_types ts; print_string " -> "; print_type t1; print_string ")"
  | TyVar a -> print_string "'a"; print_int a
and print_types tys = 
  match tys with
  | [] -> ()
  | ty :: [] -> print_type ty
  | ty :: tys' -> print_type ty; print_string ", "; print_types tys'

let rec print_tyenv tyenv = 
  print_string "{ ";
  print_tyenv_sub tyenv;
  print_string "}"
and print_tyenv_sub tyenv =
  match tyenv with
  | [] -> ()
  | (id,ty) :: [] -> print_string (id ^ ": "); print_type ty; print_string " "
  | (id,ty) :: tyenv' -> print_string (id ^ ": "); print_type ty; print_string ", "; print_tyenv_sub tyenv'

let rec print_all_tyenv all_tyenv = 
  print_string "[ ";
  print_all_tyenv_sub all_tyenv;
  print_string "]"
and print_all_tyenv_sub all_tyenv = 
  match all_tyenv with
  | [] -> ()
  | (id,tyenv) :: [] -> print_string (id ^ ": "); print_tyenv tyenv; print_string " "
  | (id,tyenv) :: all_tyenv' -> print_string (id ^ ": "); print_tyenv tyenv; print_string ", "; print_all_tyenv_sub all_tyenv'
