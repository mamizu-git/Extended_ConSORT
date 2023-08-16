exception Error

type id = string
type pos = int

let intpred_env : (id * id list) list ref = ref []

type smtlib = 
  | Or of smtlib * smtlib
  | And of smtlib * smtlib
  | Imply of smtlib * smtlib
  | Not of smtlib
  | Eq of smtlib * smtlib
  | Lt of smtlib * smtlib
  | Gt of smtlib * smtlib
  | Leq of smtlib * smtlib
  | Geq of smtlib * smtlib
  | Add of smtlib * smtlib
  | Sub of smtlib * smtlib
  | Mul of smtlib * smtlib
  | Div of smtlib * smtlib
  | FV of id
  | Id of id
  | IntPred of id * id list
  | IntVarPred of int * id * id list
  | PtrPred of id * pos * smtlib * smtlib
  | PtrVarPred of int * id * id * smtlib * smtlib
  | VarPred
  | Ands of smtlib list

type exp = 
  | ELet of id * exp * exp
  | ELetInt of id * exp * exp
  | ELetVarPtr of id * id * exp
  | ELetDerefPtr of id * id * exp
  | ELetAddPtr of id * id * int * exp
  | EIf of exp * exp * exp
  | EMkarray of id * int * exp
  | EAssign of id * exp * exp
  | EAssignInt of id * exp * exp
  | EAssignPtr of id * id * exp
  | EAlias of exp * exp * exp
  | EAliasVarPtr of id * id * exp
  | EAliasDerefPtr of id * id * exp
  | EAliasAddPtr of id * id * int * exp
  | EAssert of exp * exp
  | ESeq of exp * exp
  | EDeref of id
  | EApp of id * exp list
  | EEq of exp * exp
  | ELt of exp * exp
  | EGt of exp * exp
  | ELeq of exp * exp
  | EGeq of exp * exp
  | ENeq of exp * exp
  | EAnd of exp * exp
  | EOr of exp * exp
  | ENot of exp
  | EAdd of exp * exp
  | ESub of exp * exp
  | EMul of exp * exp
  | EDiv of exp * exp
  | EConstUnit
  | EConstFail
  | EConstInt of int
  | EConstTrue
  | EConstFalse
  | EVar of id

type ftype = 
  | FTInt of smtlib
  | FTRef of ftype * exp * exp * float 

type ftype_id =
  | RawId of id
  | HashId of id

type annotation = (ftype_id * ftype) list * (ftype_id * ftype) list * ftype
type fdef = id * id list * annotation * exp
type program = fdef list * exp

type constr = 
  | CIf of exp * constr list * constr list * pos
  | CLet of id * id * pos
  | CLetDeref of id * id * pos
  | CLetAddPtr of id * id * int * pos (* let p = q + x in ができない*)
  | CMkArray of id * int * pos
  | CAssignInt of id * pos
  | CAssignRef of id * id * pos
  | CAlias of id * id * pos
  | CAliasDeref of id * id * pos
  | CAliasAddPtr of id * id * int * pos
  | CDeref of id * pos
  | CApp of id * arg list * pos
and arg = 
  | AExp of exp
  | AId of id

type chc = 
  | CHCIf of exp * chc list * chc list * pos
  | CHCLetInt of id * exp * pos
  | CHCLet of id * id * pos
  | CHCLetDeref of id * id * pos
  | CHCLetAddPtr of id * id * int * pos (* let p = q + x in ができない*)
  | CHCMkArray of id * int * pos
  | CHCAssignInt of id * exp * pos
  | CHCAssignRef of id * id * pos
  | CHCAlias of id * id * pos
  | CHCAliasDeref of id * id * pos
  | CHCAliasAddPtr of id * id * int * pos
  | CHCAssert of exp * pos
  | CHCApp of id * exp list * pos

let rec print_ids ids = 
  match ids with
  | [] -> ()
  | id :: [] -> print_string id
  | id :: ids' -> print_string (id ^ ", "); print_ids ids'

let rec print_smtlib oc sl bool_id n num = 
  match sl with 
  | Or (s1,s2) -> 
    (output_string oc "(or ";
     print_smtlib oc s1 bool_id n num;
     output_string oc " ";
     print_smtlib oc s2 bool_id n num;
     output_string oc ")")
  | And (s1,s2) -> 
    (output_string oc "(and ";
     print_smtlib oc s1 bool_id n num;
     output_string oc " ";
     print_smtlib oc s2 bool_id n num;
     output_string oc ")")
  | Imply (s1,s2) -> 
    (output_string oc "(=> ";
     print_smtlib oc s1 bool_id n num;
     output_string oc " ";
     print_smtlib oc s2 bool_id n num;
     output_string oc ")")
  | Not s -> 
    (output_string oc "(not ";
     print_smtlib oc s bool_id n num;
     output_string oc ")")
  | Eq (s1,s2) -> 
    (output_string oc "(= ";
     print_smtlib oc s1 bool_id n num;
     output_string oc " ";
     print_smtlib oc s2 bool_id n num;
     output_string oc ")")
  | Lt (s1,s2) -> 
    (output_string oc "(< ";
     print_smtlib oc s1 bool_id n num;
     output_string oc " ";
     print_smtlib oc s2 bool_id n num;
     output_string oc ")")
  | Gt (s1,s2) -> 
    (output_string oc "(> ";
     print_smtlib oc s1 bool_id n num;
     output_string oc " ";
     print_smtlib oc s2 bool_id n num;
     output_string oc ")")
  | Leq (s1,s2) -> 
    (output_string oc "(<= ";
     print_smtlib oc s1 bool_id n num;
     output_string oc " ";
     print_smtlib oc s2 bool_id n num;
     output_string oc ")")
  | Geq (s1,s2) -> 
    (output_string oc "(>= ";
     print_smtlib oc s1 bool_id n num;
     output_string oc " ";
     print_smtlib oc s2 bool_id n num;
     output_string oc ")")
  | Add (s1,s2) -> 
    (output_string oc "(+ ";
     print_smtlib oc s1 bool_id n num;
     output_string oc " ";
     print_smtlib oc s2 bool_id n num;
     output_string oc ")")
  | Sub (s1,s2) -> 
    (output_string oc "(- ";
     print_smtlib oc s1 bool_id n num;
     output_string oc " ";
     print_smtlib oc s2 bool_id n num;
     output_string oc ")")
  | Mul (s1,s2) -> 
    (output_string oc "(* ";
     print_smtlib oc s1 bool_id n num;
     output_string oc " ";
     print_smtlib oc s2 bool_id n num;
     output_string oc ")")
  | Div (s1,s2) -> 
    (output_string oc "(/ ";
     print_smtlib oc s1 bool_id n num;
     output_string oc " ";
     print_smtlib oc s2 bool_id n num;
     output_string oc ")")
  | FV fv -> 
    if bool_id then
      output_string oc fv
    else
      output_string oc (string_of_int n)
  | Id id -> output_string oc id
  | IntPred (id1,ids) -> 
    (output_string oc ("(P" ^ string_of_int num ^ "_" ^ id1);
     List.iter
       (fun id -> 
          output_string oc (" " ^ id)) ids;
    output_string oc ")")
  | IntVarPred (num',id1,ids) -> 
    (output_string oc ("(P" ^ (string_of_int num') ^ "_" ^ id1);
     List.iter
       (fun id -> 
          output_string oc (" " ^ id)) ids;
    output_string oc ")")
  | PtrPred (id,l,i_sl,n_sl) -> 
    (output_string oc ("(P" ^ (string_of_int num) ^ "_" ^ id ^ "_" ^ (string_of_int l) ^ " ");
     print_smtlib oc i_sl bool_id n num;
     output_string oc " v ";
     print_smtlib oc n_sl bool_id n num;
     output_string oc ")")
  | PtrVarPred (num',id,be,i_sl,n_sl) -> 
    (output_string oc ("(P" ^ (string_of_int num') ^ "_" ^ id ^ "_" ^ be ^ " ");
     print_smtlib oc i_sl bool_id n num;
     output_string oc " v ";
     print_smtlib oc n_sl bool_id n num;
     output_string oc ")")
  | VarPred ->
    output_string oc "Pvar"
  | Ands sls -> 
    (output_string oc "(and";
     List.iter 
       (fun sl ->
          output_string oc " ";
          print_smtlib oc sl bool_id n num) sls;
     output_string oc ")")

let rec print_exp exp =
  match exp with
  | ELet (id,e1,e2) ->
    (print_string ("ELet(" ^ id ^ ", ");
     print_exp e1;
     print_string ", ";
     print_exp e2;
     print_string ")")
  | ELetInt (id,e1,e2) ->
    (print_string ("ELetInt(" ^ id ^ ", ");
     print_exp e1;
     print_string ", ";
     print_exp e2;
     print_string ")")
  | ELetVarPtr (id1,id2,e) ->
    (print_string ("ELetVarPtr(" ^ id1 ^ ", ");
     print_string id2;
     print_string ", ";
     print_exp e;
     print_string ")")
  | ELetDerefPtr (id1,id2,e) ->
    (print_string ("ELetDerefPtr(" ^ id1 ^ ", ");
     print_string id2;
     print_string ", ";
     print_exp e;
     print_string ")")
  | ELetAddPtr (id1,id2,i,e) ->
    (print_string ("ELetAddPtr(" ^ id1 ^ ", ");
     print_string id2;
     print_string ", ";
     print_int i;
     print_string ", ";
     print_exp e;
     print_string ")")
  | EIf (e1,e2,e3) ->
    (print_string "EIf(";
     print_exp e1;
     print_string ", "; 
     print_exp e2;
     print_string ", ";
     print_exp e3;
     print_string ")")
  | EMkarray (id,i,e) ->
    (print_string ("EMkarray(" ^ id ^ ", ");
     print_int i;
     print_string ", ";
     print_exp e;
     print_string ")")
  | EAssign (id1,e1,e2) ->
    (print_string ("EAssign(" ^ id1 ^ ", ");
     print_exp e1;
     print_string ", ";
     print_exp e2;
     print_string ")")
  | EAssignInt (id,e1,e2) ->
    (print_string ("EAssignInt(" ^ id ^ ", ");
     print_exp e1;
     print_string ", ";
     print_exp e2;
     print_string ")")
  | EAssignPtr (id1,id2,e) ->
    (print_string ("EAssignPtr(" ^ id1 ^ ", ");
     print_string id2;
     print_string ", ";
     print_exp e;
     print_string ")")
  | EAlias (e1,e2,e3) ->
    (print_string "EAlias(";
     print_exp e1;
     print_string ", "; 
     print_exp e2;
     print_string ", ";
     print_exp e3;
     print_string ")")
  | EAliasVarPtr (id1,id2,e) ->
    (print_string ("EAliasVarPtr(" ^ id1 ^ ", ");
     print_string id2;
     print_string ", ";
     print_exp e;
     print_string ")")
  | EAliasDerefPtr (id1,id2,e) ->
    (print_string ("EAliasDerefPtr(" ^ id1 ^ ", ");
     print_string id2;
     print_string ", ";
     print_exp e;
     print_string ")")
  | EAliasAddPtr (id1,id2,i,e) ->
    (print_string ("EAliasAddPtr(" ^ id1 ^ ", ");
     print_string id2;
     print_string ", ";
     print_int i;
     print_string ", ";
     print_exp e;
     print_string ")")
  | EAssert (e1,e2) ->
    (print_string "EAssert(";
     print_exp e1;
     print_string ", ";
     print_exp e2;
     print_string ")")
  | ESeq (e1,e2) ->
    (print_string "ESeq(";
     print_exp e1;
     print_string ", ";
     print_exp e2;
     print_string ")")
  | EDeref id ->
    print_string ("EDeref(" ^ id ^ ")")
  | EApp (id,es) ->
    (print_string ("EApp(" ^ id ^ ", ");
     print_exps es;
     print_string ")") 
  | EEq (e1,e2) ->
    (print_string "EEq(";
     print_exp e1;
     print_string ", ";
     print_exp e2;
     print_string ")")
  | ELt (e1, e2) ->
    (print_string "ELt(";
     print_exp e1;
     print_string ", ";
     print_exp e2;
     print_string ")")
  | EGt (e1, e2) ->
    (print_string "EGt(";
     print_exp e1;
     print_string ", ";
     print_exp e2;
     print_string ")")
  | ELeq (e1, e2) ->
    (print_string "ELeq(";
     print_exp e1;
     print_string ", ";
     print_exp e2;
     print_string ")")
  | EGeq (e1, e2) ->
    (print_string "EGeq(";
     print_exp e1;
     print_string ", ";
     print_exp e2;
     print_string ")")
  | ENeq (e1, e2) ->
    (print_string "ENeq(";
     print_exp e1;
     print_string ", ";
     print_exp e2;
     print_string ")")
  | EAnd (e1,e2) ->
    (print_string "EAnd(";
     print_exp e1;
     print_string ", ";
     print_exp e2;
     print_string ")")
  | EOr (e1,e2) ->
    (print_string "EOr(";
     print_exp e1;
     print_string ", ";
     print_exp e2;
     print_string ")")
  | ENot e ->
    (print_string "ENot(";
     print_exp e;
     print_string ")")
  | EAdd (e1,e2) -> 
    (print_string "EAdd(";
     print_exp e1;
     print_string ", ";
     print_exp e2;
     print_string ")")
  | ESub (e1,e2) -> 
    (print_string "ESub(";
     print_exp e1;
     print_string ", ";
     print_exp e2;
     print_string ")")
  | EMul (e1,e2) -> 
    (print_string "EMul(";
     print_exp e1;
     print_string ", ";
     print_exp e2;
     print_string ")")
  | EDiv (e1,e2) -> 
    (print_string "EDiv(";
     print_exp e1;
     print_string ", ";
     print_exp e2;
     print_string ")")
  | EConstUnit -> 
    print_string "()"
  | EConstFail ->
    print_string "fail"
  | EConstInt i ->
    print_int i
  | EConstTrue ->
    print_string "true"
  | EConstFalse ->
    print_string "false"
  | EVar x -> 
    print_string x
and print_exps es =
  match es with
  | [] -> ()
  | e :: [] -> print_exp e
  | e :: es' -> print_exp e; print_string ", "; print_exps es'

let rec print_ftype ft = 
  match ft with
  | FTInt sl -> 
    (print_string "FTInt(";
     print_smtlib stdout sl true 0 0;
     print_string ")");
  | FTRef (ft',e1,e2,f) ->
    (print_string "FTRef(";
     print_ftype ft';
     print_string ", ";
     print_exp e1;
     print_string ", ";
     print_exp e2;
     print_string ", ";
     print_float f;
     print_string ")")

let print_ftype_id ftid =
  match ftid with
  | RawId id -> print_string id
  | HashId id -> print_string ("#" ^ id)

let rec print_ftid_ftypes ftid_fts = 
  match ftid_fts with
  | [] -> ()
  | (ftid,ft) :: [] -> 
    print_ftype_id ftid; print_string ": "; print_ftype ft
  | (ftid,ft) :: ftid_fts' -> 
    print_ftype_id ftid; print_string ": "; print_ftype ft; 
    print_string ", "; print_ftid_ftypes ftid_fts'

let print_annotation (ftid_fts1,ftid_fts2,ft) =
  print_string "[ ";
  print_ftid_ftypes ftid_fts1;
  print_string " -> ";
  print_ftid_ftypes ftid_fts2;
  print_string " | ";
  print_ftype ft;
  print_string " ]"

let print_fdef (id,ids,ann,e) = 
  print_string (id ^ "(");
  print_ids ids;
  print_string ") ";
  print_annotation ann;
  print_string " { ";
  print_exp e;
  print_string " }"

let rec print_fdefs fdefs = 
  match fdefs with
  | [] -> ()
  | fdef :: [] -> print_fdef fdef
  | fdef :: fdefs' -> print_fdef fdef; print_string ", "; print_fdefs fdefs'

let print_program (fdefs,e) =
  print_fdefs fdefs;
  print_string " { ";
  print_exp e;
  print_string " }"


let rec print_constraint c = 
  match c with
  | CIf (e,cs1,cs2,l) -> 
    (print_string "CIf(";
     print_exp e;
     print_string ", ";
     print_constraints cs1;
     print_string ", ";
     print_constraints cs2;
     print_string " | ";
     print_int l;
     print_string ")")
  | CLet (id1,id2,l) -> 
    (print_string ("CLet(" ^ id1 ^ ", ");
     print_string id2;
     print_string " | ";
     print_int l;
     print_string ")")
  | CLetDeref (id1,id2,l) -> 
    (print_string ("CLetDeref(" ^ id1 ^ ", ");
     print_string id2;
     print_string " | ";
     print_int l;
     print_string ")")
  | CLetAddPtr (id1,id2,i,l) -> 
    (print_string ("CLetAddPtr(" ^ id1 ^ ", ");
     print_string id2;
     print_string ", ";
     print_int i;
     print_string " | "; 
     print_int l;
     print_string ")")
  | CMkArray (id,i,l) -> 
    (print_string ("CMkArray(" ^ id ^ ", ");
     print_int i;
     print_string " | ";
     print_int l;
     print_string ")")
  | CAssignInt (id,l) -> 
    (print_string ("CAssignInt(" ^ id ^ " | ");
     print_int l;
     print_string ")")
  | CAssignRef (id1,id2,l) -> 
    (print_string ("CAssignRef(" ^ id1 ^ ", ");
     print_string id2;
     print_string " | ";
     print_int l;
     print_string ")")
  | CAlias (id1,id2,l) -> 
    (print_string ("CAlias(" ^ id1 ^ ", ");
     print_string id2;
     print_string " | ";
     print_int l;
     print_string ")")
  | CAliasDeref (id1,id2,l) -> 
    (print_string ("CAliasDeref(" ^ id1 ^ ", ");
     print_string id2;
     print_string " | ";
     print_int l;
     print_string ")")
  | CAliasAddPtr (id1,id2,i,l) -> 
    (print_string ("CAliasAddPtr(" ^ id1 ^ ", ");
     print_string id2;
     print_string ", ";
     print_int i;
     print_string " | ";
     print_int l;
     print_string ")")
  | CDeref (id,l) -> 
    (print_string ("CDeref(" ^ id ^ " | ");
     print_int l;
     print_string ")")
  | CApp (id,args,l) -> 
    (print_string ("CApp(" ^ id ^ ", ");
     print_args args;
     print_string " | ";
     print_int l;
     print_string ")")
and print_arg arg = 
  match arg with
  | AExp e -> print_exp e
  | AId id -> print_string id
and print_args args = 
  match args with
  | [] -> ()
  | arg :: [] -> print_arg arg
  | arg :: args' -> print_arg arg; print_string ", "; print_args args'
and print_constraints cs =
  print_string "{ ";
  print_constraints_sub cs;
  print_string "}"
and print_constraints_sub cs =
  match cs with
  | [] -> ()
  | c :: [] -> print_constraint c; print_string " "
  | c :: cs' -> print_constraint c; print_string ", "; print_constraints_sub cs'

let rec print_all_constraints all_cs =
  print_string "[ ";
  print_all_constraints_sub all_cs;
  print_string "]"
and print_all_constraints_sub all_cs =
  match all_cs with
  | [] -> ()
  | (id,cs) :: [] -> print_string (id ^ ": "); print_constraints cs; print_string " "
  | (id,cs) :: all_cs' -> print_string (id ^ ": "); print_constraints cs; print_string ", "; print_all_constraints_sub all_cs'

let rec list_to_set li res = 
  match li with
  | [] -> res
  | [x] -> if List.mem x res then res else x :: res
  | x :: li' ->
    let res' = list_to_set li' res in
    if List.mem x res' then res' else x :: res' 

let rec print_smtlibs oc sls bool_id fvs num =
  if bool_id then
    (
      (* List.iter
      (fun fv -> 
        output_string oc "(declare-fun ";
        output_string oc fv;
        output_string oc " () Int)\n"
        ) fvs; *)
     output_string oc "\n";
     List.iter (print_smtlibs_sub oc num) sls)
    (* (List.iter 
      (fun sl -> 
        output_string oc "(assert (forall ";
        output_string oc (make_args fvs);
        print_smtlib oc sl true 0; 
        output_string oc "))\n"
        ) sls;
    output_string oc "\n") *)
  else 
    (List.iter 
      (fun sl -> 
        output_string oc "(assert ";
        print_smtlib oc sl false (-3) num; 
        output_string oc ")\n"
        ) sls;
    output_string oc "\n";
    List.iter 
      (fun sl -> 
        output_string oc "(assert ";
        print_smtlib oc sl false (-2) num; 
        output_string oc ")\n"
        ) sls;
    output_string oc "\n";
    List.iter 
      (fun sl -> 
        output_string oc "(assert ";
        print_smtlib oc sl false (-1) num; 
        output_string oc ")\n"
        ) sls;
    output_string oc "\n";
    List.iter 
      (fun sl -> 
        output_string oc "(assert ";
        print_smtlib oc sl false 0 num; 
        output_string oc ")\n"
        ) sls;
    output_string oc "\n";
    List.iter 
      (fun sl -> 
        output_string oc "(assert ";
        print_smtlib oc sl false 1 num; 
        output_string oc ")\n"
        ) sls;
    output_string oc "\n";
    List.iter 
      (fun sl -> 
        output_string oc "(assert ";
        print_smtlib oc sl false 2 num; 
        output_string oc ")\n"
        ) sls;
    output_string oc "\n";
    List.iter 
      (fun sl -> 
        output_string oc "(assert ";
        print_smtlib oc sl false 3 num; 
        output_string oc ")\n"
        ) sls)
and print_smtlibs_sub oc num sl = 
  let fvs = list_to_set (fvs_of_smtlib sl) [] in
  if fvs = [] then
    (output_string oc "(assert ";
     print_smtlib oc sl true 0 num; 
     output_string oc ")\n")
  else 
    (output_string oc "(assert (forall (";
     output_string oc (make_args fvs);
     output_string oc ") ";
     print_smtlib oc sl true 0 num; 
     output_string oc "))\n")
and make_args fvs = 
  match fvs with
  | [] -> ""
  | fv :: [] -> "(" ^ fv ^ " Int)" 
  | fv :: fvs' -> "(" ^ fv ^ " Int) " ^ (make_args fvs')
and fvs_of_smtlib sl =
  match sl with 
  | Or (s1,s2) -> 
    (fvs_of_smtlib s1) @ (fvs_of_smtlib s2)
  | And (s1,s2) -> 
    (fvs_of_smtlib s1) @ (fvs_of_smtlib s2)
  | Imply (s1,s2) -> 
    (fvs_of_smtlib s1) @ (fvs_of_smtlib s2)
  | Not s -> 
    fvs_of_smtlib s
  | Eq (s1,s2) -> 
    (fvs_of_smtlib s1) @ (fvs_of_smtlib s2)
  | Lt (s1,s2) -> 
    (fvs_of_smtlib s1) @ (fvs_of_smtlib s2)
  | Gt (s1,s2) -> 
    (fvs_of_smtlib s1) @ (fvs_of_smtlib s2)
  | Leq (s1,s2) -> 
    (fvs_of_smtlib s1) @ (fvs_of_smtlib s2)
  | Geq (s1,s2) -> 
    (fvs_of_smtlib s1) @ (fvs_of_smtlib s2)
  | Add (s1,s2) -> 
    (fvs_of_smtlib s1) @ (fvs_of_smtlib s2)
  | Sub (s1,s2) -> 
    (fvs_of_smtlib s1) @ (fvs_of_smtlib s2)
  | Mul (s1,s2) -> 
    (fvs_of_smtlib s1) @ (fvs_of_smtlib s2)
  | Div (s1,s2) -> 
    (fvs_of_smtlib s1) @ (fvs_of_smtlib s2)
  | FV fv -> 
    [fv]
  | Id id -> 
    []
  | IntPred (id1,ids) ->
    ids
  | IntVarPred (num,id1,ids) ->
    ids
  | PtrPred (id,l,s1,s2) ->
    "v" :: (fvs_of_smtlib s1) @ (fvs_of_smtlib s2) (**)
  | PtrVarPred (num,id1,id2,s1,s2) ->
    "v" :: (fvs_of_smtlib s1) @ (fvs_of_smtlib s2) (**)
  | VarPred ->
    []
  | Ands ss ->
    List.concat (List.map fvs_of_smtlib ss)

let rec print_declare oc id_count fvs =
  (List.iter
    (fun (id,i) ->
       output_string oc ("(declare-fun o_" ^ id ^ "_");
       output_string oc (string_of_int i);
       output_string oc " () Real)\n";
       print_declare_c oc fvs "l_" id i;
       output_string oc ("(declare-fun d_l_" ^ id ^ "_");
       output_string oc (string_of_int i);
       output_string oc " () Int)\n";
       print_declare_c oc fvs "h_" id i;
       output_string oc ("(declare-fun d_h_" ^ id ^ "_");
       output_string oc (string_of_int i);
       output_string oc " () Int)\n"
       ) id_count);
and print_declare_c oc fvs lh id i =
  List.iter
    (fun fv ->
       output_string oc ("(declare-fun c_" ^ lh ^ fv ^ "_" ^ id ^ "_");
       output_string oc (string_of_int i);
       output_string oc " () Int)\n"
       ) fvs

let print_declare_chc oc id_count varpred_count num =
  (List.iter
    (fun (id,i) ->
       try 
         let fvs = List.assoc id !intpred_env in
         output_string oc ("(declare-fun P" ^ string_of_int num ^ "_" ^ id ^ " ( Int ");
         List.iter (fun _ -> output_string oc "Int ") fvs;
         output_string oc (") Bool)\n")
       with Not_found -> 
         output_string oc ("(declare-fun P" ^ string_of_int num ^ "_" ^ id ^ "_");
         output_string oc (string_of_int i);
         output_string oc " ( Int Int Int ) Bool)\n"
       ) id_count);
   (List.iter
     (fun sl ->
        match sl with
        | IntVarPred(num',id,_) -> 
          if num' = num then 
            (output_string oc ("(declare-fun P" ^ string_of_int num ^ "_" ^ id);
            output_string oc " ( Int ) Bool)\n")
          else ()
        | PtrVarPred(num',id,be,_,_) -> 
          if num' = num then 
            (output_string oc ("(declare-fun P" ^ string_of_int num ^ "_" ^ id ^ "_" ^ be);
            output_string oc " ( Int Int Int ) Bool)\n")
          else ()
         ) (list_to_set (List.map fst varpred_count) []))

(* let print_declare_chc_int oc int_fvs num =
  (List.iter
    (fun id ->
       output_string oc ("(declare-fun P" ^ string_of_int num ^ "_" ^ id);
       output_string oc " ( Int ) Bool)\n"
       ) int_fvs) *)

let rec print_chc c = 
  match c with
  | CHCIf (e,cs1,cs2,l) -> 
    (print_string "CHCIf(";
     print_exp e;
     print_string ", ";
     print_chcs cs1;
     print_string ", ";
     print_chcs cs2;
     print_string " | ";
     print_int l;
     print_string ")")
  | CHCLetInt (id,e,l) -> 
    (print_string ("CHCLetInt(" ^ id ^ ", ");
     print_exp e;
     print_string " | ";
     print_int l;
     print_string ")")
  | CHCLet (id1,id2,l) -> 
    (print_string ("CHCLet(" ^ id1 ^ ", ");
     print_string id2;
     print_string " | ";
     print_int l;
     print_string ")")
  | CHCLetDeref (id1,id2,l) -> 
    (print_string ("CHCLetDeref(" ^ id1 ^ ", ");
     print_string id2;
     print_string " | ";
     print_int l;
     print_string ")")
  | CHCLetAddPtr (id1,id2,i,l) -> 
    (print_string ("CHCLetAddPtr(" ^ id1 ^ ", ");
     print_string id2;
     print_string ", ";
     print_int i;
     print_string " | "; 
     print_int l;
     print_string ")")
  | CHCMkArray (id,i,l) -> 
    (print_string ("CHCMkArray(" ^ id ^ ", ");
     print_int i;
     print_string " | ";
     print_int l;
     print_string ")")
  | CHCAssignInt (id,e,l) -> 
    (print_string ("CHCAssignInt(" ^ id ^ ", ");
     print_exp e;
     print_string " | ";
     print_int l;
     print_string ")")
  | CHCAssignRef (id1,id2,l) -> 
    (print_string ("CHCAssignRef(" ^ id1 ^ ", ");
     print_string id2;
     print_string " | ";
     print_int l;
     print_string ")")
  | CHCAlias (id1,id2,l) -> 
    (print_string ("CHCAlias(" ^ id1 ^ ", ");
     print_string id2;
     print_string " | ";
     print_int l;
     print_string ")")
  | CHCAliasDeref (id1,id2,l) -> 
    (print_string ("CHCAliasDeref(" ^ id1 ^ ", ");
     print_string id2;
     print_string " | ";
     print_int l;
     print_string ")")
  | CHCAliasAddPtr (id1,id2,i,l) -> 
    (print_string ("CHCAliasAddPtr(" ^ id1 ^ ", ");
     print_string id2;
     print_string ", ";
     print_int i;
     print_string " | ";
     print_int l;
     print_string ")")
  | CHCAssert (e,l) ->
    (print_string ("CHCAssert(");
     print_exp e;
     print_string " | ";
     print_int l;
     print_string ")")
  | CHCApp (id,es,l) -> 
    (print_string ("CHCApp(" ^ id ^ ", ");
     print_exps es;
     print_string " | ";
     print_int l;
     print_string ")")
and print_chcs cs =
  print_string "{ ";
  print_chcs_sub cs;
  print_string "}"
and print_chcs_sub cs =
  match cs with
  | [] -> ()
  | c :: [] -> print_chc c; print_string " "
  | c :: cs' -> print_chc c; print_string ", "; print_chcs_sub cs'

let rec print_all_chcs all_cs =
  print_string "[ ";
  print_all_chcs_sub all_cs;
  print_string "]"
and print_all_chcs_sub all_cs =
  match all_cs with
  | [] -> ()
  | (id,cs,_) :: [] -> print_string (id ^ ": "); print_chcs cs; print_string " "
  | (id,cs,_) :: all_cs' -> print_string (id ^ ": "); print_chcs cs; print_string ", "; print_all_chcs_sub all_cs'