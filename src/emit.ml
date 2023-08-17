open Syntax
open CollectConstraint
open TySyntax
open SimpleTyping
open Elim

let id_count = ref []

let new_id id l =
  try
    let i = lookup id !id_count in
    if i = l then ()
    else
      id_count := (id, l) :: !id_count
  with 
    Unbound -> id_count := (id, l) :: !id_count

let rec lookup_pre id env = 
  match env with
  | [] -> raise Unbound
  | (x, _) :: nenv -> if id = x then lookup id nenv else lookup_pre id nenv

let o id n = 
  Id("o_" ^ (string_of_int n) ^ "_" ^ id ^ "_" ^ (string_of_int (lookup id !id_count)))

let rec lo fvs id n = 
  match fvs with
  | [] -> Id("d_" ^ (string_of_int n) ^ "_l_" ^ id ^ "_" ^ (string_of_int (lookup id !id_count)))
  | fv :: fvs' ->
    Add(Mul(Id("c_" ^ (string_of_int n) ^ "_l_" ^ fv ^ "_" ^ id ^ "_" ^ (string_of_int (lookup id !id_count))), FV(fv)),
        lo fvs' id n)

let rec hi fvs id n = 
  match fvs with
  | [] -> Id("d_" ^ (string_of_int n) ^ "_h_" ^ id ^ "_" ^ (string_of_int (lookup id !id_count)))
  | fv :: fvs' ->
    Add(Mul(Id("c_" ^ (string_of_int n) ^ "_h_" ^ fv ^ "_" ^ id ^ "_" ^ (string_of_int (lookup id !id_count))), FV(fv)),
        hi fvs' id n)

let o_p id n = 
  Id("o_" ^ (string_of_int n) ^ "_" ^ id ^ "_" ^ (string_of_int (lookup_pre id !id_count)))

let rec lo_p fvs id n = 
  match fvs with
  | [] -> Id("d_" ^ (string_of_int n) ^ "_l_" ^ id ^ "_" ^ (string_of_int (lookup_pre id !id_count)))
  | fv :: fvs' ->
    Add(Mul(Id("c_" ^ (string_of_int n) ^ "_l_" ^ fv ^ "_" ^ id ^ "_" ^ (string_of_int (lookup_pre id !id_count))), FV(fv)),
        lo_p fvs' id n)

let rec hi_p fvs id n = 
  match fvs with
  | [] -> Id("d_" ^ (string_of_int n) ^ "_h_" ^ id ^ "_" ^ (string_of_int (lookup_pre id !id_count)))
  | fv :: fvs' ->
    Add(Mul(Id("c_" ^ (string_of_int n) ^ "_h_" ^ fv ^ "_" ^ id ^ "_" ^ (string_of_int (lookup_pre id !id_count))), FV(fv)),
        hi_p fvs' id n)


let rec constr_to_smtlib fvs n c =
  match c with
  | CIf (e,cs1,cs2,l) -> 
    let ss1 = List.concat (List.map (constr_to_smtlib fvs n) cs1) in
    let ss1' = List.map (fun s -> Imply(exp_to_smtlib e, s)) ss1 in
    let ss2 = List.concat (List.map (constr_to_smtlib fvs n) cs2) in
    let ss2' = List.map (fun s -> Imply(Not(exp_to_smtlib e), s)) ss2 in
    ss1' @ ss2'
  | CLet (id1,id2,l) -> 
    new_id id1 l; new_id id2 l;
    [Or(Geq(o_p id2 n, Add(o id1 n, o id2 n)),
     Or(Gt(lo fvs id1 n, hi fvs id2 n), 
        Gt(lo fvs id2 n, hi fvs id1 n)));
     Geq(o_p id2 n, o id1 n);
     Geq(o_p id2 n, o id2 n);
     Leq(lo_p fvs id2 n, lo fvs id1 n);
     Leq(lo_p fvs id2 n, lo fvs id2 n);
     Geq(hi_p fvs id2 n, hi fvs id1 n);
     Geq(hi_p fvs id2 n, hi fvs id2 n);
     Leq(lo fvs id1 n, hi fvs id1 n);
     Leq(lo fvs id2 n, hi fvs id2 n)]
  (* | CLetDeref (id1,id2,l) -> 
    (print_string ("CLetDeref(" ^ id1 ^ ", ");
     print_string id2;
     print_string " | ";
     print_int l;
     print_string ")") *)
  | CLetAddPtr (id1,id2,i,l) -> 
    new_id id1 l; new_id id2 l;
    (* let lh = if fvs = [] then [Leq(lo fvs id1 n, hi fvs id1 n); Leq(lo fvs id2 n, hi fvs id2 n)] else [] in  *)
    [Or(Geq(o_p id2 n, Add(o id1 n, o id2 n)),
     Or(Gt(Add(lo fvs id1 n, Id (string_of_int i)), hi fvs id2 n), 
        Gt(lo fvs id2 n, Add(hi fvs id1 n, Id (string_of_int i)))));
     Geq(o_p id2 n, o id1 n);
     Geq(o_p id2 n, o id2 n);
     Leq(lo_p fvs id2 n, Add(lo fvs id1 n, Id (string_of_int i)));
     Leq(lo_p fvs id2 n, lo fvs id2 n);
     Geq(hi_p fvs id2 n, Add(hi fvs id1 n, Id (string_of_int i)));
     Geq(hi_p fvs id2 n, hi fvs id2 n)]
     @ [Leq(lo fvs id1 n, Add(hi fvs id1 n, Id "1")); Leq(lo fvs id2 n, Add(hi fvs id2 n, Id "1"))] (**)
  | CMkArray (id,i,l) -> 
    new_id id l;
    [Eq(o id n, Id "1"); 
     Eq(lo fvs id n, Id "0"); 
     Eq(hi fvs id n, Id (string_of_int (i-1)))]
  | CAssignInt (id,l) -> 
    [Eq(o id n, Id "1");
     Leq(lo fvs id n, Id "0"); 
     Geq(hi fvs id n, Id "0")]
  (* | CAssignRef (id1,id2,l) -> 
    (print_string ("CAssignRef(" ^ id1 ^ ", ");
     print_string id2;
     print_string " | ";
     print_int l;
     print_string ")") *)
  | CAlias (id1,id2,l) -> 
    new_id id1 l; new_id id2 l;
    [Or(And(Eq(Add(o_p id1 n, o_p id2 n), Add(o id1 n, o id2 n)),
        And(Eq(lo_p fvs id1 n, lo_p fvs id2 n),
        And(Eq(lo_p fvs id1 n, lo fvs id1 n),
        And(Eq(lo_p fvs id2 n, lo fvs id2 n),
        And(Eq(hi_p fvs id1 n, hi_p fvs id2 n),
        And(Eq(hi_p fvs id1 n, hi fvs id1 n),
            Eq(hi_p fvs id2 n, hi fvs id2 n))))))),
     Or(And(Eq(Add(o_p id1 n, o_p id2 n), o id1 n),
        And(Eq(Add(o_p id1 n, o_p id2 n), o id2 n),
        And(Eq(lo_p fvs id1 n, lo_p fvs id2 n),
        And(Eq(hi_p fvs id1 n, hi_p fvs id2 n),
            Or(And(Eq(lo_p fvs id1 n, lo fvs id1 n), 
               And(Eq(hi_p fvs id2 n, hi fvs id2 n),
                   Eq(Add(hi fvs id1 n, Id "1"), lo fvs id2 n))),
               And(Eq(lo_p fvs id1 n, lo fvs id2 n), 
               And(Eq(hi_p fvs id2 n, hi fvs id1 n),
                   Eq(Add(hi fvs id2 n, Id "1"), lo fvs id1 n)))))))),
     Or(And(Eq(o_p id1 n, Add(o id1 n, o id2 n)),
        And(Eq(o_p id2 n, Add(o id1 n, o id2 n)),
        And(Eq(lo fvs id1 n, lo fvs id2 n),
        And(Eq(hi fvs id1 n, hi fvs id2 n),
            Or(And(Eq(lo_p fvs id1 n, lo fvs id1 n), 
               And(Eq(hi_p fvs id2 n, hi fvs id2 n),
                   Eq(Add(hi_p fvs id1 n, Id "1"), lo_p fvs id2 n))),
               And(Eq(lo_p fvs id2 n, lo fvs id1 n), 
               And(Eq(hi_p fvs id1 n, hi fvs id2 n),
                   Eq(Add(hi_p fvs id2 n, Id "1"), lo_p fvs id1 n)))))))),
        And(Eq(o_p id1 n, o id1 n),
        And(Eq(o_p id2 n, o id2 n),
        And(Eq(o id1 n, o id2 n),
            Or(And(Eq(lo_p fvs id1 n, lo fvs id1 n), 
               And(Eq(hi_p fvs id2 n, hi fvs id2 n),
               And(Eq(Add(hi_p fvs id1 n, Id "1"), lo_p fvs id2 n),
                   Eq(Add(hi fvs id1 n, Id "1"), lo fvs id2 n)))),
            Or(And(Eq(lo_p fvs id1 n, lo fvs id2 n), 
               And(Eq(hi_p fvs id2 n, hi fvs id1 n),
               And(Eq(Add(hi_p fvs id1 n, Id "1"), lo_p fvs id2 n),
                   Eq(Add(hi fvs id2 n, Id "1"), lo fvs id1 n)))),
            Or(And(Eq(lo_p fvs id2 n, lo fvs id1 n), 
               And(Eq(hi_p fvs id1 n, hi fvs id2 n),
               And(Eq(Add(hi_p fvs id2 n, Id "1"), lo_p fvs id1 n),
                   Eq(Add(hi fvs id1 n, Id "1"), lo fvs id2 n)))),
               And(Eq(lo_p fvs id2 n, lo fvs id2 n), 
               And(Eq(hi_p fvs id1 n, hi fvs id1 n),
               And(Eq(Add(hi_p fvs id2 n, Id "1"), lo_p fvs id1 n),
                   Eq(Add(hi fvs id2 n, Id "1"), lo fvs id1 n)))))))))))));
     Leq(lo fvs id1 n, hi fvs id1 n);
     Leq(lo fvs id2 n, hi fvs id2 n)]
  (* | CAliasDeref (id1,id2,l) -> 
    (print_string ("CAliasDeref(" ^ id1 ^ ", ");
     print_string id2;
     print_string " | ";
     print_int l;
     print_string ")") *)
  | CAliasAddPtr (id1,id2,i,l) -> 
    new_id id1 l; new_id id2 l;
    (* let lh = if fvs = [] then [Leq(lo fvs id1 n, hi fvs id1 n); Leq(lo fvs id2 n, hi fvs id2 n)] else [] in *)
    [Or(And(Eq(Add(o_p id1 n, o_p id2 n), Add(o id1 n, o id2 n)),
        And(Eq(Add(lo_p fvs id1 n, Id (string_of_int i)), lo_p fvs id2 n),
        And(Eq(Add(lo_p fvs id1 n, Id (string_of_int i)), Add(lo fvs id1 n, Id (string_of_int i))),
        And(Eq(lo_p fvs id2 n, lo fvs id2 n),
        And(Eq(Add(hi_p fvs id1 n, Id (string_of_int i)), hi_p fvs id2 n),
        And(Eq(Add(hi_p fvs id1 n, Id (string_of_int i)), Add(hi fvs id1 n, Id (string_of_int i))),
            Eq(hi_p fvs id2 n, hi fvs id2 n))))))),
     Or(And(Eq(Add(o_p id1 n, o_p id2 n), o id1 n),
        And(Eq(Add(o_p id1 n, o_p id2 n), o id2 n),
        And(Eq(Add(lo_p fvs id1 n, Id (string_of_int i)), lo_p fvs id2 n),
        And(Eq(Add(hi_p fvs id1 n, Id (string_of_int i)), hi_p fvs id2 n),
            Or(And(Eq(Add(lo_p fvs id1 n, Id (string_of_int i)), Add(lo fvs id1 n, Id (string_of_int i))), 
               And(Eq(hi_p fvs id2 n, hi fvs id2 n),
                   Eq(Add(Add(hi fvs id1 n, Id (string_of_int i)), Id "1"), lo fvs id2 n))),
               And(Eq(Add(lo_p fvs id1 n, Id (string_of_int i)), lo fvs id2 n), 
               And(Eq(hi_p fvs id2 n, Add(hi fvs id1 n, Id (string_of_int i))),
                   Eq(Add(hi fvs id2 n, Id "1"), Add(lo fvs id1 n, Id (string_of_int i)))))))))),
     Or(And(Eq(o_p id1 n, Add(o id1 n, o id2 n)),
        And(Eq(o_p id2 n, Add(o id1 n, o id2 n)),
        And(Eq(Add(lo fvs id1 n, Id (string_of_int i)), lo fvs id2 n),
        And(Eq(Add(hi fvs id1 n, Id (string_of_int i)), hi fvs id2 n),
            Or(And(Eq(Add(lo_p fvs id1 n, Id (string_of_int i)), Add(lo fvs id1 n, Id (string_of_int i))), 
               And(Eq(hi_p fvs id2 n, hi fvs id2 n),
                   Eq(Add(Add(hi_p fvs id1 n, Id (string_of_int i)), Id "1"), lo_p fvs id2 n))),
               And(Eq(lo_p fvs id2 n, Add(lo fvs id1 n, Id (string_of_int i))), 
               And(Eq(Add(hi_p fvs id1 n, Id (string_of_int i)), hi fvs id2 n),
                   Eq(Add(hi_p fvs id2 n, Id "1"), Add(lo_p fvs id1 n, Id (string_of_int i)))))))))),
        And(Eq(o_p id1 n, o id1 n),
        And(Eq(o_p id2 n, o id2 n),
        And(Eq(o id1 n, o id2 n),
            Or(And(Eq(Add(lo_p fvs id1 n, Id (string_of_int i)), Add(lo fvs id1 n, Id (string_of_int i))), 
               And(Eq(hi_p fvs id2 n, hi fvs id2 n),
               And(Eq(Add(Add(hi_p fvs id1 n, Id (string_of_int i)), Id "1"), lo_p fvs id2 n),
                   Eq(Add(Add(hi fvs id1 n, Id (string_of_int i)), Id "1"), lo fvs id2 n)))),
            Or(And(Eq(Add(lo_p fvs id1 n, Id (string_of_int i)), lo fvs id2 n), 
               And(Eq(hi_p fvs id2 n, Add(hi fvs id1 n, Id (string_of_int i))),
               And(Eq(Add(Add(hi_p fvs id1 n, Id (string_of_int i)), Id "1"), lo_p fvs id2 n),
                   Eq(Add(hi fvs id2 n, Id "1"), Add(lo fvs id1 n, Id (string_of_int i)))))),
            Or(And(Eq(lo_p fvs id2 n, Add(lo fvs id1 n, Id (string_of_int i))), 
               And(Eq(Add(hi_p fvs id1 n, Id (string_of_int i)), hi fvs id2 n),
               And(Eq(Add(hi_p fvs id2 n, Id "1"), Add(lo_p fvs id1 n, Id (string_of_int i))),
                   Eq(Add(Add(hi fvs id1 n, Id (string_of_int i)), Id "1"), lo fvs id2 n)))),
               And(Eq(lo_p fvs id2 n, lo fvs id2 n), 
               And(Eq(Add(hi_p fvs id1 n, Id (string_of_int i)), Add(hi fvs id1 n, Id (string_of_int i))),
               And(Eq(Add(hi_p fvs id2 n, Id "1"), Add(lo_p fvs id1 n, Id (string_of_int i))),
                   Eq(Add(hi fvs id2 n, Id "1"), Add(lo fvs id1 n, Id (string_of_int i)))))))))))))))]
     @ [Leq(lo fvs id1 n, Add(hi fvs id1 n, Id "1")); Leq(lo fvs id2 n, Add(hi fvs id2 n, Id "1"))]
  | CDeref (id,l) -> 
    [Gt(o id n, Id "0");
     Leq(lo fvs id n, Id "0"); 
     Geq(hi fvs id n, Id "0")]
  | CApp (id_fn,args,l) -> 
    let find_subst ftid_ft arg = 
      match ftid_ft, arg with
      | (RawId _, FTInt _), AExp e -> []
      | (HashId id, FTInt _), AExp e -> [(id, e)]
      | (_, FTRef _), AId id -> []
      | _ -> raise ConstrError
    in
    let (ftid_fts1, ftid_fts2) = lookup id_fn !fn_env in
    let subst = List.concat (List.map2 find_subst ftid_fts1 args) in
    let g1 ftid_ft arg = 
      match ftid_ft, arg with
      | (RawId _, FTRef (_,el,eh,f)), AId id -> 
        let l_arg_exp = exp_subst subst el in
        let h_arg_exp = exp_subst subst eh in
        [Geq(o id n, Id (string_of_float f));
         Leq(lo fvs id n, exp_to_smtlib l_arg_exp);
         Geq(hi fvs id n, exp_to_smtlib h_arg_exp)]
      | _, AExp e -> []
      | _ -> raise ConstrError
    in
    let ss1 = List.concat (List.map2 g1 ftid_fts1 args) in
    let g2 ftid_ft arg = 
      match ftid_ft, arg with
      | (RawId _, FTRef (_,el,eh,f)), AId id -> 
        let l_arg_exp = exp_subst subst el in
        let h_arg_exp = exp_subst subst eh in
        new_id id l;
        [Eq(o id n, Id (string_of_float f));
         Eq(lo fvs id n, exp_to_smtlib l_arg_exp);
         Eq(hi fvs id n, exp_to_smtlib h_arg_exp)]
      | _, AExp e -> []
      | _ -> raise ConstrError
    in
    let ss2 = List.concat (List.map2 g2 ftid_fts2 args) in
    ss1 @ ss2
    (* ss1 *)

let find_fv ftid_ft = 
  match ftid_ft with
  | (HashId id, _) -> [id]
  | _ -> []
    
let find_ref_id ftid_ft = 
  match ftid_ft with
  | (RawId id, FTRef _) -> [id]
  | _ -> [] 

let rec assoc_ft id ftid_fts = 
  match ftid_fts with
  | (RawId id_ft, FTRef (_,el,eh,f)) :: ftid_fts' when id_ft = id -> (el,eh,f)
  | _ :: ftid_fts' -> assoc_ft id ftid_fts'
  | [] -> raise Not_found

let ics_to_smtlib ics n =
  let (id, cs) = ics in
  let (ftid_fts1, ftid_fts2) = lookup id !fn_env in
  let fvs = List.concat (List.map find_fv ftid_fts1) in
  let ref_ids = List.concat (List.map find_ref_id ftid_fts1) in
  id_count := List.map (fun id -> (id, 1)) ref_ids;
  let g1 id = 
    let (el1,eh1,f1) = assoc_ft id ftid_fts1 in 
    [Eq(o id n, Id (string_of_float f1));
     Eq(lo fvs id n, exp_to_smtlib el1);
     Eq(hi fvs id n, exp_to_smtlib eh1)]
  in
  let s1 = List.concat (List.map g1 ref_ids) in
  let ss = List.concat (List.map (constr_to_smtlib fvs n) cs) in
  let g2 id = 
    let (el2,eh2,f2) = assoc_ft id ftid_fts2 in 
    [Geq(o id n, Id (string_of_float f2));
     Leq(lo fvs id n, exp_to_smtlib el2);
     Geq(hi fvs id n, exp_to_smtlib eh2)]
  in
  let s2 = List.concat (List.map g2 ref_ids) in
  let g_lh (id, i) =
    let o_id = Id("o_" ^ (string_of_int n) ^ "_" ^ id ^ "_" ^ (string_of_int i)) in
    (* let rec lh_id fvs lh id i = 
      (match fvs with
      | [] -> Id("d_" ^ lh ^ id ^ "_" ^ (string_of_int i))
      | fv :: fvs' ->
        Add(Mul(Id("c_" ^ lh ^ fv ^ "_" ^ id ^ "_" ^ (string_of_int i)), FV(fv)),
            lh_id fvs' lh id i))
    in
    let lo_id = lh_id fvs "l_" id i in
    let hi_id = lh_id fvs "h_" id i in *)
    [Geq(o_id, Id "0.");
     (* Leq(lo_id, hi_id);  *)
     Leq(o_id, Id "1.")]
  in
  let s_olh = List.concat (List.map g_lh !id_count) in
  (s_olh @ s1 @ ss @ s2, !id_count, fvs)

let all_cs_to_smtlib all_cs n =
  (* List.concat (List.map ics_to_smtlib all_cs) *)
  let (ss, id_count, fvs) = ics_to_smtlib (List.nth all_cs n) n in
  (* print_declare id_count fvs; *)
  (id_count, fvs, ss)
  
    