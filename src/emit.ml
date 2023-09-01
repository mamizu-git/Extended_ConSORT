open Syntax
open CollectConstraint
open TySyntax
open SimpleTyping
open Elim

let id_count = ref []

let rec lookup_ifel id ifel env =
  match env with
  | [] -> raise Unbound
  | (x, (l, lst)) :: nenv -> if id = x && ifel = lst then l else lookup_ifel id ifel nenv

let new_id id l ifel =
  try
    let i = lookup_ifel id ifel !id_count in
    if i = l then ()
    else
      id_count := (id, (l, ifel)) :: !id_count
  with 
    Unbound -> id_count := (id, (l, ifel)) :: !id_count

let rec lookup_pre_ifel id ifel env = 
  match env with
  | [] -> raise Unbound
  | (x, _) :: nenv -> if id = x then lookup_ifel id ifel nenv else lookup_pre_ifel id ifel nenv

let o id n ifel = 
  Id("o_" ^ (string_of_int n) ^ "_" ^ id ^ "_" ^ (string_of_int (lookup_ifel id ifel !id_count)) ^ ifel_to_str ifel)

let rec lo fvs id n ifel = 
  match fvs with
  | [] -> Id("d_" ^ (string_of_int n) ^ "_l_" ^ id ^ "_" ^ (string_of_int (lookup_ifel id ifel !id_count)) ^ ifel_to_str ifel)
  | fv :: fvs' ->
    Add(Mul(Id("c_" ^ (string_of_int n) ^ "_l_" ^ fv ^ "_" ^ id ^ "_" ^ (string_of_int (lookup_ifel id ifel !id_count)) ^ ifel_to_str ifel), FV(fv)),
        lo fvs' id n ifel)

let rec hi fvs id n ifel = 
  match fvs with
  | [] -> Id("d_" ^ (string_of_int n) ^ "_h_" ^ id ^ "_" ^ (string_of_int (lookup_ifel id ifel !id_count)) ^ ifel_to_str ifel)
  | fv :: fvs' ->
    Add(Mul(Id("c_" ^ (string_of_int n) ^ "_h_" ^ fv ^ "_" ^ id ^ "_" ^ (string_of_int (lookup_ifel id ifel !id_count)) ^ ifel_to_str ifel), FV(fv)),
        hi fvs' id n ifel)

let o_p id n ifel = 
  Id("o_" ^ (string_of_int n) ^ "_" ^ id ^ "_" ^ (string_of_int (lookup_pre_ifel id ifel !id_count)) ^ ifel_to_str ifel)

let rec lo_p fvs id n ifel = 
  match fvs with
  | [] -> Id("d_" ^ (string_of_int n) ^ "_l_" ^ id ^ "_" ^ (string_of_int (lookup_pre_ifel id ifel !id_count)) ^ ifel_to_str ifel)
  | fv :: fvs' ->
    Add(Mul(Id("c_" ^ (string_of_int n) ^ "_l_" ^ fv ^ "_" ^ id ^ "_" ^ (string_of_int (lookup_pre_ifel id ifel !id_count)) ^ ifel_to_str ifel), FV(fv)),
        lo_p fvs' id n ifel)

let rec hi_p fvs id n ifel = 
  match fvs with
  | [] -> Id("d_" ^ (string_of_int n) ^ "_h_" ^ id ^ "_" ^ (string_of_int (lookup_pre_ifel id ifel !id_count)) ^ ifel_to_str ifel)
  | fv :: fvs' ->
    Add(Mul(Id("c_" ^ (string_of_int n) ^ "_h_" ^ fv ^ "_" ^ id ^ "_" ^ (string_of_int (lookup_pre_ifel id ifel !id_count)) ^ ifel_to_str ifel), FV(fv)),
        hi_p fvs' id n ifel)

let o_be id n be = 
  Id("o_" ^ (string_of_int n) ^ "_" ^ id ^ "_" ^ be)

let rec lo_be fvs id n be = 
  match fvs with
  | [] -> Id("d_" ^ (string_of_int n) ^ "_l_" ^ id ^ "_" ^ be)
  | fv :: fvs' ->
    Add(Mul(Id("c_" ^ (string_of_int n) ^ "_l_" ^ fv ^ "_" ^ id ^ "_" ^ be), FV(fv)),
        lo_be fvs' id n be)

let rec hi_be fvs id n be = 
  match fvs with
  | [] -> Id("d_" ^ (string_of_int n) ^ "_h_" ^ id ^ "_" ^ be)
  | fv :: fvs' ->
    Add(Mul(Id("c_" ^ (string_of_int n) ^ "_h_" ^ fv ^ "_" ^ id ^ "_" ^ be), FV(fv)),
        hi_be fvs' id n be)

let varown_count = ref []

let rec find_id_count ifel id_count res = 
  match id_count with
  | [] -> res
  | (x, (_,lst)) :: id_count' -> 
    if List.mem x res || ifel <> lst then 
      find_id_count ifel id_count' res 
    else 
      find_id_count ifel id_count' (x :: res)
 
let rec union_list ls1 ls2 = 
  match ls1 with
  | [] -> ls2
  | x :: ls1' -> if List.mem x ls2 then union_list ls1' ls2 else union_list ls1' (x :: ls2)

let rec constr_to_smtlib fvs n fun_num ifel c =
  match c with
  | CIf (e,cs1,cs2,l) -> 
    let ids_pre = find_id_count ifel !id_count [] in 
    List.iter (fun id -> new_id id l ("if" :: ifel); new_id id l ("el" :: ifel)) ids_pre;
    let ss_pre = 
      List.concat (List.map 
        (fun id -> 
          [Eq(o id n ifel, o id n ("if" :: ifel));
           Eq(o id n ifel, o id n ("el" :: ifel));
           Eq(lo fvs id n ifel, lo fvs id n ("if" :: ifel));
           Eq(lo fvs id n ifel, lo fvs id n ("el" :: ifel));
           Eq(hi fvs id n ifel, hi fvs id n ("if" :: ifel));
           Eq(hi fvs id n ifel, hi fvs id n ("el" :: ifel))]
        ) ids_pre) in
    let ss1 = List.concat (List.map (constr_to_smtlib fvs n fun_num ("if" :: ifel)) cs1) in
    let ss1' = List.map (fun s -> Imply(exp_to_smtlib e, s)) ss1 in
    let ss2 = List.concat (List.map (constr_to_smtlib fvs n fun_num ("el" :: ifel)) cs2) in
    let ss2' = List.map (fun s -> Imply(Not(exp_to_smtlib e), s)) ss2 in
    let ids_post_if = find_id_count ("if" :: ifel) !id_count [] in
    let ids_post_el = find_id_count ("el" :: ifel) !id_count [] in
    let ids_post = union_list ids_post_if ids_post_el in
    List.iter (fun id -> new_id id (l+1) ifel) ids_post; (**)
    let ss_post_if = 
      List.map 
        (fun s -> Imply(exp_to_smtlib e, s))
        (List.concat (List.map 
          (fun id -> 
            [Or(Eq(o id n ifel, Id "0."),
             And(Leq(o id n ifel, o id n ("if" :: ifel)),
             And(Geq(lo fvs id n ifel, lo fvs id n ("if" :: ifel)),
                 Leq(hi fvs id n ifel, hi fvs id n ("if" :: ifel)))))]
          ) ids_post_if)) in
    let ss_post_el = 
      List.map 
        (fun s -> Imply(Not(exp_to_smtlib e), s))
        (List.concat (List.map 
          (fun id -> 
            [Or(Eq(o id n ifel, Id "0."),
             And(Leq(o id n ifel, o id n ("el" :: ifel)),
             And(Geq(lo fvs id n ifel, lo fvs id n ("el" :: ifel)),
                 Leq(hi fvs id n ifel, hi fvs id n ("el" :: ifel)))))]
          ) ids_post_el)) in
    ss_pre @ ss1' @ ss2' @ ss_post_if @ ss_post_el
  | CLet (id1,id2,l) -> 
    new_id id1 l ifel; new_id id2 l ifel;
    [Or(Geq(o_p id2 n ifel, Add(o id1 n ifel, o id2 n ifel)),
     Or(Gt(lo fvs id1 n ifel, hi fvs id2 n ifel), 
        Gt(lo fvs id2 n ifel, hi fvs id1 n ifel)));
     Geq(o_p id2 n ifel, o id1 n ifel);
     Geq(o_p id2 n ifel, o id2 n ifel);
     Leq(lo_p fvs id2 n ifel, lo fvs id1 n ifel);
     Leq(lo_p fvs id2 n ifel, lo fvs id2 n ifel);
     Geq(hi_p fvs id2 n ifel, hi fvs id1 n ifel);
     Geq(hi_p fvs id2 n ifel, hi fvs id2 n ifel);
     Leq(lo fvs id1 n ifel, hi fvs id1 n ifel);
     Leq(lo fvs id2 n ifel, hi fvs id2 n ifel)]
  (* | CLetDeref (id1,id2,l) -> 
    (print_string ("CLetDeref(" ^ id1 ^ ", ");
     print_string id2;
     print_string " | ";
     print_int l;
     print_string ")") *)
  | CLetAddPtr (id1,id2,e,l) -> 
    new_id id1 l ifel; new_id id2 l ifel;
    (* let lh = if fvs = [] then [Leq(lo fvs id1 n ifel, hi fvs id1 n ifel); Leq(lo fvs id2 n ifel, hi fvs id2 n ifel)] else [] in  *)
    let sl = exp_to_smtlib e in
    [Or(Geq(o_p id2 n ifel, Add(o id1 n ifel, o id2 n ifel)),
     Or(Gt(Add(lo fvs id1 n ifel, sl), hi fvs id2 n ifel), 
        Gt(lo fvs id2 n ifel, Add(hi fvs id1 n ifel, sl))));
     Geq(o_p id2 n ifel, o id1 n ifel);
     Geq(o_p id2 n ifel, o id2 n ifel);
     Leq(lo_p fvs id2 n ifel, Add(lo fvs id1 n ifel, sl));
     Leq(lo_p fvs id2 n ifel, lo fvs id2 n ifel);
     Geq(hi_p fvs id2 n ifel, Add(hi fvs id1 n ifel, sl));
     Geq(hi_p fvs id2 n ifel, hi fvs id2 n ifel)]
     (* @ [Leq(lo fvs id1 n ifel, hi fvs id1 n ifel); Leq(lo fvs id2 n ifel, hi fvs id2 n ifel)]  *)
  | CLetSubPtr (id1,id2,e,l) -> 
    new_id id1 l ifel; new_id id2 l ifel;
    (* let lh = if fvs = [] then [Leq(lo fvs id1 n ifel, hi fvs id1 n ifel); Leq(lo fvs id2 n ifel, hi fvs id2 n ifel)] else [] in  *)
    let sl = exp_to_smtlib e in
    [Or(Geq(o_p id2 n ifel, Add(o id1 n ifel, o id2 n ifel)),
     Or(Gt(Sub(lo fvs id1 n ifel, sl), hi fvs id2 n ifel), 
        Gt(lo fvs id2 n ifel, Sub(hi fvs id1 n ifel, sl))));
     Geq(o_p id2 n ifel, o id1 n ifel);
     Geq(o_p id2 n ifel, o id2 n ifel);
     Leq(lo_p fvs id2 n ifel, Sub(lo fvs id1 n ifel, sl));
     Leq(lo_p fvs id2 n ifel, lo fvs id2 n ifel);
     Geq(hi_p fvs id2 n ifel, Sub(hi fvs id1 n ifel, sl));
     Geq(hi_p fvs id2 n ifel, hi fvs id2 n ifel)]
     (* @ [Leq(lo fvs id1 n ifel, hi fvs id1 n ifel); Leq(lo fvs id2 n ifel, hi fvs id2 n ifel)]  *)
  | CMkArray (id,i,l) -> 
    new_id id l ifel;
    [Eq(o id n ifel, Id "1"); 
     Eq(lo fvs id n ifel, Id "0"); 
     Eq(hi fvs id n ifel, Id (string_of_int (i-1)))]
  | CAssignInt (id,l) -> 
    [Eq(o id n ifel, Id "1");
     Leq(lo fvs id n ifel, Id "0"); 
     Geq(hi fvs id n ifel, Id "0")]
  (* | CAssignRef (id1,id2,l) -> 
    (print_string ("CAssignRef(" ^ id1 ^ ", ");
     print_string id2;
     print_string " | ";
     print_int l;
     print_string ")") *)
  | CAlias (id1,id2,l) -> 
    new_id id1 l ifel; new_id id2 l ifel;
    [Or(And(Eq(Add(o_p id1 n ifel, o_p id2 n ifel), Add(o id1 n ifel, o id2 n ifel)),
        And(Eq(lo_p fvs id1 n ifel, lo_p fvs id2 n ifel),
        And(Eq(lo_p fvs id1 n ifel, lo fvs id1 n ifel),
        And(Eq(lo_p fvs id2 n ifel, lo fvs id2 n ifel),
        And(Eq(hi_p fvs id1 n ifel, hi_p fvs id2 n ifel),
        And(Eq(hi_p fvs id1 n ifel, hi fvs id1 n ifel),
            Eq(hi_p fvs id2 n ifel, hi fvs id2 n ifel))))))),
     Or(And(Eq(Add(o_p id1 n ifel, o_p id2 n ifel), o id1 n ifel),
        And(Eq(Add(o_p id1 n ifel, o_p id2 n ifel), o id2 n ifel),
        And(Eq(lo_p fvs id1 n ifel, lo_p fvs id2 n ifel),
        And(Eq(hi_p fvs id1 n ifel, hi_p fvs id2 n ifel),
            Or(And(Eq(lo_p fvs id1 n ifel, lo fvs id1 n ifel), 
               And(Eq(hi_p fvs id2 n ifel, hi fvs id2 n ifel),
                   Eq(Add(hi fvs id1 n ifel, Id "1"), lo fvs id2 n ifel))),
               And(Eq(lo_p fvs id1 n ifel, lo fvs id2 n ifel), 
               And(Eq(hi_p fvs id2 n ifel, hi fvs id1 n ifel),
                   Eq(Add(hi fvs id2 n ifel, Id "1"), lo fvs id1 n ifel)))))))),
     Or(And(Eq(o_p id1 n ifel, Add(o id1 n ifel, o id2 n ifel)),
        And(Eq(o_p id2 n ifel, Add(o id1 n ifel, o id2 n ifel)),
        And(Eq(lo fvs id1 n ifel, lo fvs id2 n ifel),
        And(Eq(hi fvs id1 n ifel, hi fvs id2 n ifel),
            Or(And(Eq(lo_p fvs id1 n ifel, lo fvs id1 n ifel), 
               And(Eq(hi_p fvs id2 n ifel, hi fvs id2 n ifel),
                   Eq(Add(hi_p fvs id1 n ifel, Id "1"), lo_p fvs id2 n ifel))),
               And(Eq(lo_p fvs id2 n ifel, lo fvs id1 n ifel), 
               And(Eq(hi_p fvs id1 n ifel, hi fvs id2 n ifel),
                   Eq(Add(hi_p fvs id2 n ifel, Id "1"), lo_p fvs id1 n ifel)))))))),
        And(Eq(o_p id1 n ifel, o id1 n ifel),
        And(Eq(o_p id2 n ifel, o id2 n ifel),
        And(Eq(o id1 n ifel, o id2 n ifel),
            Or(And(Eq(lo_p fvs id1 n ifel, lo fvs id1 n ifel), 
               And(Eq(hi_p fvs id2 n ifel, hi fvs id2 n ifel),
               And(Eq(Add(hi_p fvs id1 n ifel, Id "1"), lo_p fvs id2 n ifel),
                   Eq(Add(hi fvs id1 n ifel, Id "1"), lo fvs id2 n ifel)))),
            Or(And(Eq(lo_p fvs id1 n ifel, lo fvs id2 n ifel), 
               And(Eq(hi_p fvs id2 n ifel, hi fvs id1 n ifel),
               And(Eq(Add(hi_p fvs id1 n ifel, Id "1"), lo_p fvs id2 n ifel),
                   Eq(Add(hi fvs id2 n ifel, Id "1"), lo fvs id1 n ifel)))),
            Or(And(Eq(lo_p fvs id2 n ifel, lo fvs id1 n ifel), 
               And(Eq(hi_p fvs id1 n ifel, hi fvs id2 n ifel),
               And(Eq(Add(hi_p fvs id2 n ifel, Id "1"), lo_p fvs id1 n ifel),
                   Eq(Add(hi fvs id1 n ifel, Id "1"), lo fvs id2 n ifel)))),
               And(Eq(lo_p fvs id2 n ifel, lo fvs id2 n ifel), 
               And(Eq(hi_p fvs id1 n ifel, hi fvs id1 n ifel),
               And(Eq(Add(hi_p fvs id2 n ifel, Id "1"), lo_p fvs id1 n ifel),
                   Eq(Add(hi fvs id2 n ifel, Id "1"), lo fvs id1 n ifel)))))))))))));
     Leq(lo fvs id1 n ifel, hi fvs id1 n ifel);
     Leq(lo fvs id2 n ifel, hi fvs id2 n ifel)]
  (* | CAliasDeref (id1,id2,l) -> 
    (print_string ("CAliasDeref(" ^ id1 ^ ", ");
     print_string id2;
     print_string " | ";
     print_int l;
     print_string ")") *)
  | CAliasAddPtr (id1,id2,e,l) -> 
    new_id id1 l ifel; new_id id2 l ifel;
    let sl = exp_to_smtlib e in
    (* let lh = if fvs = [] then [Leq(lo fvs id1 n ifel, hi fvs id1 n ifel); Leq(lo fvs id2 n ifel, hi fvs id2 n ifel)] else [] in *)
    [Or(And(Eq(Add(o_p id1 n ifel, o_p id2 n ifel), Add(o id1 n ifel, o id2 n ifel)),
        And(Eq(Add(lo_p fvs id1 n ifel, sl), lo_p fvs id2 n ifel),
        And(Eq(Add(lo_p fvs id1 n ifel, sl), Add(lo fvs id1 n ifel, sl)),
        And(Eq(lo_p fvs id2 n ifel, lo fvs id2 n ifel),
        And(Eq(Add(hi_p fvs id1 n ifel, sl), hi_p fvs id2 n ifel),
        And(Eq(Add(hi_p fvs id1 n ifel, sl), Add(hi fvs id1 n ifel, sl)),
            Eq(hi_p fvs id2 n ifel, hi fvs id2 n ifel))))))),
     Or(And(Eq(Add(o_p id1 n ifel, o_p id2 n ifel), o id1 n ifel),
        And(Eq(Add(o_p id1 n ifel, o_p id2 n ifel), o id2 n ifel),
        And(Eq(Add(lo_p fvs id1 n ifel, sl), lo_p fvs id2 n ifel),
        And(Eq(Add(hi_p fvs id1 n ifel, sl), hi_p fvs id2 n ifel),
            Or(And(Eq(Add(lo_p fvs id1 n ifel, sl), Add(lo fvs id1 n ifel, sl)), 
               And(Eq(hi_p fvs id2 n ifel, hi fvs id2 n ifel),
                   Eq(Add(Add(hi fvs id1 n ifel, sl), Id "1"), lo fvs id2 n ifel))),
               And(Eq(Add(lo_p fvs id1 n ifel, sl), lo fvs id2 n ifel), 
               And(Eq(hi_p fvs id2 n ifel, Add(hi fvs id1 n ifel, sl)),
                   Eq(Add(hi fvs id2 n ifel, Id "1"), Add(lo fvs id1 n ifel, sl))))))))),
     Or(And(Eq(o_p id1 n ifel, Add(o id1 n ifel, o id2 n ifel)),
        And(Eq(o_p id2 n ifel, Add(o id1 n ifel, o id2 n ifel)),
        And(Eq(Add(lo fvs id1 n ifel, sl), lo fvs id2 n ifel),
        And(Eq(Add(hi fvs id1 n ifel, sl), hi fvs id2 n ifel),
            Or(And(Eq(Add(lo_p fvs id1 n ifel, sl), Add(lo fvs id1 n ifel, sl)), 
               And(Eq(hi_p fvs id2 n ifel, hi fvs id2 n ifel),
                   Eq(Add(Add(hi_p fvs id1 n ifel, sl), Id "1"), lo_p fvs id2 n ifel))),
               And(Eq(lo_p fvs id2 n ifel, Add(lo fvs id1 n ifel, sl)), 
               And(Eq(Add(hi_p fvs id1 n ifel, sl), hi fvs id2 n ifel),
                   Eq(Add(hi_p fvs id2 n ifel, Id "1"), Add(lo_p fvs id1 n ifel, sl))))))))),
        And(Eq(o_p id1 n ifel, o id1 n ifel),
        And(Eq(o_p id2 n ifel, o id2 n ifel),
        And(Eq(o id1 n ifel, o id2 n ifel),
            Or(And(Eq(Add(lo_p fvs id1 n ifel, sl), Add(lo fvs id1 n ifel, sl)), 
               And(Eq(hi_p fvs id2 n ifel, hi fvs id2 n ifel),
               And(Eq(Add(Add(hi_p fvs id1 n ifel, sl), Id "1"), lo_p fvs id2 n ifel),
                   Eq(Add(Add(hi fvs id1 n ifel, sl), Id "1"), lo fvs id2 n ifel)))),
            Or(And(Eq(Add(lo_p fvs id1 n ifel, sl), lo fvs id2 n ifel), 
               And(Eq(hi_p fvs id2 n ifel, Add(hi fvs id1 n ifel, sl)),
               And(Eq(Add(Add(hi_p fvs id1 n ifel, sl), Id "1"), lo_p fvs id2 n ifel),
                   Eq(Add(hi fvs id2 n ifel, Id "1"), Add(lo fvs id1 n ifel, sl))))),
            Or(And(Eq(lo_p fvs id2 n ifel, Add(lo fvs id1 n ifel, sl)), 
               And(Eq(Add(hi_p fvs id1 n ifel, sl), hi fvs id2 n ifel),
               And(Eq(Add(hi_p fvs id2 n ifel, Id "1"), Add(lo_p fvs id1 n ifel, sl)),
                   Eq(Add(Add(hi fvs id1 n ifel, sl), Id "1"), lo fvs id2 n ifel)))),
               And(Eq(lo_p fvs id2 n ifel, lo fvs id2 n ifel), 
               And(Eq(Add(hi_p fvs id1 n ifel, sl), Add(hi fvs id1 n ifel, sl)),
               And(Eq(Add(hi_p fvs id2 n ifel, Id "1"), Add(lo_p fvs id1 n ifel, sl)),
                   Eq(Add(hi fvs id2 n ifel, Id "1"), Add(lo fvs id1 n ifel, sl))))))))))))))]
     @ [Leq(lo fvs id1 n ifel, hi fvs id1 n ifel); Leq(lo fvs id2 n ifel, hi fvs id2 n ifel)]
  | CDeref (id,l) -> 
    [Gt(o id n ifel, Id "0");
     Leq(lo fvs id n ifel, Id "0"); 
     Geq(hi fvs id n ifel, Id "0")]
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
      | (RawId id_ptr, FTRef (_,ENull,ENull,_)), AId id ->
        let num = lookup id_fn fun_num in
        (* varown_count := (id_ptr, "b", num) :: !varown_count; *)
        let fvs' = union_list (List.map fst subst) fvs in
        let sll = lo_be fvs' id_ptr num "b" in
        let slh = hi_be fvs' id_ptr num "b" in
        [Or(Eq(Id "0.", o_be id_ptr num "b"), (* needless? *)
         And(Geq(o id n ifel, o_be id_ptr num "b"),
         And(Leq(lo fvs id n ifel, smtlib_subst subst sll),
             Geq(hi fvs id n ifel, smtlib_subst subst slh))))]
         (* @ [Leq(lo fvs id n ifel, hi fvs id n ifel)]  *)
      | (RawId _, FTRef (_,el,eh,f)), AId id -> 
        let l_arg_exp = exp_subst subst el in
        let h_arg_exp = exp_subst subst eh in
        [Or(Eq(Id "0.", Id (string_of_float f)),
         And(Geq(o id n ifel, Id (string_of_float f)),
         And(Leq(lo fvs id n ifel, exp_to_smtlib l_arg_exp),
             Geq(hi fvs id n ifel, exp_to_smtlib h_arg_exp))))]
         (* @ [Leq(lo fvs id n ifel, hi fvs id n ifel)]  *)
      | _, AExp e -> []
      | _ -> raise ConstrError
    in
    let ss1 = List.concat (List.map2 g1 ftid_fts1 args) in
    let g2 ftid_ft arg = 
      match ftid_ft, arg with
      | (RawId id_ptr, FTRef (_,ENull,ENull,_)), AId id ->
        let num = lookup id_fn fun_num in
        (* varown_count := (id_ptr, "e", num) :: !varown_count; *)
        let fvs' = union_list (List.map fst subst) fvs in
        let sll = lo_be fvs' id_ptr num "e" in
        let slh = hi_be fvs' id_ptr num "e" in
        new_id id l ifel;
        [Eq(o id n ifel, o_be id_ptr num "e");
         Eq(lo fvs id n ifel, smtlib_subst subst sll);
         Eq(hi fvs id n ifel, smtlib_subst subst slh)]
         (* @ [Leq(lo fvs id n ifel, hi fvs id n ifel)]  *)
      | (RawId _, FTRef (_,el,eh,f)), AId id -> 
        let l_arg_exp = exp_subst subst el in
        let h_arg_exp = exp_subst subst eh in
        new_id id l ifel;
        [Eq(o id n ifel, Id (string_of_float f));
         Eq(lo fvs id n ifel, exp_to_smtlib l_arg_exp);
         Eq(hi fvs id n ifel, exp_to_smtlib h_arg_exp)]
         (* @ [Leq(lo fvs id n ifel, hi fvs id n ifel)]  *)
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

let ics_to_smtlib ics n fun_num =
  let (id, cs) = ics in
  let (ftid_fts1, ftid_fts2) = lookup id !fn_env in
  let fvs = List.concat (List.map find_fv ftid_fts1) in
  let ref_ids = List.concat (List.map find_ref_id ftid_fts1) in
  id_count := List.map (fun id -> (id, (1, []))) ref_ids;
  varown_count := [];
  let g1 id = 
    let (el1,eh1,f1) = assoc_ft id ftid_fts1 in 
    match el1 with
    | ENull ->
      varown_count := (id, "b", n) :: !varown_count;
      [Eq(o id n [], o_be id n "b");
       Eq(lo fvs id n [], lo_be fvs id n "b");
       Eq(hi fvs id n [], hi_be fvs id n "b")]
    | _ ->
      [Eq(o id n [], Id (string_of_float f1));
       Eq(lo fvs id n [], exp_to_smtlib el1);
       Eq(hi fvs id n [], exp_to_smtlib eh1)]
  in
  let s1 = List.concat (List.map g1 ref_ids) in
  let ss = List.concat (List.map (constr_to_smtlib fvs n fun_num []) cs) in
  let g2 id = 
    let (el2,eh2,f2) = assoc_ft id ftid_fts2 in 
    match el2 with
    | ENull ->
      varown_count := (id, "e", n) :: !varown_count;
      [Or(Eq(o_be id n "e", Id "0."),
       And(Leq(o_be id n "e", o id n []),
       And(Geq(lo_be fvs id n "e", lo fvs id n []),
           Leq(hi_be fvs id n "e", hi fvs id n []))))]
    | _ ->
      [Or(Eq(Id (string_of_float f2), Id "0."),
       And(Leq(Id (string_of_float f2), o id n []),
       And(Geq(exp_to_smtlib el2, lo fvs id n []),
           Leq(exp_to_smtlib eh2, hi fvs id n []))))]
  in
  let s2 = List.concat (List.map g2 ref_ids) in
  let g_lh (id, (i,ifel)) =
    let o_id = Id("o_" ^ (string_of_int n) ^ "_" ^ id ^ "_" ^ (string_of_int i) ^ (ifel_to_str ifel)) in
    (* let rec lh_id fvs lh id i ifel = 
      (match fvs with
      | [] -> Id("d_" ^ (string_of_int n) ^ "_" ^ lh ^ id ^ "_" ^ (string_of_int i) ^ (ifel_to_str ifel))
      | fv :: fvs' ->
        Add(Mul(Id("c_" ^ (string_of_int n) ^ "_" ^ lh ^ fv ^ "_" ^ id ^ "_" ^ (string_of_int i) ^ (ifel_to_str ifel)), FV(fv)),
            lh_id fvs' lh id i ifel))
    in
    let lo_id = lh_id fvs "l_" id i ifel in
    let hi_id = lh_id fvs "h_" id i ifel in *)
    [Geq(o_id, Id "0.");
     (* Leq(lo_id, hi_id);  *)
     Leq(o_id, Id "1.")]
     (* Imply(Eq(o_id, Id "0."), Eq(lo_id, Id "0"));
     Imply(Eq(o_id, Id "0."), Eq(hi_id, Id "0"))] *)
  in
  let s_olh = List.concat (List.map g_lh !id_count) in (**)
  (s_olh @ s1 @ ss @ s2, !id_count, !varown_count, fvs)

let rec fun_number all_cs cnt res =
  match all_cs with
  | [] -> res
  | ics :: all_cs' -> 
    let (id,_) = ics in
    fun_number all_cs' (cnt+1) ((id, cnt) :: res)

let all_cs_to_smtlib all_cs n =
  (* List.concat (List.map ics_to_smtlib all_cs) *)
  let fun_num = fun_number all_cs 0 [] in
  let (ss, id_count, varown_count, fvs) = ics_to_smtlib (List.nth all_cs n) n fun_num in
  (* print_declare id_count fvs; *)
  (id_count, varown_count, fvs, ss)
  
    