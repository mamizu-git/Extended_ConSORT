open Z3Syntax2
open Syntax
open Util

let rec get_id ownerships num = 
  match ownerships with
  | Own (num',id,i,Float f) :: rest when num = num' -> (id, i) :: get_id rest num
  | _ :: rest -> get_id rest num
  | [] -> []

let rec find_id (id,i) num ownerships =
  match ownerships with
  | Own (num',id1,i1,Float f) :: rest when num = num' && id = id1 && i = i1 -> Own (num',id1,i1,Float f) :: find_id (id,i) num rest
  | CHigh (num',id1,id2,i1,Int i2) :: rest when num = num' && id = id2 && i = i1 -> CHigh (num',id1,id2,i1,Int i2) :: find_id (id,i) num rest
  | CLow (num',id1,id2,i1,Int i2) :: rest when num = num' && id = id2 && i = i1 -> CLow (num',id1,id2,i1,Int i2) :: find_id (id,i) num rest
  | DHigh (num',id1,i1,Int i2) :: rest when num = num' && id = id1 && i = i1 -> DHigh (num',id1,i1,Int i2) :: find_id (id,i) num rest
  | DLow (num',id1,i1,Int i2) :: rest when num = num' && id = id1 && i = i1 -> DLow (num',id1,i1,Int i2) :: find_id (id,i) num rest
  | _ :: rest -> find_id (id,i) num rest
  | [] -> []

let rec own_to_chc (id,i) h_now l_now fvs ownerships =
  match ownerships with
  | Own (num,id1,i1,Float f) :: rest -> 
    (if f = 0. then 
      [Imply(Id "true", PtrPred(id1, i1, FV "i", fvs))]
    else
      own_to_chc (id,i) h_now l_now fvs rest)
  | CHigh (num,id1,id2,i1,Int i2) :: rest ->
    (if i2 = 0 then
      own_to_chc (id,i) h_now l_now fvs rest
    else if i2 > 0 then
      own_to_chc (id,i) (Add(h_now, Mul(FV id1, Id (string_of_int i2)))) l_now fvs rest
    else
      own_to_chc (id,i) (Add(h_now, Mul(FV id1, Id ("(- " ^ string_of_int (-i2) ^ ")")))) l_now fvs rest)
  | CLow (num,id1,id2,i1,Int i2) :: rest ->
    (if i2 = 0 then
      own_to_chc (id,i) h_now l_now fvs rest
    else if i2 > 0 then 
      own_to_chc (id,i) h_now (Add(l_now, Mul(FV id1, Id (string_of_int i2)))) fvs rest
    else 
      own_to_chc (id,i) h_now (Add(l_now, Mul(FV id1, Id ("(- " ^ string_of_int (-i2) ^ ")")))) fvs rest)
  | DHigh (num,id1,i1,Int i2) :: rest ->
    (if i2 = 0 then
      own_to_chc (id,i) h_now l_now fvs rest
    else if i2 > 0 then
      own_to_chc (id,i) (Add(h_now, Id (string_of_int i2))) l_now fvs rest
    else
      own_to_chc (id,i) (Add(h_now, Id ("(- " ^ string_of_int (-i2) ^ ")"))) l_now fvs rest)
  | DLow (num,id1,i1,Int i2) :: rest ->
    (if i2 = 0 then
      own_to_chc (id,i) h_now l_now fvs rest
    else if i2 > 0 then
      own_to_chc (id,i) h_now (Add(l_now, Id (string_of_int i2))) fvs rest
    else 
      own_to_chc (id,i) h_now (Add(l_now, Id ("(- " ^ string_of_int (-i2) ^ ")"))) fvs rest)
  | _ :: rest ->
    own_to_chc (id,i) h_now l_now fvs rest
  | [] -> 
    [Imply(Gt(Id "i", h_now), PtrPred(id, i, FV "i", fvs));
     Imply(Lt(Id "i", l_now), PtrPred(id, i, FV "i", fvs))]

let collect_ownchc ownerships num fvs = 
  let ids = get_id ownerships num in
  List.concat (List.map (fun (id,i) -> own_to_chc (id,i) (Id "0") (Id "0") fvs (find_id (id,i) num ownerships)) ids)


let g num (sl, (el,eh,f)) = 
  match sl, el with
  | _, ENull -> []
  | PtrVarPred(num',_,_,_,_), _ when num' = num ->
    if f = 0. then
      [Imply(Id "true", sl)]
    else 
      let sll = exp_to_smtlib el in
      let slh = exp_to_smtlib eh in
      [Imply(Gt(Id "i", slh), sl);
       Imply(Lt(Id "i", sll), sl)]
  | _ -> []


let ownexp_to_ownchc varpred_count num =
  List.concat (List.map (g num) (list_to_set varpred_count []))