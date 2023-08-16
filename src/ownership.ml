open Z3Syntax2
open Syntax
open Elim

let rec get_id ownerships = 
  match ownerships with
  | Own (id,i,Float f) :: rest -> (id, i) :: get_id rest
  | _ :: rest -> get_id rest
  | [] -> []

let rec find_id (id,i) ownerships =
  match ownerships with
  | Own (id1,i1,Float f) :: rest when id = id1 && i = i1 -> Own (id1,i1,Float f) :: find_id (id,i) rest
  | CHigh (id1,id2,i1,Int i2) :: rest when id = id2 && i = i1 -> CHigh (id1,id2,i1,Int i2) :: find_id (id,i) rest
  | CLow (id1,id2,i1,Int i2) :: rest when id = id2 && i = i1 -> CLow (id1,id2,i1,Int i2) :: find_id (id,i) rest
  | DHigh (id1,i1,Int i2) :: rest when id = id1 && i = i1 -> DHigh (id1,i1,Int i2) :: find_id (id,i) rest
  | DLow (id1,i1,Int i2) :: rest when id = id1 && i = i1 -> DLow (id1,i1,Int i2) :: find_id (id,i) rest
  | _ :: rest -> find_id (id,i) rest
  | [] -> []

let rec own_to_chc (id,i) h_now l_now ownerships =
  match ownerships with
  | Own (id1,i1,Float f) :: rest -> 
    (if f = 0. then 
      [Imply(Id "true", PtrPred(id1, i1, FV "i", FV "n"))]
    else
      own_to_chc (id,i) h_now l_now rest)
  | CHigh (id1,id2,i1,Int i2) :: rest ->
    (if i2 = 0 then
      own_to_chc (id,i) h_now l_now rest
    else if i2 > 0 then
      own_to_chc (id,i) (Add(h_now, Mul(FV id1, Id (string_of_int i2)))) l_now rest
    else
      own_to_chc (id,i) (Add(h_now, Mul(FV id1, Id ("(- " ^ string_of_int (-i2) ^ ")")))) l_now rest)
  | CLow (id1,id2,i1,Int i2) :: rest ->
    (if i2 = 0 then
      own_to_chc (id,i) h_now l_now rest
    else if i2 > 0 then 
      own_to_chc (id,i) h_now (Add(l_now, Mul(FV id1, Id (string_of_int i2)))) rest
    else 
      own_to_chc (id,i) h_now (Add(l_now, Mul(FV id1, Id ("(- " ^ string_of_int (-i2) ^ ")")))) rest)
  | DHigh (id1,i1,Int i2) :: rest ->
    (if i2 = 0 then
      own_to_chc (id,i) h_now l_now rest
    else if i2 > 0 then
      own_to_chc (id,i) (Add(h_now, Id (string_of_int i2))) l_now rest
    else
      own_to_chc (id,i) (Add(h_now, Id ("(- " ^ string_of_int (-i2) ^ ")"))) l_now rest)
  | DLow (id1,i1,Int i2) :: rest ->
    (if i2 = 0 then
      own_to_chc (id,i) h_now l_now rest
    else if i2 > 0 then
      own_to_chc (id,i) h_now (Add(l_now, Id (string_of_int i2))) rest
    else 
      own_to_chc (id,i) h_now (Add(l_now, Id ("(- " ^ string_of_int (-i2) ^ ")"))) rest)
  | _ :: rest ->
    own_to_chc (id,i) h_now l_now rest
  | [] -> 
    [Imply(Gt(Id "i", h_now), PtrPred(id, i, FV "i", FV "n"));
     Imply(Lt(Id "i", l_now), PtrPred(id, i, FV "i", FV "n"))]

let collect_ownchc ownerships = 
  let ids = get_id ownerships in
  List.concat (List.map (fun (id,i) -> own_to_chc (id,i) (Id "0") (Id "0") (find_id (id,i) ownerships)) ids)


let g num (sl, (el,eh,f)) = 
  match sl with
  | PtrVarPred(num',_,_,_,_) when num' = num ->
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