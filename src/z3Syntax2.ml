exception Z3Syntax2Error

type id = string

type value =
  | Int   of int
  | Float of float

type ownership = 
  | Own   of int * id * int * value
  | CHigh of int * id * id * int * value
  | CLow  of int * id * id * int * value
  | DHigh of int * id * int * value
  | DLow  of int * id * int * value

type result = ownership list

let rec print_ownerships oc ownerships = 
  List.iter (print_ownership oc) ownerships
and print_ownership oc ownership = 
  match ownership with
  | Own (num,id,i,Float f) ->
    (output_string oc ("Own" ^ (string_of_int num) ^ " of ");
     output_string oc (id ^ "_" ^ (string_of_int i) ^ ": ");
     output_string oc (string_of_float f);
     output_string oc "\n")
  | CHigh (num,id1,id2,i1,Int i2) ->
    (output_string oc ("C" ^ (string_of_int num) ^ "High of ");
     output_string oc (id1 ^ "_" ^ id2 ^ "_" ^ (string_of_int i1) ^ ": ");
     output_string oc (string_of_int i2);
     output_string oc "\n")
  | CLow (num,id1,id2,i1,Int i2) ->
    (output_string oc ("C" ^ (string_of_int num) ^ "Low of ");
     output_string oc (id1 ^ "_" ^ id2 ^ "_" ^ (string_of_int i1) ^ ": ");
     output_string oc (string_of_int i2);
     output_string oc "\n")
  | DHigh (num,id,i1,Int i2) ->
    (output_string oc ("D" ^ (string_of_int num) ^ "High of ");
     output_string oc (id ^ "_" ^ (string_of_int i1) ^ ": ");
     output_string oc (string_of_int i2);
     output_string oc "\n")
  | DLow (num,id,i1,Int i2) ->
    (output_string oc ("D" ^ (string_of_int num) ^ "Low of ");
     output_string oc (id ^ "_" ^ (string_of_int i1) ^ ": ");
     output_string oc (string_of_int i2);
     output_string oc "\n")
  | _ -> raise Z3Syntax2Error
    