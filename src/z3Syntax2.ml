exception Z3Syntax2Error

type id = string

type value =
  | Int   of int
  | Float of float

type ownership = 
  | Own   of id * int * value
  | CHigh of id * id * int * value
  | CLow  of id * id * int * value
  | DHigh of id * int * value
  | DLow  of id * int * value

type result = ownership list

let rec print_ownerships oc ownerships = 
  List.iter (print_ownership oc) ownerships
and print_ownership oc ownership = 
  match ownership with
  | Own (id,i,Float f) ->
    (output_string oc "Own of ";
     output_string oc (id ^ "_" ^ (string_of_int i) ^ ": ");
     output_string oc (string_of_float f);
     output_string oc "\n")
  | CHigh (id1,id2,i1,Int i2) ->
    (output_string oc "CHigh of ";
     output_string oc (id1 ^ "_" ^ id2 ^ "_" ^ (string_of_int i1) ^ ": ");
     output_string oc (string_of_int i2);
     output_string oc "\n")
  | CLow (id1,id2,i1,Int i2) ->
    (output_string oc "CLow of ";
     output_string oc (id1 ^ "_" ^ id2 ^ "_" ^ (string_of_int i1) ^ ": ");
     output_string oc (string_of_int i2);
     output_string oc "\n")
  | DHigh (id,i1,Int i2) ->
    (output_string oc "DHigh of ";
     output_string oc (id ^ "_" ^ (string_of_int i1) ^ ": ");
     output_string oc (string_of_int i2);
     output_string oc "\n")
  | DLow (id,i1,Int i2) ->
    (output_string oc "DLow of ";
     output_string oc (id ^ "_" ^ (string_of_int i1) ^ ": ");
     output_string oc (string_of_int i2);
     output_string oc "\n")
  | _ -> raise Z3Syntax2Error
    