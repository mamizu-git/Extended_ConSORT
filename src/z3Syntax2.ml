(** Module for handling the model outputtted by Z3 in the form of ownership function *)

exception Z3Syntax2Error

type id = string

type pos = string

type value =
  | Int   of int
  | Float of float

(** Type to represent the ownership fumction of the form \[c_l * x + d_l, c_h * y +d_h \] |-> o *)
type ownership = 
  | Own   of int * id * pos * value
  | CHigh of int * id * id * pos * value
  | CLow  of int * id * id * pos * value
  | DHigh of int * id * pos * value
  | DLow  of int * id * pos * value

type result = ownership list

let rec print_ownerships oc ownerships = 
  List.iter (print_ownership oc) ownerships
and print_ownership oc ownership = 
  match ownership with
  | Own (num,id1,id2,Float f) ->
    (output_string oc ("Own" ^ (string_of_int num) ^ " of ");
     output_string oc (id1 ^ "_" ^ id2 ^ ": ");
     output_string oc (string_of_float f);
     output_string oc "\n")
  | CHigh (num,id1,id2,id3,Int i) ->
    (output_string oc ("C" ^ (string_of_int num) ^ "High of ");
     output_string oc (id1 ^ "_" ^ id2 ^ "_" ^ id3 ^ ": ");
     output_string oc (string_of_int i);
     output_string oc "\n")
  | CLow (num,id1,id2,id3,Int i) ->
    (output_string oc ("C" ^ (string_of_int num) ^ "Low of ");
     output_string oc (id1 ^ "_" ^ id2 ^ "_" ^ id3 ^ ": ");
     output_string oc (string_of_int i);
     output_string oc "\n")
  | DHigh (num,id1,id2,Int i) ->
    (output_string oc ("D" ^ (string_of_int num) ^ "High of ");
     output_string oc (id1 ^ "_" ^ id2 ^ ": ");
     output_string oc (string_of_int i);
     output_string oc "\n")
  | DLow (num,id1,id2,Int i) ->
    (output_string oc ("D" ^ (string_of_int num) ^ "Low of ");
     output_string oc (id1 ^ "_" ^ id2 ^ ": ");
     output_string oc (string_of_int i);
     output_string oc "\n")
  | _ -> raise Z3Syntax2Error
