{
	open Z3Parser2
	let next_line = Lexing.new_line
}

let int = '-'? ['0'-'9']+

let float = '-'?['0'-'9']+ '.' ['0' - '9']*

let white = [' ' '\t']+
let newline = '\n'
let id_rest = ['a'-'z' 'A'-'Z' '0'-'9' '$' ''']
let id = ['a' - 'z' 'A'-'Z'] id_rest*

rule read =
  parse
  | white    { read lexbuf }
  | newline { next_line lexbuf; read lexbuf }
  | int { let i = int_of_string @@ Lexing.lexeme lexbuf in  INT i }
  | float { let f = float_of_string @@ Lexing.lexeme lexbuf in FLOAT f }
  | "sat" { SAT }
  | "model" { MODEL }
  | "define-fun" { DEF }
  | "Real" { TREAL }
  | "Int" { TINT }
  | "o_" { O }
  | "c_" { C }
  | "d_" { D }
  | "l_" { L }
  | "h_" { H }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | '-' { MINUS }
  | '/' { DIV }
  | '_' { UNDER }
  | id { ID (Lexing.lexeme lexbuf) }
  | eof { EOF }
  | _ { failwith @@ "Invalid token " ^ (Lexing.lexeme lexbuf) }