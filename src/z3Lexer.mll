{
	open Z3Parser
	let next_line = Lexing.new_line
}

let int = '-'? ['0'-'9']+

let float = '-'?['0'-'9']+ '.' ['0' - '9']*

let white = [' ' '\t']+
let newline = '\n'
let id_rest = ['a'-'z' 'A'-'Z' '0'-'9' '_' '$' ''']
let id = ('_' id_rest+ | ['a' - 'z' 'A'-'Z'] id_rest*)

rule read =
  parse
  | white    { read lexbuf }
  | newline { next_line lexbuf; read lexbuf }
  | int { let i = int_of_string @@ Lexing.lexeme lexbuf in (* LabelManager._internal_incr i; *) INT i }
  | float { let f = float_of_string @@ Lexing.lexeme lexbuf in FLOAT f }
  | "sat" { SAT }
  | "model" { MODEL }
  | "define-fun" { DEF }
  | "Real" { TREAL }
  | "Int" { TINT }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | '-' { MINUS }
  | '/' { DIV }
  | id { ID (Lexing.lexeme lexbuf) }
  | eof { EOF }
  | _ { failwith @@ "Invalid token " ^ (Lexing.lexeme lexbuf) }