{
	open Parser

	let next_line = Lexing.new_line
}

let int = ['0'-'9']+

let float = '-'?['0'-'9']+ '.' ['0' - '9']*

let white = [' ' '\t']+
let newline = '\n'
let id_rest = ['a'-'z' 'A'-'Z' '0'-'9' '_' '$' ''']
let id = ('_' id_rest+ | ['a' - 'z' 'A'-'Z'] id_rest*)
let non_comment = [^ '/' '*' '\n']+
let comment_delim = [ '/' '*' ]
let not_newline = [^'\n']+

rule read =
  parse
  (* | "##pos" { let (nm,pos) = pd1 lexbuf in
              Locations.set_file_name lexbuf nm pos;
              read lexbuf } *)
  | "//" { line_comment lexbuf; read lexbuf }
  | "/*" { comment lexbuf; read lexbuf }
  | "/**" { comment lexbuf; read lexbuf }
  | white    { read lexbuf }
  | newline { next_line lexbuf; read lexbuf }
  | "()" { UNIT }
  | int { let i = int_of_string @@ Lexing.lexeme lexbuf in INT i }
	| float { let f = float_of_string @@ Lexing.lexeme lexbuf in FLOAT f }
  | "if" { IF }
  | "then" { THEN }
  | "else" { ELSE }
  | "let" { LET }
  | "in" { IN }
  | ';' { SEMI }
  | ':' { COLON }
  | ',' { COMMA }
  | '[' { LBRACKET }
  | ']' { RBRACKET }
  | "mkarray" { MKARRAY }
  | "alias" { ALIAS }
  | "assert" { ASSERT }
  | "true" { TRUE }
  | "false" { FALSE }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | '{' { LBRACE }
  | '}' { RBRACE }
  | '=' { EQ }
  | '<' { LTHAN }
  | '>' { GTHAN }
  | "<=" { LEQ }
  | ">=" { GEQ }
  | "!=" { NEQ }
  | "||" { OR }
  | "&&" { AND }
  | "!" { NOT }
  | '+' { PLUS }
  | '-' { MINUS }
  | '*' { STAR }
  | '/' { DIV }
  | 'v' { NU }
	| "int" { TINT }
	| "ref" { REF }
  | "unit" { TUNIT }
  | 'T' { TOP }
  | "or" { TOR }
  | "and" { TAND }
  | "=>" { TIMPLY }
  | "not" { TNOT }
  | '#' { HASH }
  | "->" { ARROW }
	| '|' { BAR }
  | ":=" { ASSIGN }
  | '_' { UNDERSCORE }
  | id { ID (Lexing.lexeme lexbuf) }
  | eof { EOF }
  | _ { failwith @@ "Invalid token " ^ (Lexing.lexeme lexbuf) }
and comment =
  parse
  | newline { next_line lexbuf; comment lexbuf }
  | non_comment { comment lexbuf }
  | "*/" { () }
  | "/*" { comment lexbuf; comment lexbuf }
  | "/**" { comment lexbuf; comment lexbuf }
  | comment_delim { comment lexbuf }
and line_comment =
  parse
  | not_newline { line_comment lexbuf }
  | newline { next_line lexbuf }
