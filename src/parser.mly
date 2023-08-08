%{
  open Syntax
%}

// values
%token UNIT
%token <int> INT
%token <float> FLOAT
%token <string> ID
// %token NULL
%token TRUE FALSE

// conditionals
%token IF THEN ELSE // IFNULL

// control flow
%token FAIL // RETURN 

// bindings
%token LET IN EQ // MKREF

// arrays
%token MKARRAY LBRACKET RBRACKET // LARROW LENGTH

// BIFs
%token ASSERT ALIAS

// Update
%token ASSIGN

// operators
%token OR
%token AND
%token NOT
%token PLUS
%token MINUS
%token STAR
%token DIV
%token LTHAN GTHAN LEQ GEQ NEQ
// %token DOT

// connectives
%token SEMI COMMA

// structure
%token LPAREN RPAREN LBRACE RBRACE BAR EOF

%token COLON 

%token UNDERSCORE

// types
%token TOP
%token ARROW
%token NU TINT REF TUNIT TOR TAND TIMPLY TNOT
%token HASH
// %token NU AND

/* priority : low -> high */
// %right ARROW
%left OR
%left AND
%nonassoc NOT
%nonassoc EQ LTHAN GTHAN LEQ GEQ NEQ
%left PLUS MINUS
%left STAR DIV

%start program
%type <Syntax.program> program
%%

program:
| fdefs LBRACE exp RBRACE EOF 
  { ($1, $3) }
| LBRACE exp RBRACE EOF 
  { ([], $2) }
;

fdefs:
| fdef 
  { [$1] } 
| fdef fdefs 
  { $1 :: $2 }
;

fdef:
  id LPAREN ids RPAREN LBRACKET annotation RBRACKET LBRACE exp RBRACE { ($1, $3, $6, $9) }
;

ids:
| id 
  { [$1] }
| id COMMA ids 
  { $1 :: $3 }
;

annotation:
  LTHAN id_ftypes GTHAN ARROW LTHAN id_ftypes BAR ftype GTHAN { ($2, $6, $8) }
;

id_ftypes:
| id_ftype 
  { [$1] }
| id_ftype COMMA id_ftypes 
  { $1 :: $3 }
;

id_ftype:
| id COLON ftype 
  { (RawId($1), $3) }
| HASH id COLON ftype
  { (HashId($2), $4) }
;

ftype:
| LBRACE NU COLON TINT BAR smtlib RBRACE
  { FTInt($6) }
| ftype REF LPAREN exp COMMA exp COMMA float RPAREN
  { FTRef($1, $4, $6, $8) }
;

smtlib:
| LPAREN TOR smtlib smtlib RPAREN
  { Or($3, $4) }
| LPAREN TAND smtlib smtlib RPAREN
  { And($3, $4) } 
| LPAREN TIMPLY smtlib smtlib RPAREN
  { Imply($3, $4) } 
| LPAREN TNOT smtlib RPAREN
  { Not($3) } 
| LPAREN EQ smtlib smtlib RPAREN
  { Eq($3, $4) } 
| LPAREN LTHAN smtlib smtlib RPAREN
  { Lt($3, $4) }  
| LPAREN GTHAN smtlib smtlib RPAREN
  { Gt($3, $4) } 
| LPAREN LEQ smtlib smtlib RPAREN
  { Leq($3, $4) } 
| LPAREN GEQ smtlib smtlib RPAREN
  { Geq($3, $4) } 
| LPAREN PLUS smtlib smtlib RPAREN
  { Add($3, $4) } 
| LPAREN MINUS smtlib smtlib RPAREN
  { Sub($3, $4) } 
| LPAREN STAR smtlib smtlib RPAREN
  { Mul($3, $4) } 
| LPAREN DIV smtlib smtlib RPAREN
  { Div($3, $4) } 
| TOP
  { Id("true") }
| NU
  { Id("v") }
| id 
  { FV($1) }
| int
  { Id(string_of_int $1) }
;

exp:
| LET id EQ exp IN exp 
  { ELet($2, $4, $6) }
| IF exp THEN LBRACE exp RBRACE ELSE LBRACE exp RBRACE 
  { EIf($2, $5, $9) }
| LET id EQ MKARRAY int IN exp // int => exp ?
  { EMkarray($2, $5, $7) }
| id ASSIGN exp SEMI exp
  { EAssign($1, $3, $5) }
| ALIAS LPAREN exp EQ exp RPAREN SEMI exp
  { EAlias($3, $5, $8) }
| ASSERT LPAREN exp RPAREN SEMI exp
  { EAssert($3, $6) }
| exp SEMI exp
  { ESeq($1, $3) } // ELet ?
| STAR id 
  { EDeref($2) }
| id LPAREN args RPAREN
  { EApp($1, $3) }
| MINUS exp 
  { ESub(EConstInt(0), $2) } // TODO: make pattern
| exp EQ exp 
  { EEq($1, $3) }
| exp LTHAN exp 
  { ELt($1, $3) }
| exp GTHAN exp 
  { EGt($1, $3) }
| exp LEQ exp 
  { ELeq($1, $3) }
| exp GEQ exp 
  { EGeq($1, $3) }
| exp NEQ exp 
  { ENeq($1, $3) }
| exp AND exp 
  { EAnd($1, $3) }
| exp OR exp 
  { EOr($1, $3) }
| NOT exp
  { ENot($2) }
| exp PLUS exp 
  { EAdd($1, $3) }
| exp MINUS exp 
  { ESub($1, $3) }
| exp STAR exp 
  { EMul($1, $3) }
| exp DIV exp 
  { EDiv($1, $3) }
| LPAREN exp RPAREN 
  { $2 }
| UNIT
  { EConstUnit }
| FAIL
  { EConstFail }
| int 
  { EConstInt($1) }
| TRUE
  { EConstTrue }
| FALSE
  { EConstFalse }
| id 
  { EVar($1) }
;

args:
| exp 
  { [$1] }
| exp COMMA args
  { $1 :: $3 }
;

int:
  INT { $1 }
;

float:
  FLOAT { $1 }
;

id:
  ID { $1 }
;
