%{
  open Z3Syntax2
%}

// values
%token <int> INT
%token <float> FLOAT
%token <string> ID

// types
%token TINT TREAL

// structure
%token SAT MODEL DEF LPAREN RPAREN EOF
%token MINUS DIV UNDER
%token O C D L H

%start result
%type <Z3Syntax2.result> result
%%

result:
  SAT LPAREN defines RPAREN { $3 }
;

defines:
| define 
  { [$1] } 
| define defines
  { $1 :: $2 }
;

define:
| LPAREN DEF O int UNDER id UNDER int LPAREN RPAREN TREAL value RPAREN 
  { Own($4, $6, $8, $12) }
| LPAREN DEF C int UNDER H id UNDER id UNDER int LPAREN RPAREN TINT value RPAREN 
  { CHigh($4, $7, $9, $11, $15) }
| LPAREN DEF C int UNDER L id UNDER id UNDER int LPAREN RPAREN TINT value RPAREN 
  { CLow($4, $7, $9, $11, $15) }
| LPAREN DEF D int UNDER H id UNDER int LPAREN RPAREN TINT value RPAREN 
  { DHigh($4, $7, $9, $13) }
| LPAREN DEF D int UNDER L id UNDER int LPAREN RPAREN TINT value RPAREN 
  { DLow($4, $7, $9, $13) }
;

value:
| INT 
  { Int($1) }
| LPAREN MINUS INT RPAREN
  { Int(-$3) } 
| FLOAT
  { Float($1) }
| LPAREN DIV FLOAT FLOAT RPAREN
  { Float($3/.$4) }

int:
  INT { $1 }
;

id:
  ID { $1 }
;
