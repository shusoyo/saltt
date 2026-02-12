%{
open Raw
%}

%token <string> IDENT
%token TYPE PRINTME SORRY BOOL TRUE FALSE IF THEN ELSE UNIT UNITVAL
%token LET IN
%token LAMBDA ARROW STAR COLON DOT COMMA BAR EQUAL
%token LPAR RPAR LBRACE RBRACE
%token EOF

%nonassoc VAR_IDENT
%nonassoc COLON

%start <n_term> named_term

%%

named_term:
  expr EOF { $1 }
;

expr:
  let_expr { $1 }
;

let_expr:
  LET IDENT EQUAL expr IN expr { Let ($4, ($2, $6)) }
| LET LPAR IDENT COMMA IDENT RPAR EQUAL expr IN expr
    { LetPair ($8, ($3, $5, $10)) }
| if_expr { $1 }
;

if_expr:
  IF expr THEN expr ELSE expr { If ($2, $4, $6) }
| lambda_expr { $1 }
;

lambda_expr:
  LAMBDA binders DOT expr
    { List.fold_right (fun binder acc -> Lam (binder, acc)) $2 $4 }
| pi_expr { $1 }
;

binders:
  IDENT binders { $1 :: $2 }
| IDENT { [$1] }
;

pi_expr:
  LPAR IDENT COLON expr RPAR ARROW pi_expr { TyPi ($4, ($2, $7)) }
| sigma_expr ARROW pi_expr { TyPi ($1, ("_", $3)) }
| sigma_expr { $1 }
;

sigma_expr:
  app_expr STAR sigma_expr { TySigma ($1, ("_", $3)) }
| LBRACE IDENT COLON expr BAR expr RBRACE { TySigma ($4, ($2, $6)) }
| app_expr { $1 }
;

app_expr:
  atom atoms { List.fold_left (fun acc arg -> App (acc, arg)) $1 $2 }
;

atoms:
  atom atoms { $1 :: $2 }
| /* empty */ { [] }
;

atom:
  IDENT %prec VAR_IDENT { Var $1 }
| TYPE { TyType }
| SORRY { Sorry }
| PRINTME { PrintMe }
| BOOL { TyBool }
| TRUE { Bool true }
| FALSE { Bool false }
| UNIT { TyUnit }
| UNITVAL { Unit }
| LPAR expr COLON expr RPAR { Ann ($2, $4) }
| LPAR expr COMMA expr RPAR { Pair ($2, $4) }
| LPAR expr RPAR { $2 }
;
