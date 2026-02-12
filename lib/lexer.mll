{
open Parser
exception Lex_error of string
}

let ident_start = ['A'-'Z''a'-'z''_']
let ident_char = ['A'-'Z''a'-'z''0'-'9''_''\'']
let whitespace = [' ' '\t' '\r' '\n']
let ident = ident_start ident_char* 

rule token = parse
| whitespace+ { token lexbuf }
| "--" [^'\n']* { token lexbuf } (* single line comment *)
| "Type" { TYPE }
| "let" { LET }
| "in" { IN }
| "if" { IF }
| "then" { THEN }
| "else" { ELSE }
| "Bool" { BOOL }
| "True" { TRUE }
| "False" { FALSE }
| "Unit" { UNIT }
| "Sorry" { SORRY }
| "PrintMe" { PRINTME }
| "()" { UNITVAL }
| "->" { ARROW }
| '\\' { LAMBDA }
| '*' { STAR }
| ':' { COLON }
| '.' { DOT }
| ',' { COMMA }
| '|' { BAR }
| '=' { EQUAL }
| '(' { LPAR }
| ')' { RPAR }
| '{' { LBRACE }
| '}' { RBRACE }
| ident as x { IDENT x }
| eof { EOF }
| _ { raise (Lex_error "unexpected character") }

