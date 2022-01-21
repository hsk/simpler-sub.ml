{ open Parser }
rule token = parse
| [' ' '\t' '\n'] { token lexbuf }
| '('    { LPAREN }
| ')'    { RPAREN }
| '{'    { LBRACE }
| '}'    { RBRACE }
| "."    { DOT }
| ";"    { SEMI }
| "let"  { LET }
| "rec"  { REC }
| "in"   { IN }
| "="    { EQL }
| "fun"  { FUN }
| "->"   { ARROW }
| "if"   { IF }
| "then" { THEN }
| "else" { ELSE }
| "true" { TRUE }
| "false" { FALSE }
| ['0'-'9']+ as n { INT (int_of_string n) }
| ['A'-'Z' 'a'-'z' '_']['A'-'Z' 'a'-'z' '_' '0'-'9']* as x { ID x }
| eof    { EOF }
