%{
open Syntax
let make_fun args body =
  List.fold_right (fun arg expr -> Lam (arg, expr)) args body
let check_record r =
  List.fold_right (fun (k,v) l -> assert(not (List.mem_assoc k l)); (k,v)::l) r []
%}
%token IF THEN ELSE FUN ARROW LET REC IN EQL SEMI DOT
%token LBRACE RBRACE LPAREN RPAREN EOF TRUE FALSE
%token <string> ID %token <int> INT
%start program %type<(bool * string * Syntax.term) list> program
%start expr %type<Syntax.term> expr
%%
expr        : term EOF                    { $1 }
program     : declaration* EOF            { $1 }
declaration : LET boption(REC) ID ID* EQL term SEMI?
                                          { ($2, $3, make_fun $4 $6) }
term        : FUN ID+ ARROW term          { make_fun $2 $4 }
            | LET boption(REC) ID ID* EQL term IN term
                                          { Let ($2, $3, make_fun $4 $6, $8) }
            | IF term THEN term ELSE term { App(App(App(Var "if",$2),$4),$6) }
            | app_expr                    { $1 }
app_expr    : app_expr prim_expr          { App($1,$2) }
            | prim_expr                   { $1 }
prim_expr   : record                      { $1 }
            | prim_expr DOT ID            { Sel ($1, $3) }
            | ID                          { Var $1 }
            | INT                         { Lit $1 }
            | TRUE                        { Var "true"}
            | FALSE                       { Var "false"}
            | LPAREN term RPAREN          { $2 }
record      : LBRACE separated_list(SEMI, field) RBRACE
                                          { Rcd (check_record $2) }
field       : ID EQL term                 { ($1, $3) }
