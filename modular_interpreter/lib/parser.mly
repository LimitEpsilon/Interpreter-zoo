%{
open Syntax

let mk_nat (n : int) =
  let rec fold acc t =
    if t <= 0 then acc else fold (succ_tm acc) (t - 1)
  in fold zero_tm n

let mk_branch (cstr : cstr_name) (varlist : var list) (body : tm) =
  match cstr with
  | Zero ->
    if List.length varlist = 0 then zero_branch body
    else failwith "Variable list to zero branch is not empty"
  | Succ ->
    if List.length varlist = 1 then succ_branch (List.hd varlist) body
    else failwith "Variable list to succ branch does not have exactly one variable"
  | Pair ->
    if List.length varlist = 2 then pair_branch varlist body
    else failwith "Variable list to cons branch does not have exactly two variables"

let mk_cstr (cstr : cstr_name) (args : tm list) =
  match cstr with
  | Zero ->
    if List.length args = 0 then zero_tm
    else failwith "Argument list to zero constructor is not empty"
  | Succ ->
    if List.length args = 1 then succ_tm (List.hd args)
    else failwith "Argument list to succ constructor does not have exactly one term"
  | Pair ->
    if List.length args = 2 then pair_tm args
    else failwith "Argument list to cons constructor does not have exactly two terms"
%}

%token <int> NAT
%token <string> ID
%token FUN LET MATCH
%token EQ
%token ZERO SUCC PAIR
%token LPAREN RPAREN LBRACK RBRACK LBRACE RBRACE
%token RARROW COMMA SEMICOLON BIND LINK
%token EOF

%start <tm> term
%%
term:
    | term = bindterm; EOF { term }
    ;

bindterm:
    | term = open_bind { term }
    | term = closed_bind { term }
    ;

open_bind:
    | LET; name = ID; EQ; bound = bindterm { Bind (name, bound, Mt) }
    | LET; name = ID; EQ; bound = closed_bind; BIND; rest = open_bind { Bind (name, bound, rest) }
    ;

closed_bind:
    | term = funterm { term }
    | LET; name = ID; EQ; bound = closed_bind; BIND; rest = closed_bind { Bind (name, bound, rest) }
    ;

funterm:
    | term = appterm { term }
    | FUN; param = var; RARROW; body = funterm { Fn (param, body) }
    ;

appterm:
    | term = linkterm { term }
    | fn = appterm; arg = linkterm { App (fn, arg) }
    ;

linkterm:
    | term = atom { term }
    | export = linkterm; LINK; import = atom { Link (export, import) }
    ;

atom:
    | var = var { Var var }
    | LPAREN; RPAREN { Mt }
    | LPAREN; term = bindterm; RPAREN { term }
    | n = NAT { mk_nat n }
    | cstr = cstr; args = args { mk_cstr cstr args }
    | LPAREN; x = bindterm; COMMA; y = bindterm; RPAREN { mk_cstr Pair [x; y] }
    | MATCH; matched = bindterm; LBRACE; branches = branches; RBRACE { Case (matched, branches) }
    ;

branches:
    | branches = separated_list(COMMA, branch) { branches } ;

branch:
    | cstr = cstr; vars = varlist; RARROW; body = bindterm { mk_branch cstr vars body }
    | LPAREN; x = var; COMMA; y = var; RPAREN; RARROW; body = bindterm { mk_branch Pair [x; y] body }
    ;

cstr:
    | ZERO { Zero }
    | SUCC { Succ }
    | PAIR { Pair }
    ;

args:
    | { [ ] }
    | LBRACK; args = separated_list(SEMICOLON, bindterm); RBRACK { args }
    ;

varlist:
    | { [ ] }
    | LBRACK; vars = separated_list(SEMICOLON, var); RBRACK { vars }
    ;

var:
    | x = ID { x } ;

