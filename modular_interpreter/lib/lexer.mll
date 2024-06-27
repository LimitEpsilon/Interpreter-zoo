{
open Lexing
open Parser

exception SyntaxError of string

let keywords =
  let tbl : (string, token) Hashtbl.t = Hashtbl.create 10 in
  let add_to_tbl (id, tok) = Hashtbl.add tbl id tok in
  List.iter add_to_tbl
    [
      ("let", LET);
      ("fun", FUN);
      ("match", MATCH);
      ("S", SUCC);
      ("O", ZERO);
      ("Pair", PAIR);
    ];
  tbl
}

let blank = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"
let id = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_' '\'']*

let digit = ['0'-'9']
let int = digit+
let pow = ['e' 'E'] ['+' '-']? int
let real = ((int '.'? | (digit* '.' int))) pow?

rule read =
  parse
  | blank     { read lexbuf }
  | newline   { new_line lexbuf; read lexbuf }
  | int as n  { NAT (int_of_string n) }
  | id as s   { match Hashtbl.find_opt keywords s with Some s -> s | None -> ID s }
  | '#'       { comment lexbuf }
  | '='       { EQ }
  | "->"      { RARROW }
  | '('       { LPAREN }
  | ')'       { RPAREN }
  | '['       { LBRACK }
  | ']'       { RBRACK }
  | '{'       { LBRACE }
  | '}'       { RBRACE }
  | ','       { COMMA }
  | ";"       { SEMICOLON }
  | ";;"      { BIND }
  | '.'       { LINK }
  | eof       { EOF }
  | _         { raise (SyntaxError ("Unexpected char: " ^ lexeme lexbuf)) }

and comment =
  parse
  | newline { read lexbuf }
  | eof     { EOF }
  | _       { comment lexbuf }
