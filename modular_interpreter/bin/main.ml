open Modular_interpreter

let nat_of_int n =
  let open Datatypes in
  let rec aux acc n = if n <= 0 then acc else aux (S acc) (n - 1) in
  aux O n

let main () =
  let src = ref "" in
  let opt_pp = ref false in
  let opt_trace = ref 0 in
  let opt_result = ref 0 in
  Arg.parse
    [
      ("-pp", Arg.Unit (fun _ -> opt_pp := true), "print pgm");
      ("-trace", Arg.Int (fun n -> opt_trace := n), "print trace");
      ("-result", Arg.Int (fun n -> opt_result := n), "print result");
    ]
    (fun x -> src := x)
    ("Usage : " ^ Filename.basename Sys.argv.(0) ^ " [-option] [filename] ");
  let lexbuf =
    Lexing.from_channel (if !src = "" then stdin else open_in !src)
  in
  let pgm = Parser.term Lexer.read lexbuf in
  if !opt_pp then
    let () = print_endline "=== Printing Input Program ===" in
    Syntax.pp pgm
  else if !opt_trace <> 0 then
    let result = Interpreter.interp (nat_of_int !opt_trace) pgm in
    print_endline (Domain.print_trace result)
  else if !opt_result <> 0 then
    let () = print_endline "=== Printing Results ===" in
    let result = Interpreter.interp (nat_of_int !opt_result) pgm in
    print_endline (Domain.print_result result)
  else print_endline "Please provide one of options! (-pp, -trace, -result)"

let _ = main ()
