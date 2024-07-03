open Modular_interpreter

let () =
  let src = ref "" in
  let opt_pp = ref false in
  let opt_trace = ref 0 in
  let opt_result = ref 0 in
  let usage_msg =
    "Usage : " ^ Filename.basename Sys.argv.(0) ^ " [-option] [filename] "
  in
  let speclist =
    [
      ("-pp", Arg.Unit (fun _ -> opt_pp := true), "print pgm");
      ("-trace", Arg.Int (fun n -> opt_trace := n), "print trace");
      ("-result", Arg.Int (fun n -> opt_result := n), "print result");
    ]
  in
  Arg.parse speclist (fun x -> src := x) usage_msg;
  if !src = "" then Arg.usage speclist usage_msg
  else
    let lexbuf = Lexing.from_channel (open_in !src) in
    let pgm = Parser.term Lexer.read lexbuf in
    if !opt_pp then
      let () = print_endline "=== Printing Input Program ===" in
      Syntax.pp pgm
    else if !opt_trace <> 0 then
      let result = Interpreter.interp !opt_trace pgm in
      print_endline (Domain.print_trace result)
    else if !opt_result <> 0 then
      let () = print_endline "=== Printing Results ===" in
      let result = Interpreter.interp !opt_result pgm in
      print_endline (Domain.print_result result)
    else Arg.usage speclist usage_msg
