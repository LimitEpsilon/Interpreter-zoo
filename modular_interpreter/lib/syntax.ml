type var = string
type cstr_name = Zero | Succ | Pair

(** val eqb_cstr : cstr_name -> cstr_name -> bool **)

let eqb_cstr c1 c2 =
  match c1 with
  | Zero -> ( match c2 with Zero -> true | _ -> false)
  | Succ -> ( match c2 with Succ -> true | _ -> false)
  | Pair -> ( match c2 with Pair -> true | _ -> false)

type cstr_type = { cs_arity : int; cs_name : cstr_name }
type 'v cstr = { cs_type : cstr_type; cs_args : 'v list }
type dstr = { ds_type : cstr_type; ds_idx : int }
type 'b branch = { br_cstr : cstr_type; br_vars : var list; br_body : 'b }

type tm =
  | Var of var
  | Fn of var * tm
  | App of tm * tm
  | Link of tm * tm
  | Mt
  | Bind of var * tm * tm
  | Cstr of tm cstr
  | Case of tm * tm branch list

let zero_tm = Cstr { cs_type = { cs_arity = 0; cs_name = Zero }; cs_args = [] }

let zero_branch b =
  { br_cstr = { cs_arity = 0; cs_name = Zero }; br_vars = []; br_body = b }

let succ_tm t =
  Cstr { cs_type = { cs_arity = 1; cs_name = Succ }; cs_args = [ t ] }

let succ_branch x b =
  { br_cstr = { cs_arity = 1; cs_name = Succ }; br_vars = [ x ]; br_body = b }

let pair_tm cs_args =
  Cstr { cs_type = { cs_arity = 2; cs_name = Pair }; cs_args }

let pair_branch br_vars b =
  { br_cstr = { cs_arity = 2; cs_name = Pair }; br_vars; br_body = b }

let string_of_cstr = function Zero -> "O" | Succ -> "S" | Pair -> "Pair"

let indent lvl =
  let indent_char = "  " in
  let rec indent acc lvl =
    if lvl <= 0 then acc else indent (indent_char ^ acc) (lvl - 1)
  in
  indent "" lvl

let rec string_of_tm lvl t =
  match t with
  | Var x -> indent lvl ^ x
  | Fn (x, e) -> indent lvl ^ "fun " ^ x ^ "->\n" ^ string_of_tm (lvl + 1) e
  | App (e1, e2) ->
      indent lvl ^ "APP\n"
      ^ string_of_tm (lvl + 1) e1
      ^ "\n"
      ^ string_of_tm (lvl + 1) e2
  | Link (e1, e2) ->
      indent lvl ^ "LINK (\n"
      ^ string_of_tm (lvl + 1) e1
      ^ ") ⋊ (\n"
      ^ string_of_tm (lvl + 1) e2
      ^ ")"
  | Mt -> indent lvl ^ "•"
  | Bind (x, e1, e2) ->
      indent lvl ^ "let " ^ x ^ " =\n"
      ^ string_of_tm (lvl + 1) e1
      ^ " ;;\n"
      ^ string_of_tm (lvl + 1) e2
  | Cstr { cs_type = { cs_name; _ }; cs_args } ->
      let args =
        List.fold_left
          (fun acc e ->
            let s = string_of_tm (lvl + 1) e in
            if acc = "" then s else acc ^ ";\n" ^ s)
          "" cs_args
      in
      if args = "" then indent lvl ^ string_of_cstr cs_name ^ "[]"
      else indent lvl ^ string_of_cstr cs_name ^ "[\n" ^ args ^ "]"
  | Case (e, b) ->
      let branches =
        List.fold_left
          (fun acc { br_cstr = { cs_name; _ }; br_vars; br_body } ->
            let c = string_of_cstr cs_name in
            let v =
              List.fold_left
                (fun acc x -> if acc = "" then x else acc ^ "; " ^ x)
                "" br_vars
            in
            let s =
              indent lvl ^ c ^ "[" ^ v ^ "] ->\n"
              ^ string_of_tm (lvl + 1) br_body
            in
            if acc = "" then s else acc ^ ",\n" ^ s)
          "" b
      in
      indent lvl ^ "match\n"
      ^ string_of_tm (lvl + 1) e
      ^ if branches = "" then " {}" else " {\n" ^ branches ^ "}"

let pp t = print_endline (string_of_tm 0 t)
