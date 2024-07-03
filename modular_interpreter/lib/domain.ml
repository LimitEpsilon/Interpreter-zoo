open Datatypes
open Syntax

type loc = positive

type 'wvl shdw =
  | Init
  | Read of 'wvl shdw * var
  | Call of 'wvl shdw * 'wvl
  | Dstr of 'wvl shdw * dstr

type 'wvl nv = Nv_mt | Nv_sh of 'wvl shdw | Nv_bd of var * 'wvl * 'wvl nv

type ('wvl, 'k) vl =
  | Vl_exp of 'wvl nv
  | Vl_sh of 'wvl shdw
  | Vl_clos of var * 'k * 'wvl nv
  | Vl_cstr of 'wvl cstr

type 'k wvl =
  | Wvl_v of ('k wvl, 'k) vl
  | Wvl_recv of ('k wvl, 'k) vl
  | Wvl_bloc of int
  | Wvl_floc of loc

type trace =
  | Bot
  | Wal of trace wvl
  | Match of trace wvl shdw * (cstr_type * trace) list
  | Guard of trace wvl nv * trace

type walue = trace wvl
type value = (walue, trace) vl
type shadow = walue shdw
type env = walue nv

(** val bot : trace **)

let bot = Bot

(** val wal : walue -> trace **)

let wal w = Wal w

(** val case : shadow -> (cstr_type, trace) list -> trace **)

let case s b = Match (s, b)

(** val guard : env -> trace -> trace **)

let guard ctx t = Guard (ctx, t)

(** val open_loc_shdw :
    (int -> loc -> walue -> walue) -> int -> loc -> shadow -> shadow **)

let rec open_loc_shdw (f : int -> loc -> walue -> walue) i l = function
  | Init -> Init
  | Read (s, x) -> Read (open_loc_shdw f i l s, x)
  | Call (s, w) -> Call (open_loc_shdw f i l s, f i l w)
  | Dstr (s, d) -> Dstr (open_loc_shdw f i l s, d)

(** val open_loc_nv :
    (int -> loc -> walue -> walue) -> int -> loc -> env -> walue nv **)

let rec open_loc_nv (f : int -> loc -> walue -> walue) i l = function
  | Nv_mt -> Nv_mt
  | Nv_sh s -> Nv_sh (open_loc_shdw f i l s)
  | Nv_bd (x, w, ctx') -> Nv_bd (x, f i l w, open_loc_nv f i l ctx')

(** val open_loc_vl :
    (int -> loc -> walue -> walue) -> int -> loc -> value -> (walue, trace) vl **)

let open_loc_vl (f : int -> loc -> walue -> walue) i l = function
  | Vl_exp ctx -> (Vl_exp (open_loc_nv f i l ctx) : value)
  | Vl_sh s -> Vl_sh (open_loc_shdw f i l s)
  | Vl_clos (x, k, ctx) -> Vl_clos (x, k, open_loc_nv f i l ctx)
  | Vl_cstr c ->
      Vl_cstr { cs_type = c.cs_type; cs_args = List.map (f i l) c.cs_args }

(** val open_loc_walue : int -> loc -> walue -> walue **)

let rec open_loc_walue i l (w : walue) =
  let open_loc_vl = open_loc_vl open_loc_walue in
  match w with
  | Wvl_v v -> Wvl_v (open_loc_vl i l v)
  | Wvl_recv v -> Wvl_recv (open_loc_vl (i + 1) l v)
  | Wvl_bloc n -> (
      match Int.equal i n with true -> Wvl_floc l | false -> Wvl_bloc n)
  | Wvl_floc l -> Wvl_floc l

(** val open_loc_value : int -> loc -> value -> (walue, trace) vl **)

let open_loc_value = open_loc_vl open_loc_walue

(** val close_shdw :
    (int -> loc -> walue -> walue) -> int -> loc -> shadow -> shadow **)

let rec close_shdw (f : int -> loc -> walue -> walue) i l = function
  | Init -> Init
  | Read (s, x) -> Read (close_shdw f i l s, x)
  | Call (s, w) -> Call (close_shdw f i l s, f i l w)
  | Dstr (s, d) -> Dstr (close_shdw f i l s, d)

(** val close_nv :
    (int -> loc -> walue -> walue) -> int -> loc -> env -> env **)

let rec close_nv (f : int -> loc -> walue -> walue) i l = function
  | Nv_mt -> Nv_mt
  | Nv_sh s -> Nv_sh (close_shdw f i l s)
  | Nv_bd (x, w, ctx') -> Nv_bd (x, f i l w, close_nv f i l ctx')

(** val close_vl :
    (int -> loc -> walue -> walue) -> int -> loc -> value -> value **)

let close_vl (f : int -> loc -> walue -> walue) i l = function
  | Vl_exp ctx -> (Vl_exp (close_nv f i l ctx) : value)
  | Vl_sh s -> Vl_sh (close_shdw f i l s)
  | Vl_clos (x, k, ctx) -> Vl_clos (x, k, close_nv f i l ctx)
  | Vl_cstr c ->
      Vl_cstr { cs_type = c.cs_type; cs_args = List.map (f i l) c.cs_args }

(** val close_walue : int -> loc -> walue -> walue **)

let rec close_walue i l (w : walue) =
  let close_vl = close_vl close_walue in
  match w with
  | Wvl_v v -> Wvl_v (close_vl i l v)
  | Wvl_recv v -> Wvl_recv (close_vl (i + 1) l v)
  | Wvl_bloc n -> Wvl_bloc n
  | Wvl_floc l' -> (
      match Pos.eqb l l' with true -> Wvl_bloc i | false -> Wvl_floc l')

(** val close_value : int -> loc -> value -> value **)

let close_value = close_vl close_walue

(** val open_wvl_shdw :
    (int -> walue -> walue -> walue) -> int -> walue -> shadow -> shadow **)

let rec open_wvl_shdw (f : int -> walue -> walue -> walue) i u = function
  | Init -> Init
  | Read (s, x) -> Read (open_wvl_shdw f i u s, x)
  | Call (s, w) -> Call (open_wvl_shdw f i u s, f i u w)
  | Dstr (s, d) -> Dstr (open_wvl_shdw f i u s, d)

(** val open_wvl_nv :
    (int -> walue -> walue -> walue) -> int -> walue -> env -> walue nv **)

let rec open_wvl_nv (f : int -> walue -> walue -> walue) i u = function
  | Nv_mt -> Nv_mt
  | Nv_sh s -> Nv_sh (open_wvl_shdw f i u s)
  | Nv_bd (x, w, ctx') -> Nv_bd (x, f i u w, open_wvl_nv f i u ctx')

(** val open_wvl_vl :
    (int -> walue -> walue -> walue) -> int -> walue -> value -> (walue,
    trace) vl **)

let open_wvl_vl (f : int -> walue -> walue -> walue) i u = function
  | Vl_exp ctx -> (Vl_exp (open_wvl_nv f i u ctx) : value)
  | Vl_sh s -> Vl_sh (open_wvl_shdw f i u s)
  | Vl_clos (x, k, ctx) -> Vl_clos (x, k, open_wvl_nv f i u ctx)
  | Vl_cstr c ->
      Vl_cstr { cs_type = c.cs_type; cs_args = List.map (f i u) c.cs_args }

(** val open_wvl_walue : int -> walue -> walue -> walue **)

let rec open_wvl_walue i u w =
  let open_wvl_vl = open_wvl_vl open_wvl_walue in
  match w with
  | Wvl_v v -> Wvl_v (open_wvl_vl i u v)
  | Wvl_recv v -> Wvl_recv (open_wvl_vl (i + 1) u v)
  | Wvl_bloc n -> ( match Int.equal i n with true -> u | false -> Wvl_bloc n)
  | Wvl_floc l -> Wvl_floc l

(** val open_wvl_value : int -> walue -> value -> (walue, trace) vl **)

let open_wvl_value = open_wvl_vl open_wvl_walue

(** val alloc_shdw : (walue -> positive) -> shadow -> positive **)

let rec alloc_shdw f = function
  | Init -> XH
  | Read (s, _) -> alloc_shdw f s
  | Call (s, w) -> Pos.max (alloc_shdw f s) (f w)
  | Dstr (s, _) -> alloc_shdw f s

(** val alloc_nv : (walue -> positive) -> env -> positive **)

let rec alloc_nv f = function
  | Nv_mt -> XH
  | Nv_sh s -> alloc_shdw f s
  | Nv_bd (_, w, ctx') -> Pos.max (f w) (alloc_nv f ctx')

(** val alloc_vl : (walue -> positive) -> value -> positive **)

let alloc_vl f (v : value) =
  match v with
  | Vl_exp ctx -> alloc_nv f ctx
  | Vl_sh s -> alloc_shdw f s
  | Vl_clos (_, _, ctx) -> alloc_nv f ctx
  | Vl_cstr c ->
      let for_each acc w = Pos.max acc (f w) in
      List.fold_left for_each XH c.cs_args

(** val alloc_walue : walue -> positive **)

let rec alloc_walue w =
  let alloc_vl = alloc_vl alloc_walue in
  match w with
  | Wvl_v v -> alloc_vl v
  | Wvl_recv v -> alloc_vl v
  | Wvl_bloc _ -> XH
  | Wvl_floc l -> Pos.succ l

(** val alloc_value : value -> positive **)

let alloc_value = alloc_vl alloc_walue

(** val alloc_env : env -> positive **)

let alloc_env = alloc_nv alloc_walue

let rec print_shadow : shadow -> string = function
  | Init -> "Init"
  | Read (s, x) -> "Read (" ^ print_shadow s ^ ", " ^ x ^ ")"
  | Call (s, w) -> "Call (" ^ print_shadow s ^ ", " ^ print_walue w ^ ")"
  | Dstr (s, { ds_type = { cs_name; _ }; ds_idx }) ->
      "Dstr (" ^ print_shadow s ^ ", "
      ^ Syntax.string_of_cstr cs_name
      ^ ", " ^ string_of_int ds_idx ^ ")"

and print_env : env -> string = function
  | Nv_mt -> "•"
  | Nv_sh s -> "[" ^ print_shadow s ^ "]"
  | Nv_bd (x, w, e) -> "(" ^ x ^ ", " ^ print_walue w ^ ") :: " ^ print_env e

and print_value : value -> string = function
  | Vl_sh s -> print_shadow s
  | Vl_exp e -> print_env e
  | Vl_clos (x, _k, e) -> "⟨" ^ x ^ ", " ^ "<fun>" ^ ", " ^ print_env e ^ "⟩"
  | Vl_cstr { cs_type = { cs_name; _ }; cs_args } ->
      let args =
        List.fold_left
          (fun acc arg ->
            if acc = "" then print_walue arg else acc ^ "; " ^ print_walue arg)
          "" cs_args
      in
      Syntax.string_of_cstr cs_name ^ "[" ^ args ^ "]"

and print_walue : walue -> string = function
  | Wvl_v v -> print_value v
  | Wvl_recv v -> "μ." ^ print_value v
  | Wvl_bloc n -> string_of_int n
  | Wvl_floc _ -> "ℓ"

let rec string_of_trace (lvl : int) : trace -> string = function
  | Bot -> indent lvl ^ "⊥"
  | Wal w -> indent lvl ^ print_walue w
  | Guard (e, t) ->
      indent lvl ^ print_env e ^ " →\n" ^ string_of_trace (lvl + 1) t
  | Match (s, b) ->
      let branches =
        List.fold_left
          (fun acc ({ cs_name; _ }, t) ->
            let c = string_of_cstr cs_name in
            if acc = "" then
              indent lvl ^ c ^ " ⤇\n" ^ string_of_trace (lvl + 1) t
            else ";\n" ^ indent lvl ^ c ^ " ⤇\n" ^ string_of_trace (lvl + 1) t)
          "" b
      in
      indent lvl ^ print_shadow s ^ " → {\n" ^ branches ^ "}"

let print_trace = string_of_trace 0

let string_of_filters (filters : (string * shadow) list) (w : walue) =
  let fold acc (c, s) =
    let filter = c ^ " ⤇ " ^ print_shadow s in
    if acc = "" then filter else acc ^ " ∧ " ^ filter
  in
  let filters = List.fold_left fold "" filters in
  if filters = "" then print_walue w else filters ^ " ⇒ " ^ print_walue w

let rec string_of_result (filters : (string * shadow) list) = function
  | Bot -> ""
  | Wal w -> string_of_filters filters w
  | Guard (_, t) -> string_of_result filters t
  | Match (s, b) ->
      let fold acc (c, t) =
        let result =
          string_of_result ((string_of_cstr c.cs_name, s) :: filters) t
        in
        if acc = "" then result
        else if result = "" then acc
        else
          acc
          ^ "\n\
             ----------------------------------------------------------------------------------------------------\n"
          ^ result
      in
      List.fold_left fold "" b

let print_result = string_of_result []
