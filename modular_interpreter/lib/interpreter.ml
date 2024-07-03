open Datatypes
open Syntax
open Domain
open Linking

(** val sem_call :
    (env -> (walue -> trace) -> walue -> trace) -> trace -> trace -> trace **)

let sem_call link fn arg =
  let check_fn fn =
    match unroll fn with
    | Some v -> (
        match v with
        | Vl_sh s ->
            let check_arg arg = wal (Wvl_v (Vl_sh (Call (s, arg)))) in
            bind check_arg arg
        | Vl_clos (x, t, ctx) ->
            let check_arg arg =
              let ctx' = Nv_bd (x, arg, ctx) in
              link_trace (link ctx') wal t
            in
            bind check_arg arg
        | _ -> bot)
    | None -> bot
  in
  bind check_fn fn

(** val sem_link : (env -> walue -> trace) -> trace -> trace -> trace **)

let sem_link link ctx w =
  let check_module m =
    match unroll m with
    | Some v -> (
        match v with
        | Vl_exp ctx -> link_trace (link ctx) (fun x -> Wal x) w
        | Vl_sh s -> link_trace (link (Nv_sh s)) (fun x -> Wal x) w
        | _ -> Bot)
    | None -> Bot
  in
  bind check_module ctx

(** val sem_bind :
    (env -> walue -> trace) -> var -> trace -> trace -> trace **)

let sem_bind link x bd exp =
  let check_bd w =
    match unroll w with
    | Some v ->
        let w = Wvl_recv (close_value 0 XH v) in
        let check_exp ctx =
          match unroll ctx with
          | Some v -> (
              match v with
              | Vl_exp ctx -> Wal (Wvl_v (Vl_exp (Nv_bd (x, w, ctx))))
              | Vl_sh s -> Wal (Wvl_v (Vl_exp (Nv_bd (x, w, Nv_sh s))))
              | _ -> Bot)
          | None -> Bot
        in
        link_trace (link (Nv_bd (x, w, Nv_sh Init))) check_exp exp
    | None -> Bot
  in
  link_trace (link (Nv_bd (x, Wvl_floc XH, Nv_sh Init))) check_bd bd

(** val sem_cstr : trace cstr -> trace **)

let sem_cstr c =
  let fold_arg =
    let rec fold_arg args k' =
      match args with
      | [] -> wal (Wvl_v (Vl_cstr { cs_type = c.cs_type; cs_args = k' [] }))
      | hd :: tl ->
          let check_trace w = fold_arg tl (fun v -> k' (w :: v)) in
          bind check_trace hd
    in
    fold_arg
  in
  fold_arg c.cs_args id

(** val sem_case :
    (env -> walue -> trace) -> trace -> trace branch list -> trace **)

let sem_case link matched branches =
  let check_match m =
    match unroll m with
    | Some v -> (
        match v with
        | Vl_sh s ->
            let map_each b =
              let body =
                link_trace (link (dstr_shadow s b)) (fun x -> Wal x) b.br_body
              in
              (b.br_cstr, body)
            in
            Match (s, List.map map_each branches)
        | Vl_cstr c -> (
            let fold_each acc b =
              match acc with
              | Some t -> Some t
              | None -> (
                  match dstr_cstr c b with
                  | Some ctx ->
                      Some (link_trace (link ctx) (fun x -> Wal x) b.br_body)
                  | None -> None)
            in
            match List.fold_left fold_each None branches with
            | Some t -> t
            | None -> Bot)
        | _ -> Bot)
    | None -> Bot
  in
  bind check_match matched

let prune = id

(** val eval : (env -> walue -> trace) -> tm -> trace **)

let rec eval link e =
  let guard x = Guard (Nv_sh Init, x) in
  let sem =
    match e with
    | Var x -> Wal (Wvl_v (Vl_sh (Read (Init, x))))
    | Fn (x, m) -> Wal (Wvl_v (Vl_clos (x, eval link m, Nv_sh Init)))
    | App (m, n) -> sem_call link (eval link m) (eval link n)
    | Link (m, n) -> sem_link link (eval link m) (eval link n)
    | Mt -> guard (Wal (Wvl_v (Vl_exp Nv_mt)))
    | Bind (x, m, n) -> sem_bind link x (eval link m) (eval link n)
    | Cstr c ->
        sem_cstr
          { cs_type = c.cs_type; cs_args = List.map (eval link) c.cs_args }
    | Case (e, b) ->
        let matched = eval link e in
        let branches =
          let for_each b =
            {
              br_cstr = b.br_cstr;
              br_vars = b.br_vars;
              br_body = eval link b.br_body;
            }
          in
          List.map for_each b
        in
        sem_case link matched branches
  in
  prune sem

(** val interp : nat -> tm -> trace **)

let interp n = eval (link n)
