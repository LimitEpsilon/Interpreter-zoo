open Datatypes
open Syntax
open Domain

(** val read_env : env -> var -> (trace wvl * env) option **)

let read_env ctx x =
  let read =
    let rec read ctx acc =
      match ctx with
      | Nv_mt -> None
      | Nv_sh s -> Some (Wvl_v (Vl_sh (Read (s, x))), acc Nv_mt)
      | Nv_bd (x', w', ctx') -> (
          match String.equal x x' with
          | true -> Some (w', acc ctx')
          | false ->
              let acc' ctx' = acc (Nv_bd (x', w', ctx')) in
              read ctx' acc')
    in
    read
  in
  read ctx id

(** val unroll : walue -> value option **)

let unroll w =
  match w with
  | Wvl_v v -> Some v
  | Wvl_recv v -> Some (open_wvl_value O w v)
  | _ -> None

(** val dstr_shadow : shadow -> 'a1 branch -> env **)

let dstr_shadow s b =
  let rec for_each n l acc =
    match l with
    | [] -> acc
    | hd :: tl ->
        for_each (n + 1) tl
          (Nv_bd
             ( hd,
               Wvl_v (Vl_sh (Dstr (s, { ds_type = b.br_cstr; ds_idx = n }))),
               acc ))
  in
  for_each 0 b.br_vars (Nv_sh Init)

(** val dstr_cstr : walue cstr -> 'a1 branch -> env option **)

let dstr_cstr c b =
  let b_name = b.br_cstr.cs_name in
  let c_name = c.cs_type.cs_name in
  match eqb_cstr c_name b_name with
  | true ->
      let add_binding =
        let rec add_binding acc xs ws =
          match xs with
          | [] -> acc
          | x :: xs -> (
              match ws with
              | [] -> assert false (* absurd case *)
              | w :: ws -> add_binding (Nv_bd (x, w, acc)) xs ws)
        in
        add_binding
      in
      Some (add_binding (Nv_sh Init) b.br_vars c.cs_args)
  | false -> None

(** val map_branches :
    (trace -> trace) -> (cstr_type * trace) list -> (cstr_type * trace) list **)

let map_branches k b =
  let for_branch (c, t) = (c, k t) in
  List.map for_branch b

(** val bind : (walue -> trace) -> trace -> trace **)

let rec bind k = function
  | Bot -> Bot
  | Wal w -> k w
  | Match (s, b) -> Match (s, map_branches (bind k) b)
  | Guard (ctx, t) -> Guard (ctx, bind k t)

(** val dstr_trace : dstr -> trace -> trace **)

let dstr_trace d =
  let k w =
    match unroll w with
    | Some v -> (
        match v with
        | Vl_sh s -> Wal (Wvl_v (Vl_sh (Dstr (s, d))))
        | Vl_cstr c -> (
            let c_name = c.cs_type.cs_name in
            let d_name = d.ds_type.cs_name in
            match eqb_cstr c_name d_name with
            | true -> Wal (get_idx c.cs_args d.ds_idx)
            | false -> Bot)
        | _ -> Bot)
    | None -> Bot
  in
  bind k

(** val cstr_trace : trace cstr -> trace **)

let cstr_trace c =
  let rec fold_arg v k =
    match v with
    | [] -> Wal (Wvl_v (Vl_cstr { cs_type = c.cs_type; cs_args = k [] }))
    | hd :: tl ->
        let check_trace w = fold_arg tl (fun v -> k (w :: v)) in
        bind check_trace hd
  in
  fold_arg c.cs_args id

(** val link_trace :
    (walue -> trace) -> (walue -> trace) -> trace -> trace **)

let rec link_trace link k = function
  | Bot -> Bot
  | Wal w -> bind k (link w)
  | Match (s, b) ->
      let check_match w =
        match unroll w with
        | Some v -> (
            match v with
            | Vl_sh s -> Match (s, map_branches (link_trace link k) b)
            | Vl_cstr c -> (
                let fold_branch acc (c', t) =
                  match acc with
                  | Some t -> Some t
                  | None -> (
                      match eqb_cstr c.cs_type.cs_name c'.cs_name with
                      | true -> Some (link_trace link k t)
                      | false -> None)
                in
                match List.fold_left fold_branch None b with
                | Some t -> t
                | None -> Bot)
            | _ -> Bot)
        | None -> Bot
      in
      bind check_match (link (Wvl_v (Vl_sh s)))
  | Guard (ctx, t) ->
      let check_guard w =
        match unroll w with
        | Some v -> (
            match v with
            | Vl_exp ctx -> Guard (ctx, link_trace link k t)
            | Vl_sh s -> Guard (Nv_sh s, link_trace link k t)
            | _ -> Bot)
        | None -> Bot
      in
      bind check_guard (link (Wvl_v (Vl_exp ctx)))

(** val read_trace : var -> trace -> trace **)

let read_trace x =
  let read w =
    match unroll w with
    | Some v -> (
        match v with
        | Vl_exp ctx -> (
            match read_env ctx x with
            | Some (w, ctx) -> Guard (ctx, Wal w)
            | None -> Bot)
        | Vl_sh s -> Wal (Wvl_v (Vl_sh (Read (s, x))))
        | _ -> Bot)
    | None -> Bot
  in
  bind read

(** val call_trace : (env -> walue -> trace) -> trace -> trace -> trace **)

let call_trace link fn arg =
  let check_fn fn =
    match unroll fn with
    | Some v -> (
        match v with
        | Vl_sh s ->
            let check_arg arg = Wal (Wvl_v (Vl_sh (Call (s, arg)))) in
            bind check_arg arg
        | Vl_clos (x, t, ctx) ->
            let check_arg arg =
              let ctx' = Nv_bd (x, arg, ctx) in
              link_trace (link ctx') (fun w -> Wal w) t
            in
            bind check_arg arg
        | _ -> Bot)
    | None -> Bot
  in
  bind check_fn fn

(** val close_rec : loc -> trace -> trace **)

let close_rec l =
  let close w =
    match unroll w with
    | Some v -> Wal (Wvl_recv (close_value O l v))
    | None -> Bot
  in
  bind close

(** val bd_trace : var -> trace -> trace -> trace **)

let bd_trace x w ctx =
  let check_bd w =
    let check_mod ctx =
      match unroll ctx with
      | Some v -> (
          match v with
          | Vl_exp ctx -> Wal (Wvl_v (Vl_exp (Nv_bd (x, w, ctx))))
          | Vl_sh s -> Wal (Wvl_v (Vl_exp (Nv_bd (x, w, Nv_sh s))))
          | _ -> Bot)
      | None -> Bot
    in
    bind check_mod ctx
  in
  bind check_bd w

(** val clos_trace : var -> trace -> trace -> trace **)

let clos_trace x k =
  let clos w =
    match unroll w with
    | Some v -> (
        match v with
        | Vl_exp ctx -> Wal (Wvl_v (Vl_clos (x, k, ctx)))
        | Vl_sh s -> Wal (Wvl_v (Vl_clos (x, k, Nv_sh s)))
        | _ -> Bot)
    | None -> Bot
  in
  bind clos

(** val filter_env : trace -> trace **)

let filter_env =
  let filter w =
    match unroll w with
    | Some v -> (
        match v with
        | Vl_exp ctx -> Wal (Wvl_v (Vl_exp ctx))
        | Vl_sh s -> Wal (Wvl_v (Vl_exp (Nv_sh s)))
        | _ -> Bot)
    | None -> Bot
  in
  bind filter

(** val link : nat -> env -> walue -> trace **)

let rec link n ctx =
  match n with
  | O -> fun _ -> Bot
  | S n ->
      let rec link_wvl = function
        | Wvl_v v -> link_vl v
        | Wvl_recv v ->
            let l = Pos.max (alloc_value v) (alloc_env ctx) in
            close_rec l (link_vl (open_loc_value O l v))
        | Wvl_bloc _ -> Bot
        | Wvl_floc l -> Wal (Wvl_floc l)
      and link_vl = function
        | Vl_exp ctx' -> link_nv ctx'
        | Vl_sh s -> link_shdw s
        | Vl_clos (x, k, ctx') -> clos_trace x k (link_nv ctx')
        | Vl_cstr c ->
            cstr_trace
              { cs_type = c.cs_type; cs_args = List.map link_wvl c.cs_args }
      and link_nv = function
        | Nv_mt -> Wal (Wvl_v (Vl_exp Nv_mt))
        | Nv_sh s -> filter_env (link_shdw s)
        | Nv_bd (x, w, ctx') ->
            let bound = link_wvl w in
            let exp = link_nv ctx' in
            bd_trace x bound exp
      and link_shdw = function
        | Init -> Wal (Wvl_v (Vl_exp ctx))
        | Read (s, x) -> read_trace x (link_shdw s)
        | Call (s, w) ->
            let fn = link_shdw s in
            let arg = link_wvl w in
            call_trace (link n) fn arg
        | Dstr (s, d) -> dstr_trace d (link_shdw s)
      in
      link_wvl

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
        let w = Wvl_recv (close_value O XH v) in
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
    | App (m, n) -> call_trace link (eval link m) (eval link n)
    | Link (m, n) -> sem_link link (eval link m) (eval link n)
    | Mt -> guard (Wal (Wvl_v (Vl_exp Nv_mt)))
    | Bind (x, m, n) -> sem_bind link x (eval link m) (eval link n)
    | Cstr c ->
        cstr_trace
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
