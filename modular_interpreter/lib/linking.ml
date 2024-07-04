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
  | Wvl_recv v -> Some (open_wvl_value 0 w v)
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

(** val dstr_trace : dstr -> (walue -> trace) -> walue -> trace **)

let dstr_trace d k w =
  match unroll w with
  | Some v -> (
      match v with
      | Vl_sh s -> k (Wvl_v (Vl_sh (Dstr (s, d))))
      | Vl_cstr c -> (
          let c_name = c.cs_type.cs_name in
          let d_name = d.ds_type.cs_name in
          match eqb_cstr c_name d_name with
          | true -> k (get_idx c.cs_args d.ds_idx)
          | false -> bot)
      | _ -> bot)
  | None -> bot

(** val case_trace : 'v cstr -> (cstr_type * 'trace) list -> ('trace -> trace) -> trace *)
let case_trace (c : 'v cstr) (b : (cstr_type * 'trace) list) k =
  let fold_branch acc (c', t) =
    match acc with
    | Some t -> Some t
    | None -> (
        match eqb_cstr c.cs_type.cs_name c'.cs_name with
        | true -> Some (k t)
        | false -> None)
  in
  match List.fold_left fold_branch None b with Some t -> t | None -> bot

(** val link_trace :
    ((walue -> trace) -> walue -> trace) -> (walue -> trace) -> trace -> trace **)

let link_trace link k =
  let rec link_trace = function
    | Bot -> bot
    | Wal w -> link k w
    | Match (s, b) ->
        let check_match w =
          match unroll w with
          | Some v -> (
              match v with
              | Vl_sh s -> case s (map_branches link_trace b)
              | Vl_cstr c -> case_trace c b link_trace
              | _ -> bot)
          | None -> bot
        in
        link check_match (Wvl_v (Vl_sh s))
    | Guard (ctx, t) ->
        let check_guard w =
          match unroll w with
          | Some v -> (
              match v with
              | Vl_exp ctx -> guard ctx (link_trace t)
              | Vl_sh s -> guard (Nv_sh s) (link_trace t)
              | _ -> bot)
          | None -> bot
        in
        link check_guard (Wvl_v (Vl_exp ctx))
  in
  link_trace

(** val read_trace : var -> (trace wvl -> trace) -> walue -> trace **)

let read_trace x k w =
  match unroll w with
  | Some v -> (
      match v with
      | Vl_exp ctx -> (
          match read_env ctx x with
          | Some (w, ctx) -> guard ctx (k w)
          | None -> bot)
      | Vl_sh s -> k (Wvl_v (Vl_sh (Read (s, x))))
      | _ -> bot)
  | None -> bot

(** val close_rec : loc -> (walue -> trace) -> walue -> trace **)

let close_rec l k w =
  match unroll w with Some v -> k (Wvl_recv (close_value 0 l v)) | None -> bot

(** val bd_trace : var -> walue -> (walue -> trace) -> walue -> trace **)

let bd_trace x w k ctx =
  match unroll ctx with
  | Some v -> (
      match v with
      | Vl_exp ctx -> k (Wvl_v (Vl_exp (Nv_bd (x, w, ctx))))
      | Vl_sh s -> k (Wvl_v (Vl_exp (Nv_bd (x, w, Nv_sh s))))
      | _ -> bot)
  | None -> bot

(** val clos_trace :
    var -> trace -> (walue -> trace) -> walue -> trace **)

let clos_trace x t k w =
  match unroll w with
  | Some v -> (
      match v with
      | Vl_exp ctx -> k (Wvl_v (Vl_clos (x, t, ctx)))
      | Vl_sh s -> k (Wvl_v (Vl_clos (x, t, Nv_sh s)))
      | _ -> bot)
  | None -> bot

(** val filter_env : (trace wvl -> trace) -> walue -> trace **)

let filter_env k w =
  match unroll w with
  | Some v -> (
      match v with
      | Vl_exp ctx -> k (Wvl_v (Vl_exp ctx))
      | Vl_sh s -> k (Wvl_v (Vl_exp (Nv_sh s)))
      | _ -> bot)
  | None -> bot

(** val linkF :
    (env -> (walue -> trace) -> walue -> trace) -> env -> (walue -> trace) ->
    walue -> trace **)

let linkF link ctx =
  let rec link_wvl k = function
    | Wvl_v v -> link_vl k v
    | Wvl_recv v ->
        let l = Pos.max (alloc_value v) (alloc_env ctx) in
        link_vl (close_rec l k) (open_loc_value 0 l v)
    | Wvl_bloc _ -> bot
    | Wvl_floc l -> k (Wvl_floc l)
  and link_vl k v =
    match v with
    | Vl_exp ctx' -> link_nv k ctx'
    | Vl_sh s -> link_shdw k s
    | Vl_clos (x, t, ctx') -> link_nv (clos_trace x t k) ctx'
    | Vl_cstr c ->
        let fold_arg =
          let rec fold_arg args k' =
            match args with
            | [] -> k (Wvl_v (Vl_cstr { cs_type = c.cs_type; cs_args = k' [] }))
            | hd :: tl ->
                let check_trace w = fold_arg tl (fun v -> k' (w :: v)) in
                link_wvl check_trace hd
          in
          fold_arg
        in
        fold_arg c.cs_args id
  and link_nv k ctx' =
    match ctx' with
    | Nv_mt -> k (Wvl_v (Vl_exp Nv_mt))
    | Nv_sh s -> link_shdw (filter_env k) s
    | Nv_bd (x, w, ctx') ->
        let check_bound w' = link_nv (bd_trace x w' k) ctx' in
        link_wvl check_bound w
  and link_shdw k s =
    match s with
    | Init -> k (Wvl_v (Vl_exp ctx))
    | Read (s, x) -> link_shdw (read_trace x k) s
    | Call (s, w) ->
        let check_fn fn =
          match unroll fn with
          | Some v -> (
              match v with
              | Vl_sh s ->
                  let check_arg arg = k (Wvl_v (Vl_sh (Call (s, arg)))) in
                  link_wvl check_arg w
              | Vl_clos (x, t, ctx) ->
                  let check_arg arg =
                    let ctx' = Nv_bd (x, arg, ctx) in
                    link_trace (link ctx') k t
                  in
                  link_wvl check_arg w
              | _ -> bot)
          | None -> bot
        in
        link_shdw check_fn s
    | Dstr (s, d) -> link_shdw (dstr_trace d k) s
  in
  link_wvl

(** val link : int -> env -> (walue -> trace) -> walue -> trace **)

let rec link n ctx = if n <= 0 then fun _ _ -> bot else linkF (link (n - 1)) ctx
