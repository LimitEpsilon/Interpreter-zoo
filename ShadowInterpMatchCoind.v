From Coq Require Import PArith Arith Lia String List.
Import ListNotations.

Local Open Scope string_scope.
Local Unset Elimination Schemes.
Local Set Primitive Projections.

Definition var := string.
Definition loc := positive.

Inductive tm :=
  | Var (x : var)
  | Fn (x : var) (e : tm) (* λ x . e *)
  | App (f a : tm)
  | Link (m e : tm) (* m ⋊ e *)
  | Mt (* ε *)
  | Bind (x : var) (v m : tm) (* let rec x = v ; m *)
  | Zero (* O *)
  | Succ (n : tm) (* S n *)
  | Case (e : tm) (z : tm) (n : var) (s : tm)
    (* match e with 0 => z | S n => s end *)
.

Inductive shdw {wvl} :=
  | Init
  | Read (s : shdw) (x : var)
  | Call (s : shdw) (w : wvl)
  | SuccS (s : shdw)
  | PredS (s : shdw)
.

Arguments shdw : clear implicits.

Definition predS {wvl} (s : shdw wvl) :=
  match s with
  | Init | Read _ _ | Call _ _ | PredS _ => PredS s
  | SuccS s => s
  end.

Inductive nv {wvl} :=
  | nv_mt (* • *)
  | nv_sh (s : shdw wvl) (* [s] *)
  | nv_bd (x : var) (w : wvl) (σ : nv) (* bound value *)
.

Arguments nv : clear implicits.

Inductive vl {wvl K} :=
  | vl_exp (σ : nv wvl)
  | vl_sh (s : shdw wvl) (* s *)
  | vl_clos (x : var) (k : K) (σ : nv wvl)
  | vl_nat (n : nat)
.

Arguments vl : clear implicits.

Inductive wvl {K} :=
  | wvl_v (v : vl wvl K) (* v *)
  | wvl_recv (v : vl wvl K) (* μ.v *)
  | wvl_bloc (n : nat) (* bound location *)
  | wvl_floc (ℓ : loc) (* free location *)
.

Arguments wvl : clear implicits.

Variant traceF {trace} :=
  | Error
  | Wal (w : wvl trace)
  | Match (s : shdw (wvl trace)) (zt : trace) (st : trace)
  | Guard (σ : nv (wvl trace)) (t : trace)
.

Arguments traceF : clear implicits.

CoInductive trace := mkTrace { _obs_tr : traceF trace }.

Definition walue := wvl trace.
Definition value := vl walue trace.
Definition shadow := shdw walue.
Definition env := nv walue.

Notation obs_tr t := (_obs_tr t) (only parsing).
Notation error := (mkTrace Error) (only parsing).
Notation wal w := (mkTrace (Wal w)) (only parsing).
Notation case s zt st := (mkTrace (Match s zt st)) (only parsing).
Notation guard σ t := (mkTrace (Guard σ t)) (only parsing).

Section PRE_VAL_IND.
  Context {K : Type}.
  Context (Pwvl : wvl K -> Prop) (Pnv : nv (wvl K) -> Prop) (Pvl : vl (wvl K) K -> Prop) (Pshdw : shdw (wvl K) -> Prop).
  Context (Pwvl_v : forall v, Pvl v -> Pwvl (wvl_v v))
          (Pwvl_recv : forall v, Pvl v -> Pwvl (wvl_recv v))
          (Pwvl_bloc : forall n, Pwvl (wvl_bloc n))
          (Pwvl_floc : forall ℓ, Pwvl (wvl_floc ℓ)).
  Context (Pnv_mt : Pnv nv_mt)
          (Pnv_sh : forall s, Pshdw s -> Pnv (nv_sh s))
          (Pnv_bd : forall x w σ, Pwvl w -> Pnv σ -> Pnv (nv_bd x w σ)).
  Context (Pvl_exp : forall σ, Pnv σ -> Pvl (vl_exp σ))
          (Pvl_sh : forall s, Pshdw s -> Pvl (vl_sh s))
          (Pvl_clos : forall x k σ, Pnv σ -> Pvl (vl_clos x k σ))
          (Pvl_nat : forall n, Pvl (vl_nat n)).
  Context (PInit : Pshdw Init)
          (PRead : forall s x, Pshdw s -> Pshdw (Read s x))
          (PCall : forall s w, Pshdw s -> Pwvl w -> Pshdw (Call s w))
          (PSucc : forall s, Pshdw s -> Pshdw (SuccS s))
          (PPred : forall s, Pshdw s -> Pshdw (PredS s)).

  Definition shdw_ind wvl_ind :=
    fix shdw_ind s : Pshdw s :=
    match s with
    | Init => PInit
    | Read s x => PRead s x (shdw_ind s)
    | Call s w => PCall s w (shdw_ind s) (wvl_ind w)
    | SuccS s => PSucc s (shdw_ind s)
    | PredS s => PPred s (shdw_ind s)
    end.

  Definition nv_ind wvl_ind :=
    fix nv_ind σ : Pnv σ :=
    match σ with
    | nv_mt => Pnv_mt
    | nv_sh s => Pnv_sh s (shdw_ind wvl_ind s)
    | nv_bd x w σ => Pnv_bd x w σ (wvl_ind w) (nv_ind σ)
    end.

  Definition vl_ind (wvl_ind : forall w, Pwvl w) : forall v, Pvl v.
  Proof.
    refine (
    let shdw_ind := shdw_ind wvl_ind in
    let nv_ind := nv_ind wvl_ind in
    fix vl_ind v :=
    match v with
    | vl_exp σ => Pvl_exp σ (nv_ind σ)
    | vl_sh s => Pvl_sh s (shdw_ind s)
    | vl_clos x k σ => Pvl_clos x k σ (nv_ind σ)
    | vl_nat n => Pvl_nat n
    end).
  Defined.

  Fixpoint wvl_ind w : Pwvl w :=
    match w with
    | wvl_v v => Pwvl_v v (vl_ind wvl_ind v)
    | wvl_recv v => Pwvl_recv v (vl_ind wvl_ind v)
    | wvl_bloc n => Pwvl_bloc n
    | wvl_floc ℓ => Pwvl_floc ℓ
    end.

  Lemma pre_val_ind :
    (forall w, Pwvl w) /\
    (forall σ, Pnv σ) /\
    (forall v, Pvl v) /\
    (forall s, Pshdw s).
  Proof.
    eauto using wvl_ind, (nv_ind wvl_ind), (vl_ind wvl_ind), (shdw_ind wvl_ind).
  Qed.
End PRE_VAL_IND.

Module ValNotations.
(* Printing *)
  Notation " 'μ' v " := (wvl_recv v) (at level 60, right associativity, only printing).
  Notation " v " := (wvl_v v) (at level 60, right associativity, only printing).
  Notation " n " := (wvl_bloc n) (at level 60, right associativity, only printing).
  Notation " ℓ " := (wvl_floc ℓ) (at level 60, right associativity, only printing).

  Notation " s " := (vl_sh s) (at level 60, right associativity, only printing).
  Notation " σ " := (vl_exp σ) (at level 60, right associativity, only printing).
  Notation " n " := (vl_nat n) (at level 60, right associativity, only printing).
  Notation "'⟨' 'λ' x k σ '⟩'" := (vl_clos x k σ) (at level 60, right associativity, only printing).

  Notation "•" := (nv_mt) (at level 60, right associativity, only printing).
  Notation "'⟪' s '⟫'" := (nv_sh s) (at level 60, right associativity, only printing).
  Notation "'⟪' x ',' w '⟫' ';;' σ " := (nv_bd x w σ) (at level 60, right associativity, only printing).

  Notation "⊥" := (Error) (at level 60, right associativity, only printing).
  Notation "w" := (Wal w) (at level 60, right associativity, only printing).
  Notation "s '→' b" := (Match s b) (at level 60, right associativity, only printing).
  Notation "σ '→' t" := (Guard σ t) (at level 60, right associativity, only printing).
End ValNotations.

(** Operations for substitution *)
(* open the bound location i with ℓ *)
Definition open_loc_shdw f (i : nat) (ℓ : loc) :=
  fix open (s : shadow) : shadow :=
  match s with
  | Init => Init
  | Read s x => Read (open s) x
  | Call s w => Call (open s) (f i ℓ w)
  | SuccS s => SuccS (open s)
  | PredS s => PredS (open s)
  end.

Definition open_loc_nv f (i : nat) (ℓ : loc) :=
  fix open (σ : env) :=
  match σ with
  | nv_mt => nv_mt
  | nv_sh s => nv_sh (open_loc_shdw f i ℓ s)
  | nv_bd x w σ' =>
    nv_bd x (f i ℓ w) (open σ')
  end.

Definition open_loc_vl f (i : nat) (ℓ : loc) :=
  fix open (v : value) :=
  match v with
  | vl_exp σ => vl_exp (open_loc_nv f i ℓ σ)
  | vl_sh s => vl_sh (open_loc_shdw f i ℓ s)
  | vl_clos x k σ => vl_clos x k (open_loc_nv f i ℓ σ)
  | vl_nat n => vl_nat n
  end.

Fixpoint open_loc_walue (i : nat) (ℓ : loc) (w : walue) : walue :=
  let open_loc_vl := open_loc_vl open_loc_walue in
  let open_loc_shdw := open_loc_shdw open_loc_walue in
  match w with
  | wvl_v v => wvl_v (open_loc_vl i ℓ v)
  | wvl_recv v => wvl_recv (open_loc_vl (S i) ℓ v)
  | wvl_bloc n => if Nat.eqb i n then wvl_floc ℓ else wvl_bloc n
  | wvl_floc ℓ => wvl_floc ℓ
  end.

Definition open_loc_value := open_loc_vl open_loc_walue.
Definition open_loc_env := open_loc_nv open_loc_walue.
Definition open_loc_shadow := open_loc_shdw open_loc_walue.

(* close the free location ℓ with the binding depth i *)
Definition close_shdw f (i : nat) (ℓ : loc) :=
  fix close (s : shadow) : shadow :=
  match s with
  | Init => Init
  | Read s x => Read (close s) x
  | Call s w => Call (close s) (f i ℓ w)
  | SuccS s => SuccS (close s)
  | PredS s => PredS (close s)
  end.

Definition close_nv f (i : nat) (ℓ : loc) :=
  fix close (σ : env) : env :=
  match σ with
  | nv_mt => nv_mt
  | nv_sh s => nv_sh (close_shdw f i ℓ s)
  | nv_bd x w σ' =>
    nv_bd x (f i ℓ w) (close σ')
  end.

Definition close_vl f (i : nat) (ℓ : loc) :=
  fix close (v : value) : value :=
  match v with
  | vl_exp σ => vl_exp (close_nv f i ℓ σ)
  | vl_sh s => vl_sh (close_shdw f i ℓ s)
  | vl_clos x k σ => vl_clos x k (close_nv f i ℓ σ)
  | vl_nat n => vl_nat n
  end.

Fixpoint close_walue (i : nat) (ℓ : loc) (w : walue) : walue :=
  let close_vl := close_vl close_walue in
  let close_shdw := close_shdw close_walue in
  match w with
  | wvl_v v => wvl_v (close_vl i ℓ v)
  | wvl_recv v => wvl_recv (close_vl (S i) ℓ v)
  | wvl_bloc n => wvl_bloc n
  | wvl_floc ℓ' => if Pos.eqb ℓ ℓ' then wvl_bloc i else wvl_floc ℓ'
  end.

Definition close_value := close_vl close_walue.
Definition close_env := close_nv close_walue.
Definition close_shadow := close_shdw close_walue.

(* open the bound location i with u *)
Definition open_wvl_shdw f (i : nat) (u : walue) :=
  fix open (s : shadow) : shadow :=
  match s with
  | Init => Init
  | Read s x => Read (open s) x
  | Call s w => Call (open s) (f i u w)
  | SuccS s => SuccS (open s)
  | PredS s => PredS (open s)
  end.

Definition open_wvl_nv f (i : nat) (u : walue) :=
  fix open (σ : env) :=
  match σ with
  | nv_mt => nv_mt
  | nv_sh s => nv_sh (open_wvl_shdw f i u s)
  | nv_bd x w σ' =>
    nv_bd x (f i u w) (open σ')
  end.

Definition open_wvl_vl f (i : nat) (u : walue) :=
  fix open (v : value) :=
  match v with
  | vl_exp σ => vl_exp (open_wvl_nv f i u σ)
  | vl_sh s => vl_sh (open_wvl_shdw f i u s)
  | vl_clos x k σ => vl_clos x k (open_wvl_nv f i u σ)
  | vl_nat n => vl_nat n
  end.

Fixpoint open_wvl_walue (i : nat) (u : walue) (w : walue) : walue :=
  let open_wvl_vl := open_wvl_vl open_wvl_walue in
  let open_wvl_shdw := open_wvl_shdw open_wvl_walue in
  match w with
  | wvl_v v => wvl_v (open_wvl_vl i u v)
  | wvl_recv v => wvl_recv (open_wvl_vl (S i) u v)
  | wvl_bloc n => if Nat.eqb i n then u else wvl_bloc n
  | wvl_floc ℓ => wvl_floc ℓ
  end.

Definition open_wvl_value := open_wvl_vl open_wvl_walue.
Definition open_wvl_env := open_wvl_nv open_wvl_walue.
Definition open_wvl_shadow := open_wvl_shdw open_wvl_walue.

(* allocate fresh locations *)
Definition alloc_shdw f :=
  fix alloc (s : shadow) : positive :=
  match s with
  | Init => xH
  | Read s x => alloc s
  | Call s w => Pos.max (alloc s) (f w)
  | SuccS s => alloc s
  | PredS s => alloc s
  end.

Definition alloc_nv f :=
  fix alloc (σ : env) : positive :=
  match σ with
  | nv_mt => xH
  | nv_sh s => alloc_shdw f s
  | nv_bd _ w σ' => Pos.max (f w) (alloc σ')
  end.

Definition alloc_vl f :=
  fix alloc (v : value) : positive :=
  match v with
  | vl_exp σ | vl_clos _ _ σ => alloc_nv f σ
  | vl_sh s => alloc_shdw f s
  | vl_nat n => xH
  end.

Fixpoint alloc_walue (w : walue) : positive :=
  let alloc_vl := alloc_vl alloc_walue in
  let alloc_shdw := alloc_shdw alloc_walue in
  match w with
  | wvl_v v | wvl_recv v => alloc_vl v
  | wvl_bloc _ => 1
  | wvl_floc ℓ => Pos.succ ℓ
  end%positive.

Definition alloc_value := alloc_vl alloc_walue.
Definition alloc_env := alloc_nv alloc_walue.
Definition alloc_shadow := alloc_shdw alloc_walue.

(* term size *)
Definition size_shdw f :=
  fix size (s : shadow) :=
  match s with
  | Init => O
  | Read s x => S (size s)
  | Call s w => S (Nat.max (size s) (f w))
  | SuccS s => S (size s)
  | PredS s => S (size s)
  end.

Definition size_nv f :=
  fix size (σ : env) :=
  match σ with
  | nv_mt => O
  | nv_sh s => S (size_shdw f s)
  | nv_bd _ w σ' => S (Nat.max (f w) (size σ'))
  end.

Definition size_vl f :=
  fix size (v : value) :=
  match v with
  | vl_exp σ | vl_clos _ _ σ => S (size_nv f σ)
  | vl_sh s => S (size_shdw f s)
  | vl_nat _ => O
  end.

Fixpoint size_walue (w : walue) :=
  let size_vl := size_vl size_walue in
  let size_shdw := size_shdw size_walue in
  match w with
  | wvl_v v | wvl_recv v => S (size_vl v)
  | wvl_bloc _ | wvl_floc _ => O
  end.

Definition size_value := size_vl size_walue.
Definition size_env := size_nv size_walue.
Definition size_shadow := size_shdw size_walue.

Definition open_loc_size_eq_wvl w :=
  forall n ℓ, size_walue w = size_walue (open_loc_walue n ℓ w).
Definition open_loc_size_eq_nv σ :=
  forall n ℓ, size_env σ = size_env (open_loc_env n ℓ σ).
Definition open_loc_size_eq_vl v :=
  forall n ℓ, size_value v = size_value (open_loc_value n ℓ v).
Definition open_loc_size_eq_shdw s :=
  forall n ℓ, size_shadow s = size_shadow (open_loc_shadow n ℓ s).

Lemma open_loc_size_eq :
  (forall w, open_loc_size_eq_wvl w) /\
  (forall σ, open_loc_size_eq_nv σ) /\
  (forall v, open_loc_size_eq_vl v) /\
  (forall s, open_loc_size_eq_shdw s).
Proof.
  apply pre_val_ind; repeat intro; simpl; auto.
  match goal with
  | |- context [Nat.eqb ?x ?y] => destruct (Nat.eqb x y)
  end; simpl; auto.
Qed.

Definition read_env (σ : env) (x : var) :=
  let fix read σ (acc : env -> env) :=
    match σ with
    | nv_mt => None
    | nv_sh s => Some (wvl_v (vl_sh (Read s x)), acc nv_mt)
    | nv_bd x' w' σ' =>
      if x =? x' then Some (w', acc σ') else
      let acc' σ' := acc (nv_bd x' w' σ')
      in read σ' acc'
    end
  in read σ id.

Definition unroll (w : walue) : option value :=
  match w with
  | wvl_v v => Some v
  | wvl_recv v => Some (open_wvl_value 0 w v)
  | wvl_bloc _ | wvl_floc _ => None
  end.

Definition bind (k : walue -> trace) : trace -> trace :=
  cofix bind_ t :=
    match obs_tr t with
    | Error => error
    | Wal w => k w
    | Match s zt st => case s (bind_ zt) (bind_ st)
    | Guard σ t => guard σ (bind_ t)
    end.

CoFixpoint link (σ0 : env) (t : trace) : trace.
Proof.
  destruct (obs_tr t); cycle 3.
  - pose (check_guard w :=
      match unroll w with
      | Some (vl_sh s) => guard (nv_sh s) (link σ0 t)
      | Some (vl_exp σ) => guard σ (link σ0 t)
      | _ => error
      end).
    refine (guard nv_mt (bind check_guard _)).
    refine (link σ0 _).
    Guarded.
:=
  match obs_tr t with
  | Error => error
  | Wal (wvl_v v) => wal (wvl_v v)
  | Wal (wvl_recv v) => wal (wvl_recv v)
  | Wal (wvl_bloc n) => error
  | Wal (wvl_floc ℓ) => wal (wvl_floc ℓ)
  | Match s zt st =>
    let check_match w :=
      match unroll w with
      | Some (vl_sh (SuccS s)) => guard nv_mt (link k σ0 st)
      | Some (vl_sh s) => case s (link k σ0 zt) (link k σ0 st)
      | Some (vl_nat O) => guard nv_mt (link k σ0 zt)
      | Some (vl_nat (S _)) => guard nv_mt (link k σ0 st)
      | _ => error
      end
    in link check_match σ0 (wal (wvl_v (vl_sh s)))
  | Guard σ t =>
    let check_guard w :=
      match unroll w with
      | Some (vl_sh s) => guard (nv_sh s) (link k σ0 t)
      | Some (vl_exp σ) => guard σ (link k σ0 t)
      | _ => error
      end
    in link check_guard σ0 (wal (wvl_v (vl_exp σ)))
  end.

Definition link_trace (link : walue -> trace) (k : walue -> trace) : trace -> trace :=
  cofix link_trace_ t :=
    match obs_tr t with
    | Error => error
    | Wal w => bind k (link w)
    | Match s zt st =>
      let check_match w :=
        match unroll w with
        | Some (vl_sh (SuccS s)) => guard nv_mt (link_trace_ st)
        | Some (vl_sh s) => case s (link_trace_ zt) (link_trace_ st)
        | Some (vl_nat O) => guard nv_mt (link_trace_ zt)
        | Some (vl_nat (S _)) => guard nv_mt (link_trace_ st)
        | _ => error
        end
      in bind check_match (link (wvl_v (vl_sh s)))
    | Guard σ t =>
      let check_guard w :=
        match unroll w with
        | Some (vl_sh s) => guard (nv_sh s) (link_trace_ t)
        | Some (vl_exp σ) => guard σ (link_trace_ t)
        | _ => error
        end
      in bind check_guard (link (wvl_v (vl_exp σ)))
    end.

Definition read_trace x :=
  let read w :=
    match unroll w with
    | Some (vl_sh s) => wal (wvl_v (vl_sh (Read s x)))
    | Some (vl_exp σ) =>
      match read_env σ x with
      | Some (w, σ) => guard σ (wal w)
      | None => error
      end
    | _ => error
    end
  in bind read.

Definition call_trace (link : env -> walue -> trace) (fn arg : trace) : trace :=
  let check_fn fn :=
    match unroll fn with
    | Some (vl_sh s) =>
      let check_arg arg := wal (wvl_v (vl_sh (Call s arg)))
      in bind check_arg arg
    | Some (vl_clos x t σ) =>
      let check_arg arg := link_trace (link (nv_bd x arg σ)) wal t
      in bind check_arg arg
    | _ => error
    end
  in bind check_fn fn.

Definition close_rec ℓ :=
  let close w :=
    match unroll w with
    | Some v => wal (wvl_recv (close_value 0 ℓ v))
    | None => error
    end
  in bind close.

Definition bd_trace x (w : trace) (σ : trace) :=
  let check_bd w :=
    let check_mod σ :=
      match unroll σ with
      | Some (vl_sh s) => wal (wvl_v (vl_exp (nv_bd x w (nv_sh s))))
      | Some (vl_exp σ) => wal (wvl_v (vl_exp (nv_bd x w σ)))
      | _ => error
      end
    in bind check_mod σ
  in bind check_bd w.

Definition clos_trace x t :=
  let clos w :=
    match unroll w with
    | Some (vl_sh s) => wal (wvl_v (vl_clos x t (nv_sh s)))
    | Some (vl_exp σ) => wal (wvl_v (vl_clos x t σ))
    | _ => error
    end
  in bind clos.

Definition filter_env :=
  let filter w :=
    match unroll w with
    | Some (vl_sh s) => wal (wvl_v (vl_exp (nv_sh s)))
    | Some (vl_exp σ) => wal (wvl_v (vl_exp σ))
    | _ => error
    end
  in bind filter.

Definition succ_trace :=
  let succ w :=
    match unroll w with
    | Some (vl_sh s) => wal (wvl_v (vl_sh (SuccS s)))
    | Some (vl_nat n) => wal (wvl_v (vl_nat (S n)))
    | _ => error
    end
  in bind succ.

Definition pred_trace :=
  let pred w :=
    match unroll w with
    | Some (vl_sh s) => wal (wvl_v (vl_sh (predS s)))
    | Some (vl_nat (S n)) => wal (wvl_v (vl_nat n))
    | _ => error
    end
  in bind pred.

Definition link_shdw (link : env -> walue -> trace) (σ0 : env) (s : shadow) : trace :=
  let link_shdw s := link σ0 (wvl_v (vl_sh s)) in
  let link_wvl w := link σ0 w in
  match s with
  | Init => wal (wvl_v (vl_exp σ0))
  | Read s x => read_trace x (link_shdw s)
  | Call s w => call_trace link (link_shdw s) (link_wvl w)
  | SuccS s => succ_trace (link_shdw s)
  | PredS s => pred_trace (link_shdw s)
  end.

Definition link_nv (link : env -> walue -> trace) (σ0 : env) (σ : env) : trace :=
  let link_shdw s := link_shdw link σ0 s in
  let link_nv σ := link σ0 (wvl_v (vl_exp σ)) in
  let link_wvl w := link σ0 w in
  match σ with
  | nv_mt => wal (wvl_v (vl_exp nv_mt))
  | nv_sh s => filter_env (link_shdw s)
  | nv_bd x w σ' => bd_trace x (link_wvl w) (link_nv σ')
  end.

Definition link_vl (link : env -> walue -> trace) (σ0 : env) v : trace :=
  let link_shdw s := link_shdw link σ0 s in
  let link_nv σ := link_nv link σ0 σ in
  match v with
  | vl_clos x t σ => clos_trace x t (link_nv σ)
  | vl_exp σ => link_nv σ
  | vl_sh s => link_shdw s
  | vl_nat n => wal (wvl_v (vl_nat n))
  end.

Definition link_wvl (link : env -> walue -> trace) (σ0 : env) w : trace :=
  let link_shdw s := link_shdw link σ0 s in
  let link_nv σ := link_nv link σ0 σ in
  let link_vl v := link_vl link σ0 v in
  match w with
  | wvl_v v => link_vl v
  | wvl_recv v =>
    let ℓ := Pos.max (alloc_value v) (alloc_env σ0) in
    close_rec ℓ (link_vl (open_loc_value 0 ℓ v))
  | wvl_bloc n => error
  | wvl_floc ℓ => wal (wvl_floc ℓ)
  end.

Local Unset Guard Checking.
CoFixpoint link := link_wvl link.
Local Set Guard Checking.

CoFixpoint link' (σ0 : env) (w : walue) : trace :=
  match w with
  | wvl_v v =>
    match v with
    | vl_clos x t σ =>
      match σ with
      | nv_mt => clos_trace x t (wal (wvl_v (vl_exp nv_mt)))
      | nv_sh s =>
        match s with
        | Init => clos_trace x t (wal (wvl_v (vl_exp σ0)))
        | Read s x =>
          read_trace x (guard nv_mt (link' σ0 (wvl_v (vl_sh s))))
        | Call s w =>
          call_trace link' (link' σ0 (wvl_v (vl_sh s))) (link' σ0 w)
        | SuccS s => succ_trace (link' σ0 (wvl_v (vl_sh s)))
        | PredS s => pred_trace (link' σ0 (wvl_v (vl_sh s)))
        end
      | nv_bd x w σ => bd_trace x (link' σ0 w) (link' σ0 (wvl_v (vl_exp σ)))
      end
    | vl_exp σ => error
    | vl_sh s => error
    | vl_nat n => error
    end
  | _ => error
  end.

Definition sem_link (link : env -> walue -> trace) (σ w : trace) :=
  let check_module m :=
    match unroll m with
    | Some (vl_sh s) => link_trace (link (nv_sh s)) wal w
    | Some (vl_exp σ) => link_trace (link σ) wal w
    | _ => error
    end
  in bind check_module σ.

(* precondition : bd, exp has no free locations *)
Definition sem_bind (link : env -> walue -> trace) x (bd exp : trace) :=
  let check_bd w :=
    match unroll w with
    | Some v =>
      let w := wvl_recv (close_value 0 xH v) in
      let check_exp σ :=
        match unroll σ with
        | Some (vl_sh s) => wal (wvl_v (vl_exp (nv_bd x w (nv_sh s))))
        | Some (vl_exp σ) => wal (wvl_v (vl_exp (nv_bd x w σ)))
        | _ => error
        end
      in link_trace (link (nv_bd x w (nv_sh Init))) check_exp exp
    | None => error
    end
  in link_trace (link (nv_bd x (wvl_floc xH) (nv_sh Init))) check_bd bd.

Definition sem_case (link : env -> walue -> trace) (m zt : trace) x (st : trace) :=
  let check_match m :=
    match unroll m with
    | Some (vl_sh (SuccS s)) =>
      link_trace (link (nv_bd x (wvl_v (vl_sh s)) (nv_sh Init))) wal st
    | Some (vl_sh s) =>
      let st := link_trace (link (nv_bd x (wvl_v (vl_sh (PredS s))) (nv_sh Init))) wal st in
      case s zt st
    | Some (vl_nat 0) => zt
    | Some (vl_nat (S n)) =>
      link_trace (link (nv_bd x (wvl_v (vl_nat n)) (nv_sh Init))) wal st
    | _ => error
    end
  in bind check_match m.

Definition eval (link : env -> walue -> trace) :=
  fix eval (e : tm) : trace :=
  match e with
  | Var x => wal (wvl_v (vl_sh (Read Init x)))
  | Fn x M => wal (wvl_v (vl_clos x (eval M) (nv_sh Init)))
  | App M N => call_trace link (eval M) (eval N)
  | Link M N => sem_link link (eval M) (eval N)
  | Mt => guard (nv_sh Init) (wal (wvl_v (vl_exp nv_mt)))
  | Bind x M N => sem_bind link x (eval M) (eval N)
  | Zero => wal (wvl_v (vl_nat 0))
  | Succ n => succ_trace (eval n)
  | Case m z x s => sem_case link (eval m) (eval z) x (eval s)
  end.

Definition interp := eval link.
Definition ω := Fn "x" (App (Var "x") (Var "x")).
Definition test :=
  Eval cbn in
    obs_tr (interp (App ω ω)).
Import ValNotations.
Print test.
(* examples *)
Fixpoint get_wal t :=
  match t with
  | Bot => []
  | Wal w => [w]
  | Match _ b =>
    let fold acc (b : cstr_type * trace) :=
      let (c, t) := b in get_wal t ++ acc
    in List.fold_left fold b nil
  | Guard _ t => get_wal t
  end%list.

Definition zero_tm c :=
  Cstr {|
    cs_type := {| cs_name := c; cs_arity := 0 |};
    cs_args := []%vec;
  |}.
Definition succ_tm t :=
  Cstr {|
    cs_type := {| cs_name := Succ; cs_arity := 1 |};
    cs_args := [t]%vec;
  |}.
Definition one_tm := succ_tm (zero_tm Zero).
Definition two_tm := succ_tm one_tm.
Definition three_tm := succ_tm two_tm.
(* Fixpoint add m n := match m with 0 => n | S m => S (add m n) end *)
Definition zero_branch (t : tm) :=
  {|
    br_cstr := {| cs_name := Zero; cs_arity := _ |};
    br_vars := []%vec;
    br_body := t
  |}.
Definition succ_branch x (t : tm) :=
  {|
    br_cstr := {| cs_name := Succ; cs_arity := _ |};
    br_vars := [x]%vec;
    br_body := t
  |}.

Module SimpleExamples.
Definition pred_tm :=
  Fn "n" (Case (Var "n") [zero_branch (zero_tm Zero); succ_branch "m" (Var "m")])
.

Definition add_tm :=
Link (Bind "+"
  (Fn "m"
    (Fn "n"
      (Case (Var "m")
        [zero_branch (Var "n");
        succ_branch "m" (succ_tm (App (App (Var "+") (Var "m")) (Var "n")))]
      )))
  Mt) (Var "+")
.

Definition mult_tm :=
Link (Bind "×"
  (Fn "m"
    (Fn "n"
      (Case (Var "m")
        [zero_branch (Var "m");
        succ_branch "m"
        (App
          (App add_tm (Var "n"))
          (App
            (App (Var "×") (Var "m"))
            (Var "n")))])))
  Mt) (Var "×")
.

Definition infinity :=
Link (Bind "n" (succ_tm (Var "n")) Mt)
  (Var "n").

Definition three_plus_three := App (App add_tm three_tm) three_tm.
Definition three_times_three := App (App mult_tm three_tm) three_tm.

Definition x_plus_three := App (App add_tm three_tm) (Var "x").

Definition double_x := App (App add_tm (Var "x")) (Var "x").

Compute get_wal (interp 5 three_plus_three).
Compute get_wal (interp 10 three_times_three).
Compute get_wal (interp 6 x_plus_three).
Compute get_wal (interp 6 double_x).
Compute get_wal (interp 6 (App pred_tm infinity)).

Compute get_wal (interp 100
  (App
    (App add_tm
      (App
        (App add_tm one_tm)
        two_tm))
    (Var "x"))).

Definition sum_tm :=
Link (Bind "Σ"
  (Fn "f"
    (Fn "n"
      (Case (Var "n")
        [zero_branch (App (Var "f") (zero_tm Zero));
        succ_branch "n"
        (App
          (App (Var "+") (App (Var "f") (succ_tm (Var "n"))))
          (App
            (App (Var "Σ") (Var "f"))
            (Var "n")))])))
  Mt) (Var "Σ").

Definition unknown_function :=
  App (App sum_tm (Var "f")) three_tm.

Compute interp 5 unknown_function.

Definition unknown_function_and_number :=
  App (App sum_tm (Var "f")) (Var "n").

Definition export_function_number :=
  Bind "f" (Fn "n" (App (App add_tm (Var "n")) one_tm))
    (Bind "n" three_tm
      (Bind "+" add_tm Mt)).

Definition export_function_number_sem :=
  Eval vm_compute in
  interp 4 export_function_number.

Definition unknown_function_and_number_sem :=
  Eval vm_compute in
  interp 10 unknown_function_and_number.

Compute get_wal (sem_link (link 10)
  export_function_number_sem
  unknown_function_and_number_sem).

Compute
  let l := get_wal (interp 10
    (Fn "n" (App (App add_tm (Var "n")) one_tm)))
  in
  let for_each w :=
    match w with
    | wvl_v (vl_clos _ k _) => get_wal k
    | _ => []
    end
  in List.map for_each l.

Definition ω := Fn "x" (App (Var "x") (Var "x")).
Definition bomb := Bind "w" ω Mt.
Definition bomber := Bind "div" (App (Var "w") (Var "w")) Mt.
Compute interp 10 (Link bomb (Link bomber Mt)).
Compute interp 10 (Link (Link bomb bomber) Mt).
End SimpleExamples.

Module MutExample.
(* even? n = 1 if n is even 0 if n is odd *)
Definition top_module :=
Bind "Top"
  (Bind "Even"
    (Bind "even?"
      (Fn "x"
        (Case (Var "x")
          [zero_branch one_tm;
          succ_branch "n" (App (Link (Var "Top") (Link (Var "Odd") (Var "odd?"))) (Var "n"))]
        ))
      Mt)
    (Bind "Odd"
      (Bind "odd?"
        (Fn "y"
          (Case (Var "y")
            [zero_branch (zero_tm Zero);
            succ_branch "n" (App (Link (Var "Top") (Link (Var "Even") (Var "even?"))) (Var "n"))]
          ))
        Mt)
      Mt))
  Mt.

Definition test_even :=
  Link top_module
    (Link (Var "Top") (Link (Var "Even") (Var "even?"))).
Definition test_odd :=
  Link top_module
    (Link (Var "Top") (Link (Var "Odd") (Var "odd?"))).

Definition test_num := succ_tm (three_tm).

Compute get_wal (interp 10 (App test_even test_num)).
Compute get_wal (interp 10 (App test_odd test_num)).
Eval vm_compute in
  let σ := interp 10 (Bind "n" test_num Mt) in
  let w := interp 10 (App test_odd (Var "n")) in
  get_wal (sem_link (link 10) σ w).
End MutExample.

