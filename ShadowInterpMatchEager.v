From Coq Require Import PArith Arith Lia String List.
Import ListNotations.

Local Open Scope string_scope.
Unset Elimination Schemes.

Definition var := string.
Definition loc := positive.

Inductive tm :=
  | Var (x : var)
  | Fn (x : var) (e : tm)
  | App (f a : tm)
  | Link (m e : tm) (* m ⋊ e *)
  | Mt (* ε *)
  | Bind (x : var) (v m : tm) (* let rec x = v ; m *)
  | Zero (* new! *)
  | Succ (n : tm) (* new! *)
  | Case (e : tm) (z : tm) (n : var) (s : tm) (* new! *)
    (* match e with 0 => z | S n => s end *)
.

Inductive wvl :=
  | wvl_v (v : vl) (* v *)
  | wvl_recv (v : vl) (* μ.v *)

with nv :=
  | nv_mt (* • *)
  | nv_sh (s : shdw) (* [s] *)
  | nv_bloc (x : var) (n : nat) (σ : nv) (* bound location *)
  | nv_floc (x : var) (ℓ : loc) (σ : nv) (* free location *)
  | nv_bval (x : var) (w : wvl) (σ : nv) (* bound value *)

with vl :=
  | vl_sh (s : shdw)
  | vl_exp (σ : nv)
  | vl_clos (x : var) (k : option vl) (σ : nv)
  | vl_nat (n : nat) (* new! *)

with shdw :=
  | Init
  | Read (s : shdw) (x : var)
  | Call (s : shdw) (v : vl)
  | SuccS (s : shdw) (* new! *)
  | PredS (s : shdw) (* new! *)
  | CaseS (s : shdw) (vO vS : option vl) (* new! *)
.

Section IND.
  Context (Pwvl : wvl -> Prop) (Pnv : nv -> Prop) (Pvl : vl -> Prop) (Pshdw : shdw -> Prop).
  Context (Pwvl_v : forall v, Pvl v -> Pwvl (wvl_v v))
          (Pwvl_recv : forall v, Pvl v -> Pwvl (wvl_recv v)).
  Context (Pnv_mt : Pnv nv_mt)
          (Pnv_sh : forall s, Pshdw s -> Pnv (nv_sh s))
          (Pnv_bloc : forall x n σ, Pnv σ -> Pnv (nv_bloc x n σ))
          (Pnv_floc : forall x ℓ σ, Pnv σ -> Pnv (nv_floc x ℓ σ))
          (Pnv_bval : forall x w σ, Pwvl w -> Pnv σ -> Pnv (nv_bval x w σ)).
  Context (Pvl_sh : forall s, Pshdw s -> Pvl (vl_sh s))
          (Pvl_exp : forall σ, Pnv σ -> Pvl (vl_exp σ))
          (Pvl_clos : forall x k σ, Pnv σ -> Pvl (vl_clos x k σ))
          (Pvl_nat : forall n, Pvl (vl_nat n)).
  Context (PInit : Pshdw Init)
          (PRead : forall s x, Pshdw s -> Pshdw (Read s x))
          (PCall : forall s v, Pshdw s -> Pvl v -> Pshdw (Call s v))
          (PSuccS : forall s, Pshdw s -> Pshdw (SuccS s))
          (PPredS : forall s, Pshdw s -> Pshdw (PredS s))
          (PCaseS : forall s vO vS, Pshdw s ->
            match vO with None => True | Some vO => Pvl vO end ->
            match vS with None => True | Some vS => Pvl vS end ->
            Pshdw (CaseS s vO vS)).

  Fixpoint wvl_ind w : Pwvl w :=
    match w with
    | wvl_v v => Pwvl_v v (vl_ind v)
    | wvl_recv v => Pwvl_recv v (vl_ind v)
    end
  with nv_ind σ : Pnv σ :=
    match σ with
    | nv_mt => Pnv_mt
    | nv_sh s => Pnv_sh s (shdw_ind s)
    | nv_bloc x n σ => Pnv_bloc x n σ (nv_ind σ)
    | nv_floc x ℓ σ => Pnv_floc x ℓ σ (nv_ind σ)
    | nv_bval x w σ => Pnv_bval x w σ (wvl_ind w) (nv_ind σ)
    end
  with vl_ind v : Pvl v :=
    match v with
    | vl_sh s => Pvl_sh s (shdw_ind s)
    | vl_exp σ => Pvl_exp σ (nv_ind σ)
    | vl_clos x k σ => Pvl_clos x k σ (nv_ind σ)
    | vl_nat n => Pvl_nat n
    end
  with shdw_ind s :=
    match s with
    | Init => PInit
    | Read s x => PRead s x (shdw_ind s)
    | Call s v => PCall s v (shdw_ind s) (vl_ind v)
    | SuccS s => PSuccS s (shdw_ind s)
    | PredS s => PPredS s (shdw_ind s)
    | CaseS s vO vS =>
      PCaseS s vO vS (shdw_ind s)
        (match vO with None => I | Some vO => vl_ind vO end)
        (match vS with None => I | Some vS => vl_ind vS end)
    end.

  Lemma pre_val_ind :
    (forall w, Pwvl w) /\
    (forall σ, Pnv σ) /\
    (forall v, Pvl v) /\
    (forall s, Pshdw s).
  Proof.
    eauto using wvl_ind, nv_ind, vl_ind, shdw_ind.
  Qed.
End IND.

Local Notation "'⟨' 'μ' v '⟩'" := (wvl_recv v) (at level 60, right associativity, only printing).
Local Notation "'⟨' 'λ' x k σ '⟩'" := (vl_clos x k σ) (at level 60, right associativity, only printing).
Local Notation "'⟨' s '⟩'" := (vl_sh s) (at level 60, right associativity, only printing).
Local Notation "'⟨' n '⟩'" := (vl_nat n) (at level 60, right associativity, only printing).
Local Notation "•" := (nv_mt) (at level 60, right associativity, only printing).
Local Notation "'⟪' s '⟫'" := (nv_sh s) (at level 60, right associativity, only printing).
Local Notation "'⟪' x ',' n '⟫' ';;' σ " := (nv_bloc x n σ) (at level 60, right associativity, only printing).
Local Notation "'⟪' x ',' 'ℓ' ℓ '⟫' ';;' σ " := (nv_floc x ℓ σ) (at level 60, right associativity, only printing).
Local Notation "'⟪' x ',' w '⟫' ';;' σ " := (nv_bval x w σ) (at level 60, right associativity, only printing).
Local Notation "'⟪' s '|' 'O' '⤇' vO '|' 'S' '⤇' vS '⟫'" := (CaseS s vO vS) (at level 60, right associativity, only printing).
Local Infix "<*>" := Basics.compose (at level 49).

(* Lifting from Reynolds, Theory of Programming Languages  *)
Definition lift {A B : Type} (f : A -> option B) (x : option A) :=
  match x with
  | None => None
  | Some x => f x
  end.

(** Operations for substitution *)
(* open the bound location i with ℓ *)
Fixpoint open_loc_wvl (i : nat) (ℓ : loc) (w : wvl) :=
  match w with
  | wvl_v v => wvl_v (open_loc_vl i ℓ v)
  | wvl_recv v => wvl_recv (open_loc_vl (S i) ℓ v)
  end

with open_loc_nv (i : nat) (ℓ : loc) (σ : nv) :=
  match σ with
  | nv_mt => nv_mt
  | nv_sh s => nv_sh (open_loc_shdw i ℓ s)
  | nv_bloc x n σ' =>
    if Nat.eqb i n
    then nv_floc x ℓ (open_loc_nv i ℓ σ')
    else nv_bloc x n (open_loc_nv i ℓ σ')
  | nv_floc x ℓ' σ' =>
    nv_floc x ℓ' (open_loc_nv i ℓ σ')
  | nv_bval x w σ' =>
    nv_bval x (open_loc_wvl i ℓ w) (open_loc_nv i ℓ σ')
  end

with open_loc_vl (i : nat) (ℓ : loc) (v : vl) :=
  match v with
  | vl_sh s => vl_sh (open_loc_shdw i ℓ s)
  | vl_exp σ => vl_exp (open_loc_nv i ℓ σ)
  | vl_clos x k σ => vl_clos x k (open_loc_nv i ℓ σ)
  | vl_nat n => vl_nat n
  end

with open_loc_shdw (i : nat) (ℓ : loc) (s : shdw) :=
  match s with
  | Init => Init
  | Read s x => Read (open_loc_shdw i ℓ s) x
  | Call s v => Call (open_loc_shdw i ℓ s) (open_loc_vl i ℓ v)
  | SuccS s => SuccS (open_loc_shdw i ℓ s)
  | PredS s => PredS (open_loc_shdw i ℓ s)
  | CaseS s vO vS =>
    CaseS (open_loc_shdw i ℓ s)
      (lift (Some <*> open_loc_vl i ℓ) vO)
      (lift (Some <*> open_loc_vl i ℓ) vS)
  end.

(* close the free location ℓ with the binding depth i *)
Fixpoint close_wvl (i : nat) (ℓ : loc) (w : wvl) :=
  match w with
  | wvl_v v => wvl_v (close_vl i ℓ v)
  | wvl_recv v => wvl_recv (close_vl (S i) ℓ v)
  end

with close_nv (i : nat) (ℓ : loc) (σ : nv) :=
  match σ with
  | nv_mt => nv_mt
  | nv_sh s => nv_sh (close_shdw i ℓ s)
  | nv_bloc x n σ' =>
    nv_bloc x n (close_nv i ℓ σ')
  | nv_floc x ℓ' σ' =>
    if Pos.eqb ℓ ℓ'
    then nv_bloc x i (close_nv i ℓ σ')
    else nv_floc x ℓ' (close_nv i ℓ σ')
  | nv_bval x w σ' =>
    nv_bval x (close_wvl i ℓ w) (close_nv i ℓ σ')
  end

with close_vl (i : nat) (ℓ : loc) (v : vl) :=
  match v with
  | vl_sh s => vl_sh (close_shdw i ℓ s)
  | vl_exp σ => vl_exp (close_nv i ℓ σ)
  | vl_clos x k σ => vl_clos x k (close_nv i ℓ σ)
  | vl_nat n => vl_nat n
  end

with close_shdw (i : nat) (ℓ : loc) (s : shdw) :=
  match s with
  | Init => Init
  | Read s x => Read (close_shdw i ℓ s) x
  | Call s v => Call (close_shdw i ℓ s) (close_vl i ℓ v)
  | SuccS s => SuccS (close_shdw i ℓ s)
  | PredS s => PredS (close_shdw i ℓ s)
  | CaseS s vO vS =>
    CaseS (close_shdw i ℓ s)
      (lift (Some <*> close_vl i ℓ) vO)
      (lift (Some <*> close_vl i ℓ) vS)
  end.

(* open the bound location i with u *)
Fixpoint open_wvl_wvl (i : nat) (u : wvl) (w : wvl) :=
  match w with
  | wvl_v v => wvl_v (open_wvl_vl i u v)
  | wvl_recv v => wvl_recv (open_wvl_vl (S i) u v)
  end

with open_wvl_nv (i : nat) (u : wvl) (σ : nv) :=
  match σ with
  | nv_mt => nv_mt
  | nv_sh s => nv_sh (open_wvl_shdw i u s)
  | nv_bloc x n σ' =>
    if Nat.eqb i n
    then nv_bval x u (open_wvl_nv i u σ')
    else nv_bloc x n (open_wvl_nv i u σ')
  | nv_floc x ℓ' σ' =>
    nv_floc x ℓ' (open_wvl_nv i u σ')
  | nv_bval x w σ' =>
    nv_bval x (open_wvl_wvl i u w) (open_wvl_nv i u σ')
  end

with open_wvl_vl (i : nat) (u : wvl) (v : vl) :=
  match v with
  | vl_sh s => vl_sh (open_wvl_shdw i u s)
  | vl_exp σ => vl_exp (open_wvl_nv i u σ)
  | vl_clos x k σ => vl_clos x k (open_wvl_nv i u σ)
  | vl_nat n => vl_nat n
  end

with open_wvl_shdw (i : nat) (u : wvl) (s : shdw) :=
  match s with
  | Init => Init
  | Read s x => Read (open_wvl_shdw i u s) x
  | Call s v => Call (open_wvl_shdw i u s) (open_wvl_vl i u v)
  | SuccS s => SuccS (open_wvl_shdw i u s)
  | PredS s => PredS (open_wvl_shdw i u s)
  | CaseS s vO vS =>
    CaseS (open_wvl_shdw i u s)
      (lift (Some <*> open_wvl_vl i u) vO)
      (lift (Some <*> open_wvl_vl i u) vS)
  end.

(* allocate fresh locations *)
Fixpoint alloc_wvl (w : wvl) :=
  match w with
  | wvl_v v | wvl_recv v => alloc_vl v
  end

with alloc_nv (σ : nv) :=
  match σ with
  | nv_mt => xH
  | nv_sh s => alloc_shdw s
  | nv_bloc _ _ σ' => alloc_nv σ'
  | nv_floc _ ℓ σ' => Pos.max ℓ (alloc_nv σ')
  | nv_bval _ w σ' => Pos.max (alloc_wvl w) (alloc_nv σ')
  end

with alloc_vl (v : vl) :=
  match v with
  | vl_sh s => alloc_shdw s
  | vl_exp σ | vl_clos _ _ σ => alloc_nv σ
  | vl_nat n => xH
  end

with alloc_shdw (s : shdw) :=
  match s with
  | Init => xH
  | Read s x => alloc_shdw s
  | Call s v => Pos.max (alloc_shdw s) (alloc_vl v)
  | SuccS s => alloc_shdw s
  | PredS s => alloc_shdw s
  | CaseS s vO vS =>
    let lift_alloc o := match o with None => xH | Some v => alloc_vl v end in
    Pos.max (alloc_shdw s) (Pos.max (lift_alloc vO) (lift_alloc vS))
  end.

(* term size *)
Fixpoint size_wvl (w : wvl) :=
  match w with
  | wvl_v v | wvl_recv v => S (size_vl v)
  end

with size_nv (σ : nv) :=
  match σ with
  | nv_mt => O
  | nv_sh s => S (size_shdw s)
  | nv_bloc _ _ σ' => S (size_nv σ')
  | nv_floc _ _ σ' => S (size_nv σ')
  | nv_bval _ w σ' => S (Nat.max (size_wvl w) (size_nv σ'))
  end

with size_vl (v : vl) :=
  match v with
  | vl_sh s => S (size_shdw s)
  | vl_exp σ | vl_clos _ _ σ => S (size_nv σ)
  | vl_nat _ => O
  end

with size_shdw (s : shdw) :=
  match s with
  | Init => O
  | Read s x => S (size_shdw s)
  | Call s v => S (Nat.max (size_shdw s) (size_vl v))
  | SuccS s => S (size_shdw s)
  | PredS s => S (size_shdw s)
  | CaseS s vO vS =>
    let lift_size o := match o with None => 0 | Some v => size_vl v end in
    S (Nat.max (size_shdw s) (Nat.max (lift_size vO) (lift_size vS)))
  end.

Definition open_loc_size_eq_wvl w :=
  forall n ℓ, size_wvl w = size_wvl (open_loc_wvl n ℓ w).
Definition open_loc_size_eq_nv σ :=
  forall n ℓ, size_nv σ = size_nv (open_loc_nv n ℓ σ).
Definition open_loc_size_eq_vl v :=
  forall n ℓ, size_vl v = size_vl (open_loc_vl n ℓ v).
Definition open_loc_size_eq_shdw s :=
  forall n ℓ, size_shdw s = size_shdw (open_loc_shdw n ℓ s).

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
  destruct vO, vS; simpl; auto.
Qed.

Fixpoint read_env (σ : nv) (x : var) :=
  match σ with
  | nv_mt => None
  | nv_sh s => Some (wvl_v (vl_sh (Read s x)))
  | nv_bloc x' _ σ' =>
    if x =? x' then None else read_env σ' x
  | nv_floc x' _ σ' =>
    if x =? x' then None else read_env σ' x
  | nv_bval x' w σ' =>
    if x =? x' then Some w else read_env σ' x
  end.

Definition unroll (w : wvl) :=
  match w with
  | wvl_v v => v
  | wvl_recv v => open_wvl_vl 0 w v
  end.

Definition eval (link : nv -> vl -> option vl) :=
  fix eval (e : tm) : option vl :=
  match e with
  | Var x => Some (vl_sh (Read Init x))
  | Fn x M => Some (vl_clos x (eval M) (nv_sh Init))
  | App M N =>
    let foldM fn :=
      let foldN arg :=
        match fn with
        | vl_clos x B σ =>
          lift (link (nv_bval x (wvl_v arg) σ)) B
        | vl_sh (SuccS _) | vl_sh (PredS _) => None
        | vl_sh fn => Some (vl_sh (Call fn arg))
        | vl_exp _ | vl_nat _ => None
        end
      in lift foldN (eval N)
    in lift foldM (eval M)
  | Link M N =>
    let foldM m :=
      let foldN cli :=
        match m with
        | vl_exp σ => link σ cli
        | vl_sh (SuccS _) | vl_sh (PredS _) => None
        | vl_sh m => link (nv_sh m) cli
        | vl_clos _ _ _ | vl_nat _ => None
        end
      in lift foldN (eval N)
    in lift foldM (eval M)
  | Mt => Some (vl_exp nv_mt)
  | Bind x M N =>
    let foldM v :=
      let w := wvl_recv (close_vl 0 xH v) in
      let foldN m :=
        match m with
        | vl_exp σ => Some (vl_exp (nv_bval x w σ))
        | vl_sh (SuccS _) | vl_sh (PredS _) => None
        | vl_sh s => Some (vl_exp (nv_bval x w (nv_sh s)))
        | vl_clos _ _ _ | vl_nat _ => None
        end
      in lift foldN
        (lift (link (nv_bval x w (nv_sh Init))) (eval N))
    in lift foldM
      (lift (link (nv_floc x xH (nv_sh Init))) (eval M))
  | Zero => Some (vl_nat 0)
  | Succ N =>
    let foldN n :=
      match n with
      | vl_nat n => Some (vl_nat (S n))
      | vl_sh s => Some (vl_sh (SuccS s))
      | vl_exp _ | vl_clos _ _ _ => None
      end
    in lift foldN (eval N)
  | Case E M x N =>
    let foldE e :=
      match e with
      | vl_nat O => eval M
      | vl_nat (S n) =>
        lift (link (nv_bval x (wvl_v (vl_nat n)) (nv_sh Init))) (eval N)
      | vl_sh (SuccS s) =>
        lift (link (nv_bval x (wvl_v (vl_sh s)) (nv_sh Init))) (eval N)
      | vl_sh s =>
        let vO := eval M in
        let vS := lift (link (nv_bval x (wvl_v (vl_sh (PredS s))) (nv_sh Init))) (eval N) in
        match vO, vS with
        | None, None => None
        | vO, vS => Some (vl_sh (CaseS s vO vS))
        end
      | vl_exp _ | vl_clos _ _ _ => None
      end
    in lift foldE (eval E)
  end.

Ltac t :=
  repeat match goal with
  | _ => solve [auto | lia]
  | _ => progress simpl
  | RR : ?x = _ |- context [?x] => rewrite RR
  | |- context [size_vl (open_loc_vl ?n ?ℓ ?v)] =>
    replace (size_vl (open_loc_vl n ℓ v)) with (size_vl v);
    [|eapply open_loc_size_eq]
  end.

(* linking, up to n steps *)
Fixpoint link (n : nat) (σ : nv) : vl -> option vl.
Proof.
  refine (
  match n with 0 => (fun _ => None) | S n =>
  let go :=
  fix link_wvl w (ACC : Acc lt (size_wvl w)) {struct ACC} : option wvl :=
    match w as w' return w = w' -> _ with
    | wvl_v v => fun _ => lift (Some <*> wvl_v) (link_vl v (Acc_inv ACC _))
    | wvl_recv v =>
      fun _ =>
      let ℓ := alloc_vl v in
      let recv v := Some (wvl_recv (close_vl 0 ℓ v)) in
      lift recv (link_vl (open_loc_vl 0 ℓ v) (Acc_inv ACC _))
    end eq_refl
  with link_vl v (ACC : Acc lt (size_vl v)) {struct ACC} : option vl :=
    match v as v' return v = v' -> _ with
    | vl_clos x k σ' => fun _ => lift (Some <*> vl_clos x k) (link_nv σ' (Acc_inv ACC _))
    | vl_exp σ' => fun _ => lift (Some <*> vl_exp) (link_nv σ' (Acc_inv ACC _))
    | vl_sh s => fun _ => link_shdw s (Acc_inv ACC _)
    | vl_nat n => fun _ => Some (vl_nat n)
    end eq_refl
  with link_nv σ' (ACC : Acc lt (size_nv σ')) {struct ACC} : option nv :=
    match σ' as σ'' return σ' = σ'' -> _ with
    | nv_mt => fun _ => Some (nv_mt)
    | nv_sh s =>
      fun _ =>
      let folds v :=
        match v with
        | vl_exp σ' => Some σ'
        | vl_sh (SuccS _) | vl_sh (PredS _) => None
        | vl_sh s' => Some (nv_sh s')
        | vl_clos _ _ _ | vl_nat _ => None
        end
      in lift folds (link_shdw s (Acc_inv ACC _))
    | nv_bloc _ _ _ => (* unreachable *) fun _ => None
    | nv_floc x ℓ σ' => fun _ => lift (Some <*> nv_floc x ℓ) (link_nv σ' (Acc_inv ACC _))
    | nv_bval x w σ' =>
      fun _ =>
      let foldw w := lift (Some <*> nv_bval x w) (link_nv σ' (Acc_inv ACC _))
      in lift foldw (link_wvl w (Acc_inv ACC _))
    end eq_refl
  with link_shdw s (ACC : Acc lt (size_shdw s)) {struct ACC} : option vl :=
    match s as s' return s = s' -> _ with
    | Init => fun _ => Some (vl_exp σ)
    | Read s x =>
      fun _ =>
      let folds s :=
        match s with
        | vl_exp σ => lift (Some <*> unroll) (read_env σ x)
        | vl_sh (SuccS _) | vl_sh (PredS _) => None
        | vl_sh s => Some (vl_sh (Read s x))
        | vl_clos _ _ _ | vl_nat _ => None
        end
      in lift folds (link_shdw s (Acc_inv ACC _))
    | Call s v =>
      fun _ =>
      let folds s :=
        let foldv v :=
          match s with
          | vl_clos x k σ =>
            lift (link n (nv_bval x (wvl_v v) σ)) k
          | vl_sh (SuccS _) | vl_sh (PredS _) => None
          | vl_sh s => Some (vl_sh (Call s v))
          | vl_exp _ | vl_nat _ => None
          end
        in lift foldv (link_vl v (Acc_inv ACC _))
      in lift folds (link_shdw s (Acc_inv ACC _))
    | SuccS s =>
      fun _ =>
      let folds s :=
        match s with
        | vl_nat n => Some (vl_nat (S n))
        | vl_sh s => Some (vl_sh (SuccS s))
        | vl_exp _ | vl_clos _ _ _ => None
        end
      in lift folds (link_shdw s (Acc_inv ACC _))
    | PredS s =>
      fun _ =>
      let folds s :=
        match s with
        | vl_nat (S n) => Some (vl_nat n)
        | vl_sh (SuccS s) => Some (vl_sh s)
        | vl_sh s => Some (vl_sh (PredS s))
        | vl_nat O | vl_exp _ | vl_clos _ _ _ => None
        end
      in lift folds (link_shdw s (Acc_inv ACC _))
    | CaseS s vO vS =>
      fun _ =>
      let folds s :=
        let vO :=
          match vO as vO' return vO = vO' -> _ with
          | None => fun _ => None
          | Some vO => fun _ => link_vl vO (Acc_inv ACC _)
          end eq_refl in
        let vS :=
          match vS as vS' return vS = vS' -> _ with
          | None => fun _ => None
          | Some vS => fun _ => link_vl vS (Acc_inv ACC _)
          end eq_refl in
        match s with
        | vl_nat O => vO
        | vl_nat (S _) | vl_sh (SuccS _) => vS
        | vl_sh s => Some (vl_sh (CaseS s vO vS))
        | vl_exp _ | vl_clos _ _ _ => None
        end
      in lift folds (link_shdw s (Acc_inv ACC _))
    end eq_refl
  for link_vl
  in fun v => go v (lt_wf (size_vl v))
  end).
  Unshelve.
  all: try abstract t.
  all: abstract t.
Defined.

Definition interp n := eval (link n).

Local Coercion wvl_v : vl >-> wvl.
Local Coercion vl_exp : nv >-> vl.
Definition one_tm := Succ Zero.
Definition two_tm := Succ (Succ Zero).
Definition three_tm := Succ (Succ (Succ Zero)).
(* Fixpoint add m n := match m with 0 => n | S m => S (add m n) end *)
Definition add_tm :=
Link (Bind "+"
  (Fn "m"
    (Fn "n"
      (Case (Var "m")
        (Var "n")
        "m"
        (Succ (App (App (Var "+") (Var "m")) (Var "n"))))))
  Mt) (Var "+")
.

Definition three_plus_three := App (App add_tm three_tm) three_tm.

Definition x_plus_three := App (App add_tm three_tm) (Var "x").

Definition double_x := App (App add_tm (Var "x")) (Var "x").

Compute interp 5 three_plus_three.
Compute interp 6 x_plus_three.
Compute interp 6 double_x.
Compute interp 100
  (App
    (App add_tm
      (App
        (App add_tm one_tm)
        two_tm))
    (Var "x")).

Definition sum_tm :=
Link (Bind "Σ"
  (Fn "f"
    (Fn "n"
      (Case (Var "n")
        (App (Var "f") (Var "n"))
        "n"
        (App
          (App (Var "+") (App (Var "f") (Succ (Var "n"))))
          (App
            (App (Var "Σ") (Var "f"))
            (Var "n"))))))
  Mt) (Var "Σ").

Definition unknown_function :=
  App (App sum_tm (Var "f")) three_tm.

Compute interp 5 unknown_function.

Definition unknown_function_and_number :=
  App (App sum_tm (Var "f")) (Var "n").

Compute interp 5 unknown_function_and_number.

Definition unknown_function_and_number_sem :=
  Eval vm_compute in
  interp 5 (App (App sum_tm (Var "f")) (Var "n")).

Print unknown_function_and_number_sem.

Definition sem_link n (σ : option nv) (v : option vl) :=
  match σ with
  | None => None
  | Some σ => lift (link n σ) v
  end.

Compute sem_link 5 (Some (nv_bval "n" (wvl_v (vl_nat 3)) (nv_sh Init)))
  unknown_function_and_number_sem.

Compute interp 100
  (Link (Bind "+" add_tm (Bind "n" three_tm (Bind "f" (Fn "x" (Var "x")) Mt)))
        unknown_function_and_number).

