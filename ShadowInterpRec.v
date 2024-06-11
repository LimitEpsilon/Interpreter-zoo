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
  | Link (m e : tm)
  | Mt
  | Bind (x : var) (v m : tm)
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
  | vl_clos (x : var) (k : list vl) (σ : nv)

with shdw :=
  | Init
  | Read (s : shdw) (x : var)
  | Call (s : shdw) (v : vl)
.

Scheme wvl_ind_mut := Induction for wvl Sort Prop
with nv_ind_mut := Induction for nv Sort Prop
with vl_ind_mut := Induction for vl Sort Prop
with shdw_ind_mut := Induction for shdw Sort Prop.

Combined Scheme pre_val_ind from wvl_ind_mut, nv_ind_mut, vl_ind_mut, shdw_ind_mut.

Local Notation "'⟨' 'μ' v '⟩'" := (wvl_recv v) (at level 60, right associativity, only printing).
Local Notation "'⟨' 'λ' x k σ '⟩'" := (vl_clos x k σ) (at level 60, right associativity, only printing).
Local Notation "'⟨' σ '⟩'" := (vl_exp σ) (at level 60, right associativity, only printing).
Local Notation "'⟨' s '⟩'" := (vl_sh s) (at level 60, right associativity, only printing).
Local Notation "•" := (nv_mt) (at level 60, right associativity, only printing).
Local Notation "'⟪' s '⟫'" := (nv_sh s) (at level 60, right associativity, only printing).
Local Notation "'⟪' x ',' n '⟫' ';;' σ " := (nv_bloc x n σ) (at level 60, right associativity, only printing).
Local Notation "'⟪' x ',' 'ℓ' ℓ '⟫' ';;' σ " := (nv_floc x ℓ σ) (at level 60, right associativity, only printing).
Local Notation "'⟪' x ',' w '⟫' ';;' σ " := (nv_bval x w σ) (at level 60, right associativity, only printing).

Definition ω := Fn "x" (App (Var "x") (Var "x")).
Definition ι := Fn "x" (Var "x").
Definition α := Fn "f" (Fn "x" (App (Var "f") (Var "x"))).

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
  end

with open_loc_shdw (i : nat) (ℓ : loc) (s : shdw) :=
  match s with
  | Init => Init
  | Read s x => Read (open_loc_shdw i ℓ s) x
  | Call s v => Call (open_loc_shdw i ℓ s) (open_loc_vl i ℓ v)
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
  end

with close_shdw (i : nat) (ℓ : loc) (s : shdw) :=
  match s with
  | Init => Init
  | Read s x => Read (close_shdw i ℓ s) x
  | Call s v => Call (close_shdw i ℓ s) (close_vl i ℓ v)
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
  end

with open_wvl_shdw (i : nat) (u : wvl) (s : shdw) :=
  match s with
  | Init => Init
  | Read s x => Read (open_wvl_shdw i u s) x
  | Call s v => Call (open_wvl_shdw i u s) (open_wvl_vl i u v)
  end.

(* substitute the free location ℓ for ℓ' *)
Fixpoint subst_loc_wvl (ν ℓ : loc) (w : wvl) :=
  match w with
  | wvl_v v => wvl_v (subst_loc_vl ν ℓ v)
  | wvl_recv v => wvl_recv (subst_loc_vl ν ℓ v)
  end

with subst_loc_nv (ν ℓ : loc) (σ : nv) :=
  match σ with
  | nv_mt => nv_mt
  | nv_sh s => nv_sh (subst_loc_shdw ν ℓ s)
  | nv_bloc x n σ' =>
    nv_bloc x n (subst_loc_nv ν ℓ σ')
  | nv_floc x ℓ' σ' =>
    if Pos.eqb ℓ ℓ'
    then nv_floc x ν (subst_loc_nv ν ℓ σ')
    else nv_floc x ℓ' (subst_loc_nv ν ℓ σ')
  | nv_bval x w σ' =>
    nv_bval x (subst_loc_wvl ν ℓ w) (subst_loc_nv ν ℓ σ')
  end

with subst_loc_vl (ν ℓ : loc) (v : vl) :=
  match v with
  | vl_sh s => vl_sh (subst_loc_shdw ν ℓ s)
  | vl_exp σ => vl_exp (subst_loc_nv ν ℓ σ)
  | vl_clos x k σ => vl_clos x k (subst_loc_nv ν ℓ σ)
  end

with subst_loc_shdw (ν ℓ : loc) (s : shdw) :=
  match s with
  | Init => Init
  | Read s x => Read (subst_loc_shdw ν ℓ s) x
  | Call s v => Call (subst_loc_shdw ν ℓ s) (subst_loc_vl ν ℓ v)
  end.

(* substitute the free location ℓ for u *)
Fixpoint subst_wvl_wvl (u : wvl) (ℓ : loc) (w : wvl) :=
  match w with
  | wvl_v v => wvl_v (subst_wvl_vl u ℓ v)
  | wvl_recv v => wvl_recv (subst_wvl_vl u ℓ v)
  end

with subst_wvl_nv (u : wvl) (ℓ : loc) (σ : nv) :=
  match σ with
  | nv_mt => nv_mt
  | nv_sh s => nv_sh (subst_wvl_shdw u ℓ s)
  | nv_bloc x n σ' =>
    nv_bloc x n (subst_wvl_nv u ℓ σ')
  | nv_floc x ℓ' σ' =>
    if Pos.eqb ℓ ℓ'
    then nv_bval x u (subst_wvl_nv u ℓ σ')
    else nv_floc x ℓ' (subst_wvl_nv u ℓ σ')
  | nv_bval x w σ' =>
    nv_bval x (subst_wvl_wvl u ℓ w) (subst_wvl_nv u ℓ σ')
  end

with subst_wvl_vl (u : wvl) (ℓ : loc) (v : vl) :=
  match v with
  | vl_sh s => vl_sh (subst_wvl_shdw u ℓ s)
  | vl_exp σ => vl_exp (subst_wvl_nv u ℓ σ)
  | vl_clos x k σ => vl_clos x k (subst_wvl_nv u ℓ σ)
  end

with subst_wvl_shdw (u : wvl) (ℓ : loc) (s : shdw) :=
  match s with
  | Init => Init
  | Read s x => Read (subst_wvl_shdw u ℓ s) x
  | Call s v => Call (subst_wvl_shdw u ℓ s) (subst_wvl_vl u ℓ v)
  end.

(* free locations *)
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
  end

with alloc_shdw (s : shdw) :=
  match s with
  | Init => xH
  | Read s x => alloc_shdw s
  | Call s v => Pos.max (alloc_shdw s) (alloc_vl v)
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
  end

with size_shdw (s : shdw) :=
  match s with
  | Init => O
  | Read s x => S (size_shdw s)
  | Call s v => S (Nat.max (size_shdw s) (size_vl v))
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
Qed.

Fixpoint read_env (σ : nv) (x : var) :=
  match σ with
  | nv_mt => None
  | nv_sh s => Some (wvl_v (vl_sh s))
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

Definition eval (link : nv -> vl -> list vl) :=
  fix eval (e : tm) : list vl :=
  match e with
  | Var x => [vl_sh (Read Init x)]
  | Fn x M => [vl_clos x (eval M) (nv_sh Init)]
  | App M N =>
    let foldM acc fn :=
      let foldN acc' arg :=
        match fn with
        | vl_clos x B σ =>
          flat_map (link (nv_bval x (wvl_v arg) σ)) B ++ acc'
        | vl_sh fn =>
          vl_sh (Call fn arg) :: acc'
        | vl_exp _ => acc'
        end
      in fold_left foldN (eval N) acc
    in fold_left foldM (eval M) []
  | Link M N =>
    let foldM acc m :=
      let foldN acc' cli :=
        match m with
        | vl_exp σ =>
          link σ cli ++ acc'
        | vl_sh m =>
          link (nv_sh m) cli ++ acc'
        | vl_clos _ _ _ => acc'
        end
      in fold_left foldN (eval N) acc
    in fold_left foldM (eval M) []
  | Mt => [vl_exp nv_mt]
  | Bind x M N =>
    let foldM acc v :=
      let w := wvl_recv (close_vl 0 xH v) in
      let foldN acc' m :=
        match m with
        | vl_exp σ => vl_exp (nv_bval x w σ) :: acc'
        | vl_sh s => vl_exp (nv_bval x w (nv_sh s)) :: acc'
        | vl_clos _ _ _ => acc'
        end
      in fold_left foldN (flat_map (link (nv_bval x w (nv_sh Init))) (eval N)) acc
    in fold_left foldM (flat_map (link (nv_floc x xH (nv_sh Init))) (eval M)) []
  end%list.

Ltac t :=
  repeat match goal with
  | _ => solve [auto | lia]
  | _ => progress simpl
  | RR : ?x = _ |- _ < _ ?x => rewrite RR
  | |- context [size_vl (open_loc_vl ?n ?ℓ ?v)] =>
    replace (size_vl (open_loc_vl n ℓ v)) with (size_vl v);
    [|eapply open_loc_size_eq]
  end.

(* linking, up to n steps *)
Fixpoint link (n : nat) (σ : nv) : vl -> list vl.
Proof.
  refine (
  match n with 0 => (fun _ => []) | S n =>
  let go :=
  fix link_wvl w (ACC : Acc lt (size_wvl w)) {struct ACC} : list wvl :=
    match w as w' return w = w' -> _ with
    | wvl_v v => fun _ => map wvl_v (link_vl v (Acc_inv ACC _))
    | wvl_recv v =>
      fun _ =>
      let ℓ := alloc_vl v in
      let recv v := wvl_recv (close_vl 0 ℓ v) in
      map recv (link_vl (open_loc_vl 0 ℓ v) (Acc_inv ACC _))
    end eq_refl
  with link_vl v (ACC : Acc lt (size_vl v)) {struct ACC} : list vl :=
    match v as v' return v = v' -> _ with
    | vl_clos x k σ' => fun _ => map (vl_clos x k) (link_nv σ' (Acc_inv ACC _))
    | vl_exp σ' => fun _ => map vl_exp (link_nv σ' (Acc_inv ACC _))
    | vl_sh s => fun _ => link_shdw s (Acc_inv ACC _)
    end eq_refl
  with link_nv σ' (ACC : Acc lt (size_nv σ')) {struct ACC} : list nv :=
    match σ' as σ'' return σ' = σ'' -> _ with
    | nv_mt => fun _ => [nv_mt]
    | nv_sh s =>
      fun _ =>
      let folds acc v :=
        match v with
        | vl_exp σ' => σ' :: acc
        | vl_sh s' => nv_sh s' :: acc
        | vl_clos _ _ _ => acc
        end
      in fold_left folds (link_shdw s (Acc_inv ACC _)) []
    | nv_bloc _ _ _ => (* unreachable *) fun _ => []
    | nv_floc x ℓ σ' => fun _ => map (nv_floc x ℓ) (link_nv σ' (Acc_inv ACC _))
    | nv_bval x w σ' =>
      fun _ =>
      let foldw acc w :=
        let foldσ acc' σ' := nv_bval x w σ' :: acc'
        in fold_left foldσ (link_nv σ' (Acc_inv ACC _)) acc
      in fold_left foldw (link_wvl w (Acc_inv ACC _)) []
    end eq_refl
  with link_shdw s (ACC : Acc lt (size_shdw s)) {struct ACC} : list vl :=
    match s as s' return s = s' -> _ with
    | Init => fun _ => [vl_exp σ]
    | Read s x =>
      fun _ =>
      let folds acc s :=
        match s with
        | vl_exp σ =>
          match read_env σ x with
          | None => acc
          | Some w => (unroll w) :: acc
          end
        | vl_sh s => vl_sh (Read s x) :: acc
        | vl_clos _ _ _ => acc
        end
      in fold_left folds (link_shdw s (Acc_inv ACC _)) []
    | Call s v =>
      fun _ =>
      let folds acc s :=
        let foldv acc' v :=
          match s with
          | vl_clos x k σ =>
            flat_map (link n (nv_bval x (wvl_v v) σ)) k ++ acc'
          | vl_sh s =>
            vl_sh (Call s v) :: acc'
          | vl_exp _ => acc'
          end
        in fold_left foldv (link_vl v (Acc_inv ACC _)) acc
      in fold_left folds (link_shdw s (Acc_inv ACC _)) []
    end eq_refl
  for link_vl
  in fun v => go v (lt_wf (size_vl v))
  end%list).
  Unshelve.
  all: try abstract t.
  all: abstract t.
Defined.

Definition interp n := eval (link n).

Local Coercion wvl_v : vl >-> wvl.
Local Coercion vl_sh : shdw >-> vl.
Local Coercion vl_exp : nv >-> vl.
Compute interp 1 ω.
Compute interp 100 (App ω ω).
Compute interp 1 (App ι ι).
Definition test_module := Bind "app" α (Bind "id" ι Mt).
Definition open1 := App (Var "id") (Var "id").
Definition open2 := App (Var "app") (Var "id").
Definition compute_in_fun1 := Fn "x" (App (App ι ι) (Var "x")).
Definition compute_in_fun2 := Fn "x" (App ι (App ι (Var "x"))).
Compute interp 2 (Link test_module open1).
Compute interp 2 (Link test_module open2).
Compute interp 1 compute_in_fun1.
Compute interp 1 compute_in_fun2.

Definition bomb := Bind "w" ω Mt.
Definition bomber := Bind "div" (App (Var "w") (Var "w")) Mt.
Compute interp 1 (Link bomb (Link bomber Mt)).
Compute interp 100 (Link (Link bomb bomber) Mt).

