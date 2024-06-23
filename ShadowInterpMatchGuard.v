From Coq Require Import PArith Arith Lia String List.
Import ListNotations.

Local Open Scope string_scope.
Unset Elimination Schemes.
Set Primitive Projections.

Definition var := string.
Definition loc := positive.

(* length-indexed list *)
Inductive vec {A : Type} : nat -> Type :=
  | vnil : vec 0
  | vcons {n} (hd : A) (tl : vec n) : vec (S n)
.

Section VEC_IND.
  Context {A : Type}.
  Context (P : forall n, @vec A n -> Prop).
  Context (Pnil : P 0 vnil)
          (Pcons : forall n hd tl (IHtl : P n tl), P (S n) (vcons hd tl)).

  Fixpoint vec_ind {n} (v : @vec A n) : P n v :=
    match v as v' in vec n' return P n' v' with
    | vnil => Pnil
    | @vcons _ n' hd tl => Pcons n' hd tl (vec_ind tl)
    end.
End VEC_IND.

Declare Scope vec_scope.
Delimit Scope vec_scope with vec.
Infix "::" := vcons.
Notation "[ ]" := vnil (format "[ ]") : vec_scope.
Notation "[ x ]" := (vcons x vnil) : vec_scope.
Notation "[ x ; y ; .. ; z ]" := (vcons x (vcons y .. (vcons z vnil) ..)) : vec_scope.

Arguments vec : clear implicits.

Fixpoint get_idx {A n} (l : vec A n) (i : nat) (pf : S i <= n) : A.
Proof.
  refine (
    match l in vec _ n' return S i <= n' -> A with
    | [] => _
    | hd :: tl => _
    end%vec pf
  ); intro LE.
  - exfalso. eapply Nat.nle_succ_0; eauto.
  - destruct i.
    + exact hd.
    + refine (get_idx A _ tl i _).
      apply le_S_n; assumption.
Defined.

Definition fold_vec {A B} (f : A -> B -> A) :=
  fix fold {n} (l : vec B n) (acc : A) {struct l} : A :=
    match l with
    | [] => acc
    | hd :: tl => fold tl (f acc hd)
    end%vec.

Definition map_vec {A B} (f : A -> B) :=
  fix map {n} (l : vec A n) {struct l} : vec B n :=
    match l with
    | [] => []
    | hd :: tl => (f hd) :: (map tl)
    end%vec.

Definition In_vec {A} (x : A) :=
  fix In {n} (l : vec A n) {struct l} : Prop :=
    match l with
    | [] => False
    | hd :: tl => x = hd \/ In tl
    end%vec.

Fixpoint map_vec_In {A B n} (l : vec A n) (f : forall x, In_vec x l -> B) {struct l} : vec B n.
Proof.
  destruct l.
  - exact vnil.
  - apply vcons.
    + eapply (f hd _).
    + eapply (map_vec_In _ _ _ l _).
      Unshelve.
      simpl. left; reflexivity.
      intros. eapply f. simpl. eauto.
Defined.

Variant cstr_name : nat -> Type :=
  | Zero : cstr_name 0
  | Succ : cstr_name 1
  | Cons : cstr_name 2
.

Definition eqb_cstr {m n} (c1 : cstr_name m) (c2 : cstr_name n) :=
  match c1, c2 with
  | Zero, Zero | Succ, Succ | Cons, Cons => true
  | Zero, _ | Succ, _ | Cons, _ => false
  end.

Record cstr_type :=
  {
    cs_arity : nat;
    cs_name : cstr_name cs_arity;
  }.

Lemma eqb_cstr_eq (c1 c2 : cstr_type) :
  eqb_cstr c1.(cs_name) c2.(cs_name) = true <-> c1 = c2.
Proof.
  destruct c1, c2; simpl;
  match goal with
  | |- context [eqb_cstr ?x ?y] => destruct x, y
  end; simpl;
  split; intro EQ; inversion EQ; auto.
Qed.

Record cstr {V : Type} := mkCstr
  {
    cs_type : cstr_type;
    cs_args : vec V cs_type.(cs_arity);
  }.

Record dstr := mkDstr
  {
    ds_type : cstr_type;
    ds_idx : nat;
    ds_valid : S ds_idx <= ds_type.(cs_arity);
  }.

Record branch {B : Type} := mkBranch
  {
    br_cstr : cstr_type;
    br_vars : vec var br_cstr.(cs_arity);
    br_body : B;
  }.

Inductive tm :=
  | Var (x : var)
  | Fn (x : var) (e : tm) (* λ x . e *)
  | App (f a : tm)
  | Link (m e : tm) (* m ⋊ e *)
  | Mt (* ε *)
  | Bind (x : var) (v m : tm) (* let rec x = v ; m *)
  | Cstr (args : @cstr tm) (* C e1 e2 ... en *)
  | Case (e : tm) (b : list (@branch tm))
  (* match e with | C1 \vec{x1} => e1 | ... | Cn \vec{xn} => en end *)
.

Inductive shdw {wvl} :=
  | Init
  | Read (s : shdw) (x : var)
  | Call (s : shdw) (w : wvl)
  | Dstr (s : shdw) (d : dstr)
.

Arguments shdw : clear implicits.

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
  | vl_cstr (c : @cstr wvl)
.

Arguments vl : clear implicits.

Inductive wvl {K} :=
  | wvl_v (v : vl wvl K) (* v *)
  | wvl_recv (v : vl wvl K) (* μ.v *)
  | wvl_bloc (n : nat) (* bound location *)
  | wvl_floc (ℓ : loc) (* free location *)
.

Arguments wvl : clear implicits.

(* finite approximations *)
Inductive trace :=
  | Bot
  | Wal (w : wvl trace)
  | Match (s : shdw (wvl trace)) (b : list (cstr_type * trace))
  | Guard (σ : nv (wvl trace)) (t : trace)
.

(*
Variant traceF trace :=
  | Bot
  | Wal (w : wvl trace)
  | Match (s : shdw (wvl trace)) (b : list (cstr_type * trace))
  | Guard (σ : nv (wvl trace)) (t : trace)
.

CoInductive trace := mkTrace { _obs_tr : traceF trace }.
*)

Definition walue := wvl trace.
Definition value := vl walue trace.
Definition shadow := shdw walue.
Definition env := nv walue.

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
          (Pvl_cstr : forall c (Pl : forall w, In_vec w c.(cs_args) -> Pwvl w),
            Pvl (vl_cstr c)).
  Context (PInit : Pshdw Init)
          (PRead : forall s x, Pshdw s -> Pshdw (Read s x))
          (PCall : forall s w, Pshdw s -> Pwvl w -> Pshdw (Call s w))
          (PDstr : forall s d, Pshdw s -> Pshdw (Dstr s d)).

  Definition shdw_ind wvl_ind :=
    fix shdw_ind s : Pshdw s :=
    match s with
    | Init => PInit
    | Read s x => PRead s x (shdw_ind s)
    | Call s w => PCall s w (shdw_ind s) (wvl_ind w)
    | Dstr s d => PDstr s d (shdw_ind s)
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
    | vl_cstr c =>
      let fix in_vec {n} (l : vec _ n) w (IN : In_vec w l) {struct l} : Pwvl w :=
        match l as l' return In_vec w l' -> Pwvl w with
        | [] => _
        | hd :: tl => _
        end%vec IN
      in
      Pvl_cstr c (in_vec c.(cs_args))
    end); intro IN'; simpl in IN'.
    - exfalso. assumption.
    - destruct IN' as [IN' | IN'].
      + rewrite IN'. apply wvl_ind.
      + eapply in_vec. exact IN'.
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

(* Printing *)
Local Notation " 'μ' v " := (wvl_recv v) (at level 60, right associativity, only printing).
Local Notation " v " := (wvl_v v) (at level 60, right associativity, only printing).
Local Notation " n " := (wvl_bloc n) (at level 60, right associativity, only printing).
Local Notation " ℓ " := (wvl_floc ℓ) (at level 60, right associativity, only printing).

Local Notation " s " := (vl_sh s) (at level 60, right associativity, only printing).
Local Notation " σ " := (vl_exp σ) (at level 60, right associativity, only printing).
Local Notation " name args " := (vl_cstr {| cs_type := {| cs_name := name; cs_arity := _ |}; cs_args := args |})
  (at level 60, right associativity, only printing).
Local Notation "'⟨' 'λ' x k σ '⟩'" := (vl_clos x k σ) (at level 60, right associativity, only printing).

Local Notation "•" := (nv_mt) (at level 60, right associativity, only printing).
Local Notation "'⟪' s '⟫'" := (nv_sh s) (at level 60, right associativity, only printing).
Local Notation "'⟪' x ',' w '⟫' ';;' σ " := (nv_bd x w σ) (at level 60, right associativity, only printing).

Local Infix "<*>" := Basics.compose (at level 49).

(** Operations for substitution *)
(* open the bound location i with ℓ *)
Definition open_loc_shdw f (i : nat) (ℓ : loc) :=
  fix open (s : shadow) : shadow :=
  match s with
  | Init => Init
  | Read s x => Read (open s) x
  | Call s w => Call (open s) (f i ℓ w)
  | Dstr s d => Dstr (open s) d
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
  | vl_cstr c =>
    vl_cstr
    {|
      cs_type := c.(cs_type);
      cs_args := map_vec (f i ℓ) c.(cs_args)
    |}
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
  | Dstr s d => Dstr (close s) d
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
  | vl_cstr c =>
    vl_cstr
    {|
      cs_type := c.(cs_type);
      cs_args := map_vec (f i ℓ) c.(cs_args);
    |}
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
  | Dstr s d => Dstr (open s) d
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
  | vl_cstr c =>
    vl_cstr
    {|
      cs_type := c.(cs_type);
      cs_args := map_vec (f i u) c.(cs_args)
    |}
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
  | Dstr s d => alloc s
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
  | vl_cstr c =>
    let for_each acc w := Pos.max acc (f w) in
    fold_vec for_each c.(cs_args) xH
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
  | Dstr s d => S (size s)
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
  | vl_cstr c =>
    let for_each acc w := Nat.max acc (f w) in
    S (fold_vec for_each c.(cs_args) O)
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

Lemma open_loc_size_eq_vec m n ℓ (l : vec _ m) :
  forall acc
    (IH : forall w, In_vec w l -> open_loc_size_eq_wvl w),
    fold_vec (fun acc w => Nat.max acc (size_walue w)) l acc =
    fold_vec (fun acc w => Nat.max acc (size_walue w))
      (map_vec (open_loc_walue n ℓ) l) acc.
Proof.
  induction l; intros; simpl; auto.
  rewrite <- IH; simpl; auto.
  eapply IHl. intros. apply IH. simpl. auto.
Qed.

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
  f_equal. auto using open_loc_size_eq_vec.
Qed.

Fixpoint read_env (σ : env) (x : var) :=
  match σ with
  | nv_mt => None
  | nv_sh s => Some (wvl_v (vl_sh (Read s x)))
  | nv_bd x' w σ' =>
    if x =? x' then Some w else read_env σ' x
  end.

Definition unroll (w : walue) : option value :=
  match w with
  | wvl_v v => Some v
  | wvl_recv v => Some (open_wvl_value 0 w v)
  | wvl_bloc _ | wvl_floc _ => None
  end.

Local Definition dstr_helper1 m n k :
  n <= m -> S k <= m -> k <= m.
Proof. lia. Qed.

Local Definition dstr_helper2 m n k :
  n <= m -> S k <= m -> S (m - S k) <= m.
Proof. lia. Qed.

Definition dstr_shadow {B} (s : shadow) (b : @branch B) : env.
Proof.
  refine (
  let arity := b.(br_cstr).(cs_arity) in
  let fix for_each {n} (l : vec var n) (LE : n <= arity) acc {struct l} :=
    match l as l' in vec _ m return m <= arity -> _ with
    | [] => fun _ => acc
    | hd :: tl => _
    end%vec LE
  in for_each b.(br_vars) _ (nv_sh Init)); constructor.
  Unshelve. intro LE'.
  eapply for_each; [exact tl | eapply dstr_helper1; eauto | eapply nv_bd].
  - exact hd.
  - apply wvl_v. apply vl_sh.
    match goal with
    | _ : context [S ?m] |- _ =>
    refine (Dstr s
      {|
        ds_type := b.(br_cstr);
        ds_idx := b.(br_cstr).(cs_arity) - (S m);
        ds_valid := _
      |})
    end; eapply dstr_helper2; eauto.
  - exact acc.
Defined.

Definition dstr_cstr {B} (c : @cstr walue) (b : @branch B) : option env.
Proof.
  refine(
  let b_name := b.(br_cstr).(cs_name) in
  let c_name := c.(cs_type).(cs_name) in
  match eqb_cstr c_name b_name as b return eqb_cstr c_name b_name = b -> _ with
  | true => fun EQ =>
    let fix add_binding {m n} acc (xs : vec _ m) (ws : vec _ n) (EQ : m = n) :=
      match xs in vec _ m' return m' = n -> _ with
      | [] => fun _ => acc
      | x :: xs => fun EQ =>
        match ws in vec _ n' return m = n' -> _ with
        | [] => fun CONTRA => _
        | w :: ws => fun RR =>
          add_binding (nv_bd x w acc) xs ws _
        end _
      end EQ
    in Some (add_binding (nv_sh Init) b.(br_vars) c.(cs_args) _)
  | false => fun _ => None
  end%vec eq_refl).
  - subst b_name. subst c_name.
    rewrite eqb_cstr_eq in *.
    rewrite EQ. reflexivity.
    Unshelve.
    all:congruence.
Defined.

Definition map_branches (k : trace -> trace) b :=
  let for_branch (b : cstr_type * trace) :=
    let (c, t) := b in (c, k t)
  in List.map for_branch b
.

Definition bind (k : walue -> trace) : trace -> trace :=
  fix bind t :=
    match t with
    | Bot => Bot
    | Wal w => k w
    | Match s b => Match s (map_branches bind b)
    | Guard σ t => Guard σ (bind t)
    end.

Definition dstr_trace (d : dstr) : trace -> trace.
Proof.
  refine (
  let k w :=
    match unroll w with
    | Some (vl_sh s) => Wal (wvl_v (vl_sh (Dstr s d)))
    | Some (vl_cstr c) =>
      let c_name := c.(cs_type).(cs_name) in
      let d_name := d.(ds_type).(cs_name) in
      match eqb_cstr c_name d_name as b return eqb_cstr c_name d_name = b -> _ with
      | true => fun EQ => Wal (get_idx c.(cs_args) d.(ds_idx) _)
      | false => fun _ => Bot
      end eq_refl
    | _ => Bot
    end
  in bind k);
  subst c_name; subst d_name;
  rewrite eqb_cstr_eq in *;
  rewrite EQ; exact d.(ds_valid).
Defined.

Definition test_dstr_shadow := dstr_shadow Init
  {|
    br_cstr := {| cs_name := Cons; cs_arity := 2 |};
    br_vars := ["x"; "y"]%vec;
    br_body := tt;
  |}.

Definition test_dstr_cstr := dstr_cstr
  {|
    cs_type := {| cs_name := Cons; cs_arity := 2 |};
    cs_args := [wvl_bloc 0; wvl_bloc 1]%vec;
  |}
  {|
    br_cstr := {| cs_name := Cons; cs_arity := 2 |};
    br_vars := ["x"; "y"]%vec;
    br_body := tt;
  |}.

(*
Eval vm_compute in test_dstr_shadow.
Eval vm_compute in test_dstr_cstr.
 *)

Compute dstr_trace
  {|
    ds_type := {| cs_name := Cons; cs_arity := 2 |};
    ds_idx := 1;
    ds_valid := ltac:(repeat constructor);
  |}
  (Wal (wvl_v (vl_cstr
  {|
    cs_type := {| cs_name := Cons; cs_arity := 2 |};
    cs_args := [wvl_bloc 0; wvl_bloc 1]%vec;
  |}))).

(* type of fold_left *)
(* forall A B, (A -> B -> A) -> list B -> A -> A *)

Definition cstr_trace (c : @cstr trace) : trace :=
  let arity := c.(cs_type).(cs_arity) in
  let fix fold_arg {n} (v : vec trace n) (k : vec walue n -> vec walue arity) {struct v} :=
    match v in vec _ m return (vec walue m -> vec walue arity) -> _ with
    | [] => fun k =>
      Wal (wvl_v (vl_cstr {| cs_type := c.(cs_type) ; cs_args := k vnil |}))
    | hd :: tl => fun k =>
      let check_trace w := fold_arg tl (fun v => k (w :: v))
      in bind check_trace hd
    end%vec k
  in fold_arg c.(cs_args) (fun v => v).

Definition link_trace (link : walue -> trace) (k : walue -> trace) : trace -> trace :=
  fix link_trace t :=
    match t with
    | Bot => Bot
    | Wal w => bind k (link w)
    | Match s b =>
      let check_match w :=
        match unroll w with
        | Some (vl_sh s) => Match s (map_branches link_trace b)
        | Some (vl_cstr c) =>
          let fold_branch acc (b : cstr_type * trace) :=
            let (c', t) := b in
            match acc with
            | None =>
              if eqb_cstr c.(cs_type).(cs_name) c'.(cs_name)
              then Some (link_trace t) else None
            | Some t => Some t
            end
          in match List.fold_left fold_branch b None with
          | None => Bot
          | Some t => t
          end
        | _ => Bot
        end
      in bind check_match (link (wvl_v (vl_sh s)))
    | Guard σ t =>
      let check_guard w :=
        match unroll w with
        | Some (vl_sh s) => Guard (nv_sh s) (link_trace t)
        | Some (vl_exp σ) => Guard σ (link_trace t)
        | _ => Bot
        end
      in bind check_guard (link (wvl_v (vl_exp σ)))
    end.

Definition read_trace x :=
  let read w :=
    match unroll w with
    | Some (vl_sh s) => Wal (wvl_v (vl_sh (Read s x)))
    | Some (vl_exp σ) =>
      match read_env σ x with
      | Some w => Wal w
      | None => Bot
      end
    | _ => Bot
    end
  in bind read.

Definition call_trace
  (link : env -> walue -> trace)
  (fn arg : trace) : trace :=
  let check_fn fn :=
    match unroll fn with
    | Some (vl_sh s) =>
      let check_arg arg := Wal (wvl_v (vl_sh (Call s arg)))
      in bind check_arg arg
    | Some (vl_clos x t σ) =>
      let check_arg arg :=
        let σ' := nv_bd x arg σ
        in link_trace (link σ') Wal t
      in bind check_arg arg
    | _ => Bot
    end
  in bind check_fn fn.

Definition close_rec ℓ :=
  let close w :=
    match unroll w with
    | Some v => Wal (wvl_recv (close_value 0 ℓ v))
    | None => Bot
    end
  in bind close.

Definition bd_trace x (w : trace) (σ : trace) :=
  let check_bd w :=
    let check_mod σ :=
      match unroll σ with
      | Some (vl_sh s) => Wal (wvl_v (vl_exp (nv_bd x w (nv_sh s))))
      | Some (vl_exp σ) => Wal (wvl_v (vl_exp (nv_bd x w σ)))
      | _ => Bot
      end
    in bind check_mod σ in
  bind check_bd w.

Definition clos_trace x k :=
  let clos w :=
    match unroll w with
    | Some (vl_sh s) => Wal (wvl_v (vl_clos x k (nv_sh s)))
    | Some (vl_exp σ) => Wal (wvl_v (vl_clos x k σ))
    | _ => Bot
    end
  in bind clos.

Definition filter_env :=
  let filter w :=
    match unroll w with
    | Some (vl_sh s) => Wal (wvl_v (vl_exp (nv_sh s)))
    | Some (vl_exp σ) => Wal (wvl_v (vl_exp σ))
    | _ => Bot
    end
  in bind filter.

Lemma fold_fact {n} (v : vec walue n) :
  let fold acc w' := Nat.max acc (size_walue w') in
  forall x y, x <= y -> x < S (fold_vec fold v y).
Proof.
  induction v; intros; simpl in *; [lia | apply IHv; subst fold; simpl; lia].
Qed.

Lemma link_helper {n} (v : vec walue n) :
  let fold acc w' := Nat.max acc (size_walue w') in
  forall m w (IN : In_vec w v),
    size_walue w < S (fold_vec fold v m).
Proof.
  intro.
  induction v; intros; simpl in *; [contradiction | destruct IN as [IN | IN]].
  - subst. apply fold_fact. subst fold; simpl. lia.
  - auto.
Qed.

Ltac t :=
  repeat match goal with
  | _ => solve [auto | lia]
  | _ => progress simpl
  | RR : ?x = _ |- context [?x] => rewrite RR
  | |- context [size_value (open_loc_value ?n ?ℓ ?v)] =>
    replace (size_value (open_loc_value n ℓ v)) with (size_value v);
    [|eapply open_loc_size_eq]
  | _ => apply link_helper
  end.

(* linking, up to n steps *)
Fixpoint link (n : nat) (σ : env) : walue -> trace.
Proof.
  refine (
  match n with 0 => (fun _ => Bot) | S n =>
  let go :=
  fix link_wvl w (ACC : Acc lt (size_walue w)) {struct ACC} : trace :=
    match w as w' return w = w' -> _ with
    | wvl_v v => fun _ => link_vl v (Acc_inv ACC _)
    | wvl_recv v => fun _ =>
      let ℓ := Pos.max (alloc_value v) (alloc_env σ) in
      close_rec ℓ (link_vl (open_loc_value 0 ℓ v) (Acc_inv ACC _))
    | wvl_bloc n => fun _ => (* unreachable *) Bot
    | wvl_floc ℓ => fun _ => Wal (wvl_floc ℓ)
    end eq_refl
  with link_vl v (ACC : Acc lt (size_value v)) {struct ACC} : trace :=
    match v as v' return v = v' -> _ with
    | vl_clos x k σ' => fun _ =>
      clos_trace x k (link_nv σ' (Acc_inv ACC _))
    | vl_exp σ' => fun _ => link_nv σ' (Acc_inv ACC _)
    | vl_sh s => fun _ => link_shdw s (Acc_inv ACC _)
    | vl_cstr c => fun _ =>
      cstr_trace
      {|
        cs_type := c.(cs_type);
        cs_args :=
          map_vec_In c.(cs_args)
            (fun w IN => link_wvl w (Acc_inv ACC _));
      |}
    end eq_refl
  with link_nv σ' (ACC : Acc lt (size_env σ')) {struct ACC} : trace :=
    match σ' as σ'' return σ' = σ'' -> _ with
    | nv_mt => fun _ => Wal (wvl_v (vl_exp nv_mt))
    | nv_sh s => fun _ =>
      filter_env (link_shdw s (Acc_inv ACC _))
    | nv_bd x w σ' => fun _ =>
      bd_trace x
        (link_wvl w (Acc_inv ACC _))
        (link_nv σ' (Acc_inv ACC _))
    end eq_refl
  with link_shdw s (ACC : Acc lt (size_shadow s)) {struct ACC} : trace :=
    match s as s' return s = s' -> _ with
    | Init => fun _ => Wal (wvl_v (vl_exp σ))
    | Read s x => fun _ =>
      read_trace x (link_shdw s (Acc_inv ACC _))
    | Call s w => fun _ =>
      let fn := link_shdw s (Acc_inv ACC _) in
      let arg := link_wvl w (Acc_inv ACC _) in
      call_trace (link n) fn arg
    | Dstr s d => fun _ =>
      dstr_trace d (link_shdw s (Acc_inv ACC _))
    end eq_refl
  for link_wvl
  in fun w => go w (lt_wf (size_walue w))
  end).
  Unshelve.
  all: try abstract t.
  all: abstract t.
Defined.

Definition eval (link : env -> walue -> trace) :=
  fix eval (e : tm) : trace :=
  match e with
  | Var x => Guard (nv_sh Init) (Wal (wvl_v (vl_sh (Read Init x))))
  | Fn x M => Guard (nv_sh Init) (Wal (wvl_v (vl_clos x (eval M) (nv_sh Init))))
  | App M N => call_trace link (eval M) (eval N)
  | Link M N =>
    let client := eval N in
    let check_module m :=
      match unroll m with
      | Some (vl_sh s) => link_trace (link (nv_sh s)) Wal client
      | Some (vl_exp σ) => link_trace (link σ) Wal client
      | _ => Bot
      end
    in bind check_module (eval M)
  | Mt => Guard (nv_sh Init) (Wal (wvl_v (vl_exp nv_mt)))
  | Bind x M N =>
    let bd := eval M in
    let exp := eval N in
    let check_bd w :=
      match unroll w with
      | Some v =>
        let w := wvl_recv (close_value 0 xH v) in
        let check_exp σ :=
          match unroll σ with
          | Some (vl_sh s) => Wal (wvl_v (vl_exp (nv_bd x w (nv_sh s))))
          | Some (vl_exp σ) => Wal (wvl_v (vl_exp (nv_bd x w σ)))
          | _ => Bot
          end
        in link_trace (link (nv_bd x w (nv_sh Init))) check_exp exp
      | None => Bot
      end
    in link_trace (link (nv_bd x (wvl_floc xH) (nv_sh Init))) check_bd bd
  | Cstr c =>
    cstr_trace
      {|
        cs_type := c.(cs_type);
        cs_args := map_vec eval c.(cs_args)
      |}
  | Case E B =>
    let matched := eval E in
    let branches :=
      let for_each b :=
        {|
          br_cstr := b.(br_cstr);
          br_vars := b.(br_vars);
          br_body := eval b.(br_body);
        |} in
      List.map for_each B in
    let check_match m :=
      match unroll m with
      | Some (vl_sh s) =>
        let for_each b :=
          let body := link_trace (link (dstr_shadow s b)) Wal b.(br_body)
          in (b.(br_cstr), body)
        in Match s (List.map for_each branches)
      | Some (vl_cstr c) =>
        let fold_each acc b :=
          match acc with
          | None =>
            match dstr_cstr c b with
            | None => None
            | Some σ => Some (link_trace (link σ) Wal b.(br_body))
            end
          | Some t => Some t
          end
        in match List.fold_left fold_each branches None with
        | None => Bot
        | Some t => t
        end
      | _ => Bot
      end
    in bind check_match matched
  end.

Definition interp n := eval (link n).

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
Definition sem_link n (σ : trace) (w : trace) :=
  let check_module m :=
    match unroll m with
    | Some (vl_sh s) => link_trace (link n (nv_sh s)) Wal w
    | Some (vl_exp σ) => link_trace (link n σ) Wal w
    | _ => Bot
    end
  in bind check_module σ.

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
  interp 10 export_function_number.

Definition unknown_function_and_number_sem :=
  Eval vm_compute in
  interp 10 unknown_function_and_number.

Compute get_wal (sem_link 10
  export_function_number_sem
  unknown_function_and_number_sem).
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

Definition test_num := three_tm.

Compute get_wal (interp 10 (App test_even test_num)).
Compute get_wal (interp 10 (App test_odd test_num)).
Eval vm_compute in
  let σ := interp 10 (Bind "n" (zero_tm Zero) Mt) in
  let w := interp 10 (App test_odd (Var "n")) in
  get_wal (sem_link 10 σ w).
End MutExample.

