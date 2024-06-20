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

Section vec_IND.
  Context {A : Type}.
  Context (P : forall n, @vec A n -> Prop).
  Context (Pnil : P 0 vnil)
          (Pcons : forall n hd tl (IHtl : P n tl), P (S n) (vcons hd tl)).

  Fixpoint vec_ind {n} (v : @vec A n) : P n v :=
    match v as v' in vec n' return P n' v' with
    | vnil => Pnil
    | @vcons _ n' hd tl => Pcons n' hd tl (vec_ind tl)
    end.
End vec_IND.

Declare Scope vec_scope.
Delimit Scope vec_scope with vec.
Infix "::" := vcons.
Notation "[ ]" := vnil (format "[ ]") : vec_scope.
Notation "[ x ]" := (vcons x nil) : vec_scope.
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

Variant cstr_name : nat -> Type :=
  | Zero : cstr_name 0
  | Succ : cstr_name 1
.

Record cstr_type :=
  {
    cs_arity : nat;
    cs_name : cstr_name cs_arity;
  }.

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
  | Fn (x : var) (e : tm)
  | App (f a : tm)
  | Link (m e : tm) (* m ⋊ e *)
  | Mt (* ε *)
  | Bind (x : var) (v m : tm) (* let rec x = v ; m *)
  | Cstr (args : @cstr tm) (* C e1 e2 ... en *)
  | Case (e : tm) (b : list (@branch tm))
    (* match e with | C1 \vec{x1} => e1 | ... | Cn \vec{xn} => en end *)
.

Inductive wvl {vl} :=
  | wvl_v (v : vl) (* v *)
  | wvl_recv (v : vl) (* μ.v *)
  | wvl_bloc (n : nat) (* bound location *)
  | wvl_floc (ℓ : loc) (* free location *)
.

Arguments wvl : clear implicits.

Inductive shdw {vl} :=
  | Init
  | Read (s : shdw) (x : var)
  | Call (s : shdw) (v : vl)
  | Dstr (s : shdw) (d : dstr)
.

Arguments shdw : clear implicits.

Inductive nv {vl} :=
  | nv_mt (* • *)
  | nv_sh (s : shdw vl) (* [s] *)
  | nv_bd (x : var) (w : wvl vl) (σ : nv) (* bound value *)
.

Arguments nv : clear implicits.

Inductive vl {K} :=
  | vl_sh (s : shdw vl)
  | vl_exp (σ : nv vl)
  | vl_clos (x : var) (k : K) (σ : nv vl)
  | vl_cstr (c : @cstr (wvl vl))
.

Arguments vl : clear implicits.

(*
Variant traceF trace :=
  | Bot
  | Wal (w : (wvl (vl (list trace))))
  | Match (v : shdw (vl (list trace))) (c : cstr_type) (k : trace)
  | Guard (σ : nv (vl (list trace))) (k : trace)
.

CoInductive trace := mkTrace { _observe : traceF trace }.
*)

(* finite approximations *)
Inductive trace :=
  | Bot
  | Wal (w : wvl (vl (list trace)))
  | Match (s : shdw (vl (list trace))) (c : cstr_type) (k : trace)
  | Guard (σ : nv (vl (list trace))) (k : trace)
.

Definition value := vl (list trace).
Definition walue := wvl value.
Definition shadow := shdw value.
Definition env := nv value.

Section pre_val_IND.
  Context {K : Type}.
  Context (Pwvl : wvl (vl K) -> Prop) (Pnv : nv (vl K) -> Prop) (Pvl : vl K -> Prop) (Pshdw : shdw (vl K) -> Prop).
  Context (Pwvl_v : forall v, Pvl v -> Pwvl (wvl_v v))
          (Pwvl_recv : forall v, Pvl v -> Pwvl (wvl_recv v))
          (Pwvl_bloc : forall n, Pwvl (wvl_bloc n))
          (Pwvl_floc : forall ℓ, Pwvl (wvl_floc ℓ)).
  Context (Pnv_mt : Pnv nv_mt)
          (Pnv_sh : forall s, Pshdw s -> Pnv (nv_sh s))
          (Pnv_bd : forall x w σ, Pwvl w -> Pnv σ -> Pnv (nv_bd x w σ)).
  Context (Pvl_sh : forall s, Pshdw s -> Pvl (vl_sh s))
          (Pvl_exp : forall σ, Pnv σ -> Pvl (vl_exp σ))
          (Pvl_clos : forall x k σ, Pnv σ -> Pvl (vl_clos x k σ))
          (Pvl_cstr : forall c (Pl : forall w, In_vec w c.(cs_args) -> Pwvl w),
            Pvl (vl_cstr c)).
  Context (PInit : Pshdw Init)
          (PRead : forall s x, Pshdw s -> Pshdw (Read s x))
          (PCall : forall s v, Pshdw s -> Pvl v -> Pshdw (Call s v))
          (PDstr : forall s d, Pshdw s -> Pshdw (Dstr s d)).

  Definition wvl_ind vl_ind w : Pwvl w :=
    match w with
    | wvl_v v => Pwvl_v v (vl_ind v)
    | wvl_recv v => Pwvl_recv v (vl_ind v)
    | wvl_bloc n => Pwvl_bloc n
    | wvl_floc ℓ => Pwvl_floc ℓ
    end.

  Definition shdw_ind vl_ind :=
    fix shdw_ind s : Pshdw s :=
    match s with
    | Init => PInit
    | Read s x => PRead s x (shdw_ind s)
    | Call s v => PCall s v (shdw_ind s) (vl_ind v)
    | Dstr s d => PDstr s d (shdw_ind s)
    end.

  Definition nv_ind vl_ind :=
    fix nv_ind σ : Pnv σ :=
    match σ with
    | nv_mt => Pnv_mt
    | nv_sh s => Pnv_sh s (shdw_ind vl_ind s)
    | nv_bd x w σ => Pnv_bd x w σ (wvl_ind vl_ind w) (nv_ind σ)
    end.

  Fixpoint vl_ind v : Pvl v.
  Proof.
    refine (
    let wvl_ind := wvl_ind vl_ind in
    let shdw_ind := shdw_ind vl_ind in
    let nv_ind := nv_ind vl_ind in
    match v with
    | vl_sh s => Pvl_sh s (shdw_ind s)
    | vl_exp σ => Pvl_exp σ (nv_ind σ)
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
  Qed.

  Lemma pre_val_ind :
    (forall w, Pwvl w) /\
    (forall σ, Pnv σ) /\
    (forall v, Pvl v) /\
    (forall s, Pshdw s).
  Proof.
    eauto using (wvl_ind vl_ind), (nv_ind vl_ind), vl_ind, (shdw_ind vl_ind).
  Qed.
End pre_val_IND.

Local Notation "'⟨' 'μ' v '⟩'" := (wvl_recv v) (at level 60, right associativity, only printing).
Local Notation "'⟨' v '⟩'" := (wvl_v v) (at level 60, right associativity, only printing).
Local Notation "'⟨' 'λ' x k σ '⟩'" := (vl_clos x k σ) (at level 60, right associativity, only printing).
Local Notation "'⟨' s '⟩'" := (vl_sh s) (at level 60, right associativity, only printing).
Local Notation "•" := (nv_mt) (at level 60, right associativity, only printing).
Local Notation "'⟪' s '⟫'" := (nv_sh s) (at level 60, right associativity, only printing).
Local Notation "'⟪' x ',' w '⟫' ';;' σ " := (nv_bd x w σ) (at level 60, right associativity, only printing).
Local Infix "<*>" := Basics.compose (at level 49).

(* Lifting from Reynolds, Theory of Programming Languages  *)
Definition lift {A B : Type} (f : A -> option B) (x : option A) :=
  match x with
  | None => None
  | Some x => f x
  end.

(** Operations for substitution *)
(* open the bound location i with ℓ *)
Definition open_loc_wvl f (i : nat) (ℓ : loc) (w : walue) : walue :=
  match w with
  | wvl_v v => wvl_v (f i ℓ v)
  | wvl_recv v => wvl_recv (f (S i) ℓ v)
  | wvl_bloc n => if Nat.eqb i n then wvl_floc ℓ else wvl_bloc n
  | wvl_floc ℓ => wvl_floc ℓ
  end.

Definition open_loc_shdw f (i : nat) (ℓ : loc) :=
  fix open (s : shadow) : shadow :=
  match s with
  | Init => Init
  | Read s x => Read (open s) x
  | Call s v => Call (open s) (f i ℓ v)
  | Dstr s d => Dstr (open s) d
  end.

Definition open_loc_nv f (i : nat) (ℓ : loc) :=
  fix open (σ : env) :=
  match σ with
  | nv_mt => nv_mt
  | nv_sh s => nv_sh (open_loc_shdw f i ℓ s)
  | nv_bd x w σ' =>
    nv_bd x (open_loc_wvl f i ℓ w) (open σ')
  end.

Fixpoint open_loc_value (i : nat) (ℓ : loc) (v : value) {struct v} :=
  match v with
  | vl_sh s => vl_sh (open_loc_shdw open_loc_value i ℓ s)
  | vl_exp σ => vl_exp (open_loc_nv open_loc_value i ℓ σ)
  | vl_clos x k σ => vl_clos x k (open_loc_nv open_loc_value i ℓ σ)
  | vl_cstr c =>
    vl_cstr
    {|
      cs_type := c.(cs_type);
      cs_args := map_vec (open_loc_wvl open_loc_value i ℓ) c.(cs_args)
    |}
  end.

Definition open_loc_walue := open_loc_wvl open_loc_value.
Definition open_loc_env := open_loc_nv open_loc_value.
Definition open_loc_shadow := open_loc_shdw open_loc_value.

(* close the free location ℓ with the binding depth i *)
Definition close_wvl f (i : nat) (ℓ : loc) (w : walue) : walue :=
  match w with
  | wvl_v v => wvl_v (f i ℓ v)
  | wvl_recv v => wvl_recv (f (S i) ℓ v)
  | wvl_bloc n => wvl_bloc n
  | wvl_floc ℓ' => if Pos.eqb ℓ ℓ' then wvl_bloc i else wvl_floc ℓ'
  end.

Definition close_shdw f (i : nat) (ℓ : loc) :=
  fix close (s : shadow) : shadow :=
  match s with
  | Init => Init
  | Read s x => Read (close s) x
  | Call s v => Call (close s) (f i ℓ v)
  | Dstr s d => Dstr (close s) d
  end.

Definition close_nv f (i : nat) (ℓ : loc) :=
  fix close (σ : env) : env :=
  match σ with
  | nv_mt => nv_mt
  | nv_sh s => nv_sh (close_shdw f i ℓ s)
  | nv_bd x w σ' =>
    nv_bd x (close_wvl f i ℓ w) (close σ')
  end.

Fixpoint close_value (i : nat) (ℓ : loc) (v : value) : value :=
  match v with
  | vl_sh s => vl_sh (close_shdw close_value i ℓ s)
  | vl_exp σ => vl_exp (close_nv close_value i ℓ σ)
  | vl_clos x k σ => vl_clos x k (close_nv close_value i ℓ σ)
  | vl_cstr c =>
    vl_cstr
    {|
      cs_type := c.(cs_type);
      cs_args := map_vec (close_wvl close_value i ℓ) c.(cs_args);
    |}
  end.

Definition close_walue := close_wvl close_value.
Definition close_env := close_nv close_value.
Definition close_shadow := close_shdw close_value.

(* open the bound location i with u *)
Definition open_wvl_wvl f (i : nat) (u : walue) (w : walue) : walue :=
  match w with
  | wvl_v v => wvl_v (f i u v)
  | wvl_recv v => wvl_recv (f (S i) u v)
  | wvl_bloc n => if Nat.eqb i n then u else wvl_bloc n
  | wvl_floc ℓ => wvl_floc ℓ
  end.

Definition open_wvl_shdw f (i : nat) (u : walue) :=
  fix open (s : shadow) : shadow :=
  match s with
  | Init => Init
  | Read s x => Read (open s) x
  | Call s v => Call (open s) (f i u v)
  | Dstr s d => Dstr (open s) d
  end.

Definition open_wvl_nv f (i : nat) (u : walue) :=
  fix open (σ : env) :=
  match σ with
  | nv_mt => nv_mt
  | nv_sh s => nv_sh (open_wvl_shdw f i u s)
  | nv_bd x w σ' =>
    nv_bd x (open_wvl_wvl f i u w) (open σ')
  end.

Fixpoint open_wvl_value (i : nat) (u : walue) (v : value) {struct v} :=
  match v with
  | vl_sh s => vl_sh (open_wvl_shdw open_wvl_value i u s)
  | vl_exp σ => vl_exp (open_wvl_nv open_wvl_value i u σ)
  | vl_clos x k σ => vl_clos x k (open_wvl_nv open_wvl_value i u σ)
  | vl_cstr c =>
    vl_cstr
    {|
      cs_type := c.(cs_type);
      cs_args := map_vec (open_wvl_wvl open_wvl_value i u) c.(cs_args)
    |}
  end.

Definition open_wvl_walue := open_wvl_wvl open_wvl_value.
Definition open_wvl_env := open_wvl_nv open_wvl_value.
Definition open_wvl_shadow := open_wvl_shdw open_wvl_value.

(* allocate fresh locations *)
Definition alloc_wvl f (w : walue) : positive :=
  match w with
  | wvl_v v | wvl_recv v => f v
  | wvl_bloc _ => 1
  | wvl_floc ℓ => Pos.succ ℓ
  end%positive.

Definition alloc_shdw f :=
  fix alloc (s : shadow) : positive :=
  match s with
  | Init => xH
  | Read s x => alloc s
  | Call s v => Pos.max (alloc s) (f v)
  | Dstr s d => alloc s
  end.

Definition alloc_nv f :=
  fix alloc (σ : env) : positive :=
  match σ with
  | nv_mt => xH
  | nv_sh s => alloc_shdw f s
  | nv_bd _ w σ' => Pos.max (alloc_wvl f w) (alloc σ')
  end.

Fixpoint alloc_value (v : value) : positive :=
  match v with
  | vl_sh s => alloc_shdw alloc_value s
  | vl_exp σ | vl_clos _ _ σ => alloc_nv alloc_value σ
  | vl_cstr c =>
    let for_each acc w := Pos.max acc (alloc_wvl alloc_value w) in
    fold_vec for_each c.(cs_args) xH
  end.

Definition alloc_walue := alloc_wvl alloc_value.
Definition alloc_env := alloc_nv alloc_value.
Definition alloc_shadow := alloc_shdw alloc_value.

(* term size *)
Definition size_wvl f (w : walue) :=
  match w with
  | wvl_v v | wvl_recv v => S (f v)
  | wvl_bloc _ | wvl_floc _ => O
  end.

Definition size_shdw f :=
  fix size (s : shadow) :=
  match s with
  | Init => O
  | Read s x => S (size s)
  | Call s v => S (Nat.max (size s) (f v))
  | Dstr s d => S (size s)
  end.

Definition size_nv f :=
  fix size (σ : env) :=
  match σ with
  | nv_mt => O
  | nv_sh s => S (size_shdw f s)
  | nv_bd _ w σ' => S (Nat.max (size_wvl f w) (size σ'))
  end.

Fixpoint size_value (v : value) :=
  match v with
  | vl_sh s => S (size_shdw size_value s)
  | vl_exp σ | vl_clos _ _ σ => S (size_nv size_value σ)
  | vl_cstr c =>
    let for_each acc w := Nat.max acc (size_wvl size_value w) in
    S (fold_vec for_each c.(cs_args) O)
  end.

Definition size_walue := size_wvl size_value.
Definition size_env := size_nv size_value.
Definition size_shadow := size_shdw size_value.

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
    fold_vec (fun acc w => Nat.max acc (size_wvl size_value w)) l acc =
    fold_vec (fun acc w => Nat.max acc (size_wvl size_value w))
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

Definition eval (link : nv -> vl -> option vl) :=
  fix eval (e : tm) : list trace :=
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
      let w := wvl_recv (close_value 0 xH v) in
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
        Some (vl_sh (CaseS s vO vS))
      | vl_exp _ | vl_clos _ _ _ => None
      end
    in lift foldE (eval E)
  end.

Ltac t :=
  repeat match goal with
  | _ => solve [auto | lia]
  | _ => progress simpl
  | RR : ?x = _ |- context [?x] => rewrite RR
  | |- context [size_value (open_loc_value ?n ?ℓ ?v)] =>
    replace (size_value (open_loc_value n ℓ v)) with (size_vl v);
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
      let ℓ := alloc_value v in
      let recv v := Some (wvl_recv (close_value 0 ℓ v)) in
      lift recv (link_vl (open_loc_value 0 ℓ v) (Acc_inv ACC _))
    end eq_refl
  with link_vl v (ACC : Acc lt (size_value v)) {struct ACC} : option vl :=
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
        | vl_sh (PredS s) => Some (vl_sh s)
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
  in fun v => go v (lt_wf (size_value v))
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
        (App (Var "f") Zero)
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

Compute interp 10
(App
  (App add_tm
    (App (App add_tm (Var "x")) (Succ Zero)))
    (Succ (Succ Zero))).

