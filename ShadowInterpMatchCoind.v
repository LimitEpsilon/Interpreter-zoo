From Coq Require Import Utf8 PArith Lia String List.
From Paco Require Import paco.
Import ListNotations.

Local Open Scope string_scope.
Local Unset Elimination Schemes.
Local Set Primitive Projections.

Definition var := string.

Module simple.

Inductive shdw {vl} :=
  | Rd (x : var)
  | Ap (s : shdw) (v : vl)
.

Arguments shdw : clear implicits.

Inductive nv {vl} :=
  | Init
  | nv_mt
  | nv_bd (x : var) (v : vl) (σ : nv)
.

Arguments nv : clear implicits.

Inductive vl {tr} :=
  | vl_sh (s : shdw vl) (* s *)
  | vl_clos (x : var) (t : tr) (σ : nv vl) (* ⟨ λx.t, σ ⟩ *)
.

Arguments vl : clear implicits.

Definition value := vl.
Definition shadow trace := shdw (value trace).
Definition env trace := nv (value trace).

Section ind.
  Context {T : Type}.
  Let Value := value T.
  Let Env := env T.
  Let Shadow := shadow T.
  Context (Ptr : T → Prop) (tr_ind : ∀ t, Ptr t)
          (Pshdw : Shadow → Prop)
          (Pnv : Env → Prop)
          (Pvl : Value → Prop).
  Context (PRd : ∀ x, Pshdw (Rd x))
          (PAp : ∀ s v, Pshdw s → Pvl v → Pshdw (Ap s v)).
  Context (PInit : Pnv Init)
          (Pnv_mt : Pnv nv_mt)
          (Pnv_bd : ∀ x v σ, Pvl v → Pnv σ → Pnv (nv_bd x v σ)).
  Context (Pvl_sh : ∀ s, Pshdw s → Pvl (vl_sh s))
          (Pvl_clos : ∀ x k σ, Ptr k → Pnv σ → Pvl (vl_clos x k σ)).

  Definition shdw_ind vl_ind :=
    fix go s : Pshdw s :=
      match s as s' return Pshdw s' with
      | Rd x => PRd x
      | Ap f v => PAp f v (go f) (vl_ind v)
      end.

  Definition nv_ind vl_ind :=
    fix go σ : Pnv σ :=
      match σ as σ' return Pnv σ' with
      | Init => PInit
      | nv_mt => Pnv_mt
      | nv_bd x v σ' => Pnv_bd x v σ' (vl_ind v) (go σ')
      end.

  Fixpoint vl_ind v : Pvl v :=
    match v as v' return Pvl v' with
    | vl_sh s => Pvl_sh s (shdw_ind vl_ind s)
    | vl_clos x t σ => Pvl_clos x t σ (tr_ind t) (nv_ind vl_ind σ)
    end.

  Lemma pre_val_ind :
    (∀ s, Pshdw s) ∧ (∀ σ, Pnv σ) ∧ (∀ v, Pvl v).
  Proof.
    pose proof (nv_ind vl_ind).
    pose proof (shdw_ind vl_ind).
    eauto using vl_ind.
  Qed.
End ind.

Section link.
  Context {trace : Type}.
  Context {T : Type}.
  Context (stuck : T).
  Context (link_trace : env trace → trace → (value trace → T) → T).

  Definition rd x :=
    fix rd (σ : env trace) :=
      match σ with
      | Init => Some (vl_sh (Rd x))
      | nv_mt => None
      | nv_bd x' v σ' =>
        if x =? x' then Some v else rd σ'
      end.

  Definition link_shdw link_value σ0 :=
    fix link (s : shadow trace) k : T :=
      match s with
      | Rd x =>
        match rd x σ0 with
        | None => stuck
        | Some v => k v
        end
      | Ap s' v =>
        let k_s f :=
          let k_v a :=
            match f with
            | vl_sh f' => k (vl_sh (Ap f' a))
            | vl_clos x k' σ => link_trace (nv_bd x a σ) k' k
            end
          in link_value v k_v
        in link s' k_s
      end.

  Definition link_nv link_value (σ0 : env trace) :=
    fix link (σ : env trace) k : T :=
      match σ with
      | Init => k σ0
      | nv_mt => k nv_mt
      | nv_bd x v σ' =>
        let k_v v' :=
          let k_σ σ'' := k (nv_bd x v' σ'')
          in link σ' k_σ
        in link_value v k_v
      end.

  Definition link_vl σ0 :=
    fix link (v : value trace) k : T :=
      match v with
      | vl_sh s => link_shdw link σ0 s k
      | vl_clos x t σ =>
        let k_σ σ' := k (vl_clos x t σ')
        in link_nv link σ0 σ k_σ
      end.
End link.

Inductive term :=
  | Var (x : var)
  | Lam (x : var) (t : term)
  | App (fn arg : term)
.

Definition term_ind P
  (PVar : ∀ x, P (Var x))
  (PLam : ∀ x e, P e → P (Lam x e))
  (PApp : ∀ fn arg, P fn → P arg → P (App fn arg)) :=
  fix go t :=
    match t as t' return P t' with
    | Var x => PVar x
    | Lam x e => PLam x e (go e)
    | App fn arg => PApp fn arg (go fn) (go arg)
    end.

Definition ω := Lam "x" (App (Var "x") (Var "x")).
Definition ι := Lam "x" (Var "x").
Definition fst' := Lam "x" (Lam "y" (Var "x")).

Inductive traceF {trace} :=
  | Stuck
  | Ret (v : value trace)
  | Step (s : env trace) (k : traceF)
.

Arguments traceF : clear implicits.

(* Finite approximation *)
Inductive trace := Tr (e : term) (k : traceF trace).

Definition link_tr link σ0 :=
  fix go (t : traceF trace) k {struct t} :=
    let link_value := link_vl Stuck link in
    match t with
    | Stuck => Stuck
    | Ret v => link_value σ0 v k
    | Step σ t' =>
      let k_σ σ' := Step σ' (go t' k) in
      link_nv (link_value σ0) σ0 σ k_σ
    end.

Fixpoint link_trace n :=
  match n with
  | 0 => fun _ _ _ => Stuck
  | S n' =>
    let link σ0 t k :=
      match t with
      | Tr _ t' => link_trace n' σ0 t' k
      end in
    link_tr link
  end.

Fixpoint denote (t : term) k {struct t} : nat → traceF trace :=
  fun m => match m with 0 => Stuck | S n =>
  match t with
  | Var x =>
    let r := vl_sh (Rd x) in
    Step Init (k r)
  | Lam x e =>
    let E := Tr e (denote e Ret n) in
    let r := vl_clos x E Init in
    Step Init (k r)
  | App fn arg =>
    let k_fn f :=
      let k_arg a :=
        match f with
        | vl_sh f' => k (vl_sh (Ap f' a))
        | vl_clos x (Tr _ k') σ =>
          link_trace n (nv_bd x a σ) k' k
        end in
      denote arg k_arg n in
    Step Init (denote fn k_fn n)
  end end.

(*
Definition ev ev :=
  fix go t (k : _ → list (env term) * option (vl term)) :=
  match t with
  | Var x => fun σ =>
    match rd x σ with
    | None => ([σ], None)
    | Some r =>
      let '(tr, v) := k r in
      (σ :: tr, v)
    end
  | Lam x e => fun σ =>
    let '(tr, v) := k (vl_clos x e σ) in
    (σ :: tr, v)
  | App fn arg => fun σ =>
    let k_fn f :=
      let k_arg a :=
        match f with
        | vl_sh f' => k (vl_sh (Ap f' a))
        | vl_clos x e σ' => ev e k (nv_bd x a σ')
        end in
      go arg k_arg σ in
    let '(tr, v) := go fn k_fn σ in
    (σ :: tr, v)
  end.
*)

Definition ev ev :=
  fix go t (k : _ → option (vl term)) :=
  match t with
  | Var x => fun σ =>
    match rd x σ with
    | None => None
    | Some r => k r
    end
  | Lam x e => fun σ => k (vl_clos x e σ)
  | App fn arg => fun σ =>
    let k_fn f :=
      let k_arg a :=
        match f with
        | vl_sh f' => k (vl_sh (Ap f' a))
        | vl_clos x e σ' => ev e k (nv_bd x a σ')
        end in
      go arg k_arg σ in
    go fn k_fn σ
  end.

Fixpoint eval n :=
  match n with
  | 0 => fun _ _ _ => None
  | S n' => ev (eval n')
  end.

Definition lift_shdw f n :=
  fix go (s : shadow trace) :=
    match s with
    | Rd x => fun σ0 => rd x σ0
    | Ap s v => fun σ0 =>
      match go s σ0 with
      | Some fn =>
        match f v σ0 with
        | Some arg =>
          match fn with
          | vl_sh s' => Some (vl_sh (Ap s' arg))
          | vl_clos x e σ => eval n e Some (nv_bd x arg σ)
          end
        | None => None
        end
      | None => None
      end
    end.

Definition lift_nv f :=
  fix go (σ : env trace) :=
    match σ with
    | Init => Some
    | nv_mt => fun _ : env term => Some nv_mt
    | nv_bd x v σ' => fun σ0 =>
      match f v σ0 with
      | Some v' =>
        match go σ' σ0 with
        | Some σ'' => Some (nv_bd x v' σ'')
        | None => None
        end
      | None => None
      end
    end.

Definition lift_vl n :=
  fix go (v : value trace) :=
    match v with
    | vl_sh s => fun σ0 => lift_shdw go n s σ0
    | vl_clos x (Tr e _) σ => fun σ0 =>
      match lift_nv go σ σ0 with
      | Some σ' => Some (vl_clos x e σ')
      | None => None
      end
    end.

Definition lift_value := lift_vl.
Definition lift_env n := lift_nv (lift_value n).
Definition lift_shadow n := lift_shdw (lift_value n) n.
Definition lift_trace n :=
  fix go (t : traceF trace) :=
    match t with
    | Stuck => fun σ0 => None
    | Ret v => fun σ0 => lift_vl n v σ0
    | Step σ k => fun σ0 =>
      match lift_env n σ σ0 with
      | Some _ => go k σ0
      | None => None
      end
    end.

Lemma test : ∀ m t n (GT : n < m) k k' k0 σ0 σ
  (WF : ∀ v
    (WFv :
      match v with
      | vl_sh _ => True
      | vl_clos x (Tr e t') σ =>
        t' = match n with
        | 0 => Stuck
        | S n' => denote e Ret n'
        end
      end),
    lift_trace m (link_trace m σ0 (k v) k0) σ =
    match lift_env m σ0 σ with
    | Some σ' =>
      match lift_value m v σ' with
      | Some v' => k' v'
      | None => None
      end
    | None => None
    end),
  lift_trace m (link_trace m σ0 (denote t k n) k0) σ =
  match lift_env m σ0 σ with
  | Some σ' => eval n t k' σ'
  | None => None
  end.
Proof.
  induction m. lia.
  induction t; intros.
  - simpl.
    match goal with
    | |- context [link_tr ?link ?σ0 ?t ?k] =>
      change (link_tr link σ0 t k) with
      (link_trace (S m) σ0 t k)
    end.
    destruct n; simpl.
    destruct (lift_env _ _ _); auto.
    match goal with
    | |- context [link_tr ?link ?σ0 ?t ?k] =>
      change (link_tr link σ0 t k) with
      (link_trace (S m) σ0 t k)
    end.
    rewrite WF; auto.
    destruct (lift_env _ _ _); auto.
  - simpl.
    match goal with
    | |- context [link_tr ?link ?σ0 ?t ?k] =>
      change (link_tr link σ0 t k) with
      (link_trace (S m) σ0 t k)
    end.
    destruct n; simpl.
    destruct (lift_env _ _ _); auto.
    match goal with
    | |- context [link_tr ?link ?σ0 ?t ?k] =>
      change (link_tr link σ0 t k) with
      (link_trace (S m) σ0 t k)
    end.
    rewrite WF; auto.
    destruct (lift_env _ _ _); auto.
  - simpl.
    match goal with
    | |- context [link_tr ?link ?σ0 ?t ?k] =>
      change (link_tr link σ0 t k) with
      (link_trace (S m) σ0 t k)
    end.
    destruct n; simpl.
    destruct (lift_env _ _ _); auto.
    match goal with
    | |- context [link_tr ?link ?σ0 ?t ?k] =>
      change (link_tr link σ0 t k) with
      (link_trace (S m) σ0 t k)
    end.
    erewrite IHt1.
    destruct (lift_env _ _ _) eqn:RR; try reflexivity.


    auto.

  induction n.
  { intro. induction t; simpl; intros;
    destruct (lift_env _ _ _) eqn:RR; auto. }
  intro. apply PeanoNat.lt_S_n in GT.
  induction t; intros.
  - simpl.
    match goal with
    | |- context [link_tr ?link ?σ0 ?t ?k] =>
      change (link_tr link σ0 t k) with
      (link_trace (S m) σ0 t k)
    end.
    rewrite WF; auto.
    destruct (lift_env _ _ _); auto.
  - simpl.
    match goal with
    | |- context [link_tr ?link ?σ0 ?t ?k] =>
      change (link_tr link σ0 t k) with
      (link_trace (S m) σ0 t k)
    end.
    rewrite WF; auto. simpl.
    destruct (lift_env _ _ _); auto.
  - simpl.
    match goal with
    | |- context [link_tr ?link ?σ0 ?t ?k] =>
      change (link_tr link σ0 t k) with
      (link_trace (S m) σ0 t k)
    end.
    destruct (lift_env _ _ _) eqn:RR; auto.
    erewrite IHt1. rewrite RR. reflexivity.
    intros f WFf.
    erewrite IHt2. rewrite RR.
    instantiate (1 := fun a =>
      match lift_value (S n) f e with
      | Some f' =>
        match f' with
        | vl_sh s' => k' (vl_sh (Ap s' a))
        | vl_clos x e' σ' => ev (eval n) e' k' (nv_bd x a σ')
        end
      | None => None
      end).
    destruct (lift_value _ _ _) eqn:RR'; auto. { admit. }
    intros.
    destruct f. rewrite WF; auto.
    rewrite RR. simpl.
    destruct (lift_shdw _ _ _ _);
    destruct (lift_value _ _ _); auto.
    destruct v0; auto. { admit. } 
    destruct t; subst.
    rewrite RR.
    match goal with
    | |- context [link_tr ?link ?σ0 ?t ?k] =>
      change (link_tr link σ0 t k) with
      (link_trace (S n) σ0 t k)
    end.
    cbv [lift_value]. cbn [lift_vl].
    destruct (lift_env _ _ _); try reflexivity.
    simpl. reflexivity.
    .
  destruct (lift_env _ _ _) eqn:RR; auto.
    match goal with
    | |- context [link_tr ?link ?σ0 ?t ?k] =>
      change (link_tr link σ0 t k) with
      (link_trace (S n) σ0 t k)
    end.
    rewrite IHt1.
    fold 
Abort.
Lemma test' : ∀ n t k k' σ
  (WF : ∀ v
    (WFv :
      match v with
      | vl_sh _ => True
      | vl_clos x (Tr e t') σ =>
        t' = denote e Ret n
      end),
    lift_trace n (k v) σ =
    match lift_value n v σ with
    | Some v' => k' v'
    | None => None
    end),
  lift_trace n (denote t k n) σ =
  ev (eval n) t k' σ.
Proof.
  induction n; [apply test|].
  induction t; simpl; intros.
  - rewrite WF; auto.
  - rewrite WF; auto.
  - erewrite IHt1. reflexivity.
    intros f WFf. simpl.
    erewrite IHt2.
    instantiate (1 := fun a =>
      match lift_value (S n) f σ with
      | Some f' =>
        match f' with
        | vl_sh s' => k' (vl_sh (Ap s' a))
        | vl_clos x e σ' => ev (eval n) e k' (nv_bd x a σ')
        end
      | None => None
      end).
    destruct (lift_value (S n) f σ) eqn:?; simpl; auto.
    { admit. }
    intros. simpl. destruct f; simpl.
    rewrite WF; auto. simpl.
    destruct (lift_shdw _ _ _ _); simpl;
    destruct (lift_value _ _ _); simpl; auto.
    destruct v0; auto. { admit. }
    destruct t; simpl; subst.
    destruct (lift_nv _ _ _) eqn:?.
Abort.
Module judg.
(* Judgment *)
Variant judgF {judg} :=
  | Stuck
  | Ret (v : value judg)
  | AppJ (fn arg body : judg)
.

Arguments judgF : clear implicits.

Inductive judg := mkJudg (j : judgF judg).

Definition on_ret k :=
  fix go (j : judg) {struct j} :=
    let '(mkJudg j') := j in
    match j' with
    | Stuck => mkJudg Stuck
    | Ret v => k v
    | AppJ _ _ body => go body
    end.

Definition link_j link σ0 :=
  let stuck := mkJudg Stuck in
  let ret v := mkJudg (Ret v) in
  let appj f a b := mkJudg (AppJ f a b) in
  fix go (j : judg) k {struct j} :=
    let '(mkJudg j') := j in
    match j' with
    | Stuck => stuck
    | Ret v => link_vl stuck link σ0 v k
    | AppJ fn arg _ =>
      let fn' := go fn ret in
      let arg' := go arg ret in
      let k_fn f :=
        let k_arg a :=
          match f with
          | vl_sh s => k (vl_sh (Ap s a))
          | vl_clos x k' σ => link (nv_bd x a σ) k' k
          end
        in on_ret k_arg arg'
      in appj fn' arg' (on_ret k_fn fn')
    end.

Definition link_judg :=
  let stuck := mkJudg Stuck in
  fix go n :=
    match n with
    | 0 => fun _ _ _ => stuck
    | S n' => link_j (go n')
    end.

Definition denote_judg :=
  let stuck := mkJudg Stuck in
  let ret v := mkJudg (Ret v) in
  let appj f a b := mkJudg (AppJ f a b) in
  fix go (t : term) k : nat → judg :=
    match t with
    | Var x => fun _ =>
      let r := vl_sh (Rd x)
      in k r
    | Lam x e => fun n =>
      let r := vl_clos x (go e ret n) Init
      in k r
    | App fn arg => fun n =>
      let fn' := go fn ret n in
      let arg' := go arg ret n in
      let k_fn f :=
        let k_arg a :=
          match f with
          | vl_sh f' => k (vl_sh (Ap f' a))
          | vl_clos x k' σ => link_judg n (nv_bd x a σ) k' k
          end
        in on_ret k_arg arg'
      in appj fn' arg' (on_ret k_fn fn')
    end.

(* Compute denote_judg (App (App fst' (App ω ω)) ι) (fun r => mkJudg (Ret r)) 2. *)
End judg.

(* Prove that there exists a unique coinductive tree for every ω chain *)
End simple.

Definition loc := positive.

Inductive shdw {nv wvl} :=
  | Init
  | Rd (s : shdw) (σ : nv) (x : var)
  | Ap (s : shdw) (w : wvl)
.

Arguments shdw : clear implicits.

Inductive nv {wvl} :=
  | nv_sh (s : shdw nv wvl) (* [s] *)
  | nv_one (x : var) (w : wvl) (* x ↦ w *)
  | nv_mrg (σ σ' : nv) (* σ ;; σ' *)
.

Arguments nv : clear implicits.

Variant vl {P wvl tr} :=
  | vl_prim (p : P) (* primitive Value *)
  | vl_nv (σ : nv wvl)
  | vl_sh (s : shdw (nv wvl) wvl) (* s *)
  | vl_clos (x : var) (t : tr) (σ : nv wvl) (* ⟨ λx.t, σ ⟩ *)
.

Arguments vl : clear implicits.

Inductive wvl {P tr} :=
  | wvl_v (v : vl P wvl tr) (* v *)
  | wvl_recv (v : vl P wvl tr) (* μℓ.v *)
  | wvl_floc (ℓ : loc) (* free location *)
  | wvl_bloc (n : nat) (* bound location *)
.

Arguments wvl : clear implicits.

Variant traceF {P trace} :=
  | Stuck
  | Ret (w : wvl P trace)
  | Step (σ : nv (wvl P trace)) (t : trace)
.

Arguments traceF : clear implicits.

(* Finite approximation *)
Inductive trace' {P} := mkTrace' (k : traceF P trace').
Definition obs_tr' {P} (t : @trace' P) :=
  match t with
  | mkTrace' k => k
  end.

(* Infinite tree *)
CoInductive trace {P} := mkTrace { obs_tr : traceF P trace }.

Arguments trace' : clear implicits.
Arguments trace : clear implicits.
Arguments mkTrace {_} _.

Definition walue := wvl.
Definition env P trace := nv (walue P trace).
Definition shadow P trace := shdw (env P trace) (walue P trace).
Definition value P trace := vl P (walue P trace) trace.

Definition Walue' P := walue P (trace' P).
Definition Walue P := walue P (trace P).
Definition Env' P := env P (trace' P).
Definition Env P := env P (trace P).
Definition Shadow' P := shadow P (trace' P).
Definition Shadow P := shadow P (trace P).
Definition Value' P := value P (trace' P).
Definition Value P := value P (trace P).

Notation stuck' := (mkTrace' Stuck) (only parsing).
Notation stuck := (mkTrace Stuck) (only parsing).
Notation ret' w := (mkTrace' (Ret w)) (only parsing).
Notation ret w := (mkTrace (Ret w)) (only parsing).
Notation step' σ t := (mkTrace' (Step σ t)) (only parsing).
Notation step σ t := (mkTrace (Step σ t)) (only parsing).

Section ind.
  Context {P tr : Type}.
  Let Walue := walue P tr.
  Let Value := value P tr.
  Let Env := env P tr.
  Let Shadow := shadow P tr.
  Context (Ptr : tr → Prop) (tr_ind : ∀ k, Ptr k)
          (Pshdw : Shadow → Prop)
          (Pnv : Env → Prop)
          (Pvl : Value → Prop)
          (Pwvl : Walue → Prop).
  Context (PInit : Pshdw Init)
          (PRd : ∀ s σ x, Pshdw s → Pnv σ → Pshdw (Rd s σ x))
          (PAp : ∀ s w, Pshdw s → Pwvl w → Pshdw (Ap s w)).
  Context (Pnv_sh : ∀ s, Pshdw s → Pnv (nv_sh s))
          (Pnv_one : ∀ x w, Pwvl w → Pnv (nv_one x w))
          (Pnv_mrg : ∀ σ σ', Pnv σ → Pnv σ' -> Pnv (nv_mrg σ σ')).
  Context (Pvl_prim : ∀ p, Pvl (vl_prim p))
          (Pvl_nv : ∀ σ, Pnv σ → Pvl (vl_nv σ))
          (Pvl_sh : ∀ s, Pshdw s → Pvl (vl_sh s))
          (Pvl_clos : ∀ x k σ, Ptr k → Pnv σ → Pvl (vl_clos x k σ)).
  Context (Pwvl_v : ∀ v, Pvl v → Pwvl (wvl_v v))
          (Pwvl_recv : ∀ v, Pvl v → Pwvl (wvl_recv v))
          (Pwvl_floc : ∀ ℓ, Pwvl (wvl_floc ℓ))
          (Pwvl_bloc : ∀ n, Pwvl (wvl_bloc n)).

  Definition shdw_ind nv_ind wvl_ind :=
    fix go s : Pshdw s :=
      match s as s' return Pshdw s' with
      | Init => PInit
      | Rd s σ x => PRd s σ x (go s) (nv_ind σ)
      | Ap f w => PAp f w (go f) (wvl_ind w)
      end.

  Definition nv_ind wvl_ind :=
    fix go σ : Pnv σ :=
      match σ as σ' return Pnv σ' with
      | nv_sh s => Pnv_sh s (shdw_ind go wvl_ind s)
      | nv_one x w => Pnv_one x w (wvl_ind w)
      | nv_mrg σ1 σ2 => Pnv_mrg σ1 σ2 (go σ1) (go σ2)
      end.

  Definition vl_ind wvl_ind v : Pvl v :=
    match v as v' return Pvl v' with
    | vl_prim p => Pvl_prim p
    | vl_nv σ => Pvl_nv σ (nv_ind wvl_ind σ)
    | vl_sh s => Pvl_sh s (shdw_ind (nv_ind wvl_ind) wvl_ind s)
    | vl_clos x t σ => Pvl_clos x t σ (tr_ind t) (nv_ind wvl_ind σ)
    end.

  Fixpoint wvl_ind w : Pwvl w :=
    match w with
    | wvl_v v => Pwvl_v v (vl_ind wvl_ind v)
    | wvl_recv v => Pwvl_recv v (vl_ind wvl_ind v)
    | wvl_floc ℓ => Pwvl_floc ℓ
    | wvl_bloc n => Pwvl_bloc n
    end.

  Lemma pre_val_ind :
    (∀ s, Pshdw s) ∧ (∀ σ, Pnv σ) ∧ (∀ v, Pvl v) ∧ (∀ w, Pwvl w).
  Proof.
    pose proof (nv_ind wvl_ind).
    pose proof (vl_ind wvl_ind).
    pose proof (shdw_ind (nv_ind wvl_ind) wvl_ind).
    eauto using wvl_ind.
  Qed.
End ind.

Section trace'_ind.
  Context {P : Type}.
  Let tr := trace' P.
  Let Walue := walue P tr.
  Let Value := value P tr.
  Let Env := env P tr.
  Let Shadow := shadow P tr.
  Context (Ptr : tr → Prop)
          (Pshdw : Shadow → Prop)
          (Pnv : Env → Prop)
          (Pvl : Value → Prop)
          (Pwvl : Walue → Prop).
  Context (PInit : Pshdw Init)
          (PRd : ∀ s σ x, Pshdw s → Pnv σ → Pshdw (Rd s σ x))
          (PAp : ∀ s w, Pshdw s → Pwvl w → Pshdw (Ap s w)).
  Context (Pnv_sh : ∀ s, Pshdw s → Pnv (nv_sh s))
          (Pnv_one : ∀ x w, Pwvl w → Pnv (nv_one x w))
          (Pnv_mrg : ∀ σ σ', Pnv σ → Pnv σ' -> Pnv (nv_mrg σ σ')).
  Context (Pvl_prim : ∀ p, Pvl (vl_prim p))
          (Pvl_nv : ∀ σ, Pnv σ → Pvl (vl_nv σ))
          (Pvl_sh : ∀ s, Pshdw s → Pvl (vl_sh s))
          (Pvl_clos : ∀ x k σ, Ptr k → Pnv σ → Pvl (vl_clos x k σ)).
  Context (Pwvl_v : ∀ v, Pvl v → Pwvl (wvl_v v))
          (Pwvl_recv : ∀ v, Pvl v → Pwvl (wvl_recv v))
          (Pwvl_floc : ∀ ℓ, Pwvl (wvl_floc ℓ))
          (Pwvl_bloc : ∀ n, Pwvl (wvl_bloc n)).
  Context (Pstuck : Ptr stuck')
          (Pret : ∀ w, Pwvl w → Ptr (ret' w))
          (Pstep : ∀ σ t, Pnv σ → Ptr t → Ptr (step' σ t)).

  Fixpoint trace'_ind (t : tr) : Ptr t :=
    let wvl_ind' := wvl_ind _ trace'_ind _ _ _ _
      PInit PRd PAp
      Pnv_sh Pnv_one Pnv_mrg
      Pvl_prim Pvl_nv Pvl_sh Pvl_clos
      Pwvl_v Pwvl_recv Pwvl_floc Pwvl_bloc in
    let nv_ind' := nv_ind _ _ _
      PInit PRd PAp
      Pnv_sh Pnv_one Pnv_mrg wvl_ind' in
    match t with
    | mkTrace' k =>
      match k as k' return Ptr (mkTrace' k') with
      | Stuck => Pstuck
      | Ret w => Pret w (wvl_ind' w)
      | Step σ t => Pstep σ t (nv_ind' σ) (trace'_ind t)
      end
    end.

  Lemma val'_ind :
    (∀ s, Pshdw s) ∧ (∀ σ, Pnv σ) ∧ (∀ v, Pvl v) ∧ (∀ w, Pwvl w) ∧ (∀ t, Ptr t).
  Proof.
    pose proof
      (pre_val_ind (tr := tr) Ptr trace'_ind Pshdw Pnv Pvl Pwvl
        PInit PRd PAp
        Pnv_sh Pnv_one Pnv_mrg
        Pvl_prim Pvl_nv Pvl_sh Pvl_clos
        Pwvl_v Pwvl_recv Pwvl_floc Pwvl_bloc).
    intuition auto.
    apply trace'_ind.
  Qed.
End trace'_ind.

Section map.
  Definition map_shdw {wvl wvl'}
    (map_wvl : wvl → wvl')
    (map_nv : nv wvl → nv wvl') :=
    fix map_s (s : shdw (nv wvl) wvl) : shdw (nv wvl') wvl' :=
      match s with
      | Init => Init
      | Rd s' σ x => Rd (map_s s') (map_nv σ) x
      | Ap f w => Ap (map_s f) (map_wvl w)
      end.

  Definition map_nv {wvl wvl'}
    (map_wvl : wvl → wvl') :=
    fix map_nv (σ : nv wvl) : nv wvl' :=
      match σ with
      | nv_sh s => nv_sh (map_shdw map_wvl map_nv s)
      | nv_one x w => nv_one x (map_wvl w)
      | nv_mrg σ1 σ2 => nv_mrg (map_nv σ1) (map_nv σ2)
      end.

  Definition map_vl {P wvl wvl' tr tr'}
    (map_wvl : wvl → wvl')
    (map_tr : tr → tr')
    (v : vl P wvl tr) : vl P wvl' tr' :=
    match v with
    | vl_prim p => vl_prim p
    | vl_nv σ => vl_nv (map_nv map_wvl σ)
    | vl_sh s => vl_sh (map_shdw map_wvl (map_nv map_wvl) s)
    | vl_clos x t σ => vl_clos x (map_tr t) (map_nv map_wvl σ)
    end.

  Definition map_wvl {P tr tr'}
    (map_tr : tr → tr') :=
    fix map_w (w : wvl P tr) : wvl P tr' :=
      match w with
      | wvl_v v => wvl_v (map_vl map_w map_tr v)
      | wvl_recv v => wvl_recv (map_vl map_w map_tr v)
      | wvl_floc ℓ => wvl_floc ℓ
      | wvl_bloc ℓ => wvl_bloc ℓ
      end.
End map.

Section rel.
  Definition rel_shdw {wvl wvl'}
    (rel_wvl : wvl → wvl' → Prop)
    (rel_nv : nv wvl → nv wvl' → Prop) :=
    fix rel_s (s : shdw (nv wvl) wvl) (s' : shdw (nv wvl') wvl') : Prop :=
      match s with
      | Init => match s' with Init => True | _ => False end
      | Rd s σ x =>
        match s' with
        | Rd s' σ' x' => rel_s s s' ∧ rel_nv σ σ' ∧ x = x'
        | _ => False
        end
      | Ap f w =>
        match s' with
        | Ap f' w' => rel_s f f' ∧ rel_wvl w w'
        | _ => False
        end
      end.

  Definition rel_nv {wvl wvl'}
    (rel_wvl : wvl → wvl' → Prop) :=
    fix rel_nv (σ : nv wvl) (σ' : nv wvl') : Prop :=
      match σ with
      | nv_sh s =>
        match σ' with
        | nv_sh s' => rel_shdw rel_wvl rel_nv s s'
        | _ => False
        end
      | nv_one x w =>
        match σ' with
        | nv_one x' w' => x = x' ∧ rel_wvl w w'
        | _ => False
        end
      | nv_mrg σ1 σ2 =>
        match σ' with
        | nv_mrg σ1' σ2' => rel_nv σ1 σ1' ∧ rel_nv σ2 σ2'
        | _ => False
        end
      end.

  Definition rel_vl {P wvl wvl' tr tr'}
    (rel_wvl : wvl → wvl' → Prop)
    (rel_tr : tr → tr' → Prop)
    (v : vl P wvl tr) (v' : vl P wvl' tr') :=
    match v with
    | vl_prim p =>
      match v' with
      | vl_prim p' => p = p'
      | _ => False
      end
    | vl_nv σ =>
      match v' with
      | vl_nv σ' => rel_nv rel_wvl σ σ'
      | _ => False
      end
    | vl_sh s =>
      match v' with
      | vl_sh s' => rel_shdw rel_wvl (rel_nv rel_wvl) s s'
      | _ => False
      end
    | vl_clos x t σ =>
      match v' with
      | vl_clos x' t' σ' =>
        x = x' ∧ rel_tr t t' ∧ rel_nv rel_wvl σ σ'
      | _ => False
      end
    end.

  Definition rel_wvl {P tr tr'}
    (rel_tr : tr → tr' → Prop) :=
    fix rel_w (w : wvl P tr) (w' : wvl P tr') :=
      match w with
      | wvl_v v =>
        match w' with
        | wvl_v v' => rel_vl rel_w rel_tr v v'
        | _ => False
        end
      | wvl_recv v =>
        match w' with
        | wvl_recv v' => rel_vl rel_w rel_tr v v'
        | _ => False
        end
      (* Assume a fixed allocation function *)
      | wvl_floc ℓ => match w' with wvl_floc ℓ' => ℓ = ℓ' | _ => False end
      | wvl_bloc n => match w' with wvl_bloc n' => n = n' | _ => False end
      end.

  Context {P tr tr' : Type}
    (r r' : tr → tr' → Prop)
    (LEt : ∀ t t', r t t' → r' t t').

  Definition rel_shdw_monotone (s : shdw (nv (wvl P tr)) (wvl P tr)) :=
    ∀ s', rel_shdw (rel_wvl r) (rel_nv (rel_wvl r)) s s' →
          rel_shdw (rel_wvl r') (rel_nv (rel_wvl r')) s s'
  .
  Definition rel_nv_monotone (σ : nv (wvl P tr)) :=
    ∀ σ', rel_nv (rel_wvl r) σ σ' → rel_nv (rel_wvl r') σ σ'
  .
  Definition rel_vl_monotone (v : vl P (wvl P tr) tr) :=
    ∀ v', rel_vl (rel_wvl r) r v v' → rel_vl (rel_wvl r') r' v v'
  .
  Definition rel_wvl_monotone (w : wvl P tr) :=
    ∀ w', rel_wvl r w w' → rel_wvl r' w w'
  .

  Lemma rel_monotone :
    (∀ s, rel_shdw_monotone s) ∧
    (∀ σ, rel_nv_monotone σ) ∧
    (∀ v, rel_vl_monotone v) ∧
    (∀ w, rel_wvl_monotone w).
  Proof.
    apply (pre_val_ind _ (fun _ => I));
    cbv [rel_shdw_monotone rel_nv_monotone rel_vl_monotone rel_wvl_monotone];
    simpl; intros;
    match goal with
    | _ : match ?x with _ => _ end |- _ =>
      destruct x; intuition auto
    end.
  Qed.
End rel.

(* partial order between finite approximations *)
Definition le_trace' {P} :=
  fix le_t (t t' : trace' P) :=
    let le_wvl := rel_wvl le_t in
    match obs_tr' t with
    | Stuck => True
    | Ret w =>
      match obs_tr' t' with
      | Ret w' => le_wvl w w'
      | _ => False
      end
    | Step σ k =>
      match obs_tr' t' with
      | Step σ' k' => rel_nv le_wvl σ σ' ∧ le_t k k'
      | _ => False
      end
    end.

Lemma le_trace'_refl {P} :
  let le_wvl (w : Walue' P) := rel_wvl le_trace' w in
  let le_vl (v : Value' P) := rel_vl le_wvl le_trace' v in
  let le_nv (σ : Env' P) := rel_nv le_wvl σ in
  let le_shdw (s : Shadow' P) := rel_shdw le_wvl le_nv s in
  (∀ s, le_shdw s s) ∧
  (∀ σ, le_nv σ σ) ∧
  (∀ v, le_vl v v) ∧
  (∀ w, le_wvl w w) ∧
  (∀ t : trace' P, le_trace' t t).
Proof. cbn zeta. apply val'_ind; simpl; auto. Qed.

Lemma le_trace'_trans {P} :
  let le_wvl (w : Walue' P) := rel_wvl le_trace' w in
  let le_vl (v : Value' P) := rel_vl le_wvl le_trace' v in
  let le_nv (σ : Env' P) := rel_nv le_wvl σ in
  let le_shdw (s : Shadow' P) := rel_shdw le_wvl le_nv s in
  (∀ s' : Shadow' P,
    ∀ s s'', le_shdw s s' → le_shdw s' s'' → le_shdw s s'') ∧
  (∀ σ' : Env' P,
    ∀ σ σ'', le_nv σ σ' → le_nv σ' σ'' → le_nv σ σ'') ∧
  (∀ v' : Value' P,
    ∀ v v'', le_vl v v' → le_vl v' v'' → le_vl v v'') ∧
  (∀ w' : Walue' P,
    ∀ w w'', le_wvl w w' → le_wvl w' w'' → le_wvl w w'') ∧
  (∀ t' : trace' P,
    ∀ t t'', le_trace' t t' → le_trace' t' t'' → le_trace' t t'').
Proof.
  cbn zeta. apply val'_ind; simpl; intros;
  match goal with
  | |- rel_shdw _ _ ?s ?s'' =>
    destruct s; simpl in *; intuition eauto;
    on_ret; destruct s''; intuition eauto
  | |- rel_nv _ ?σ ?σ'' =>
    destruct σ; simpl in *; intuition eauto;
    on_ret; destruct σ''; intuition eauto
  | |- rel_vl _ _ ?v ?v'' =>
    destruct v; simpl in *; intuition eauto;
    on_ret; destruct v''; intuition eauto
  | |- rel_wvl _ ?w ?w'' =>
    destruct w; simpl in *; intuition eauto;
    on_ret; destruct w''; intuition eauto
  | |- le_trace' ?t ?t'' =>
    destruct t; simpl in *; intuition eauto;
    on_ret; destruct t''; intuition eauto
  end.
  - destruct k; simpl in *; intuition eauto.
  - destruct k; simpl in *; intuition eauto.
    destruct k0; simpl in *; intuition eauto.
  - destruct k; simpl in *; intuition eauto.
    destruct k0; simpl in *; intuition eauto.
Qed.

(* approx t' t : t' is a finite approximation of t *)
Definition approx {P} :=
  fix approx (t' : trace' P) (t : trace P) :=
    let approx_w := rel_wvl approx in
    match obs_tr' t' with
    | Stuck => True
    | Ret w' =>
      match obs_tr t with
      | Ret w => approx_w w' w
      | _ => False
      end
    | Step σ' k' =>
      match obs_tr t with
      | Step σ k => rel_nv approx_w σ' σ ∧ approx k' k
      | _ => False
      end
    end.

Variant eq_traceF {P} eq : trace P → trace P → Prop :=
  | eq_stuck : eq_traceF eq stuck stuck
  | eq_ret w w'
    (EQw : rel_wvl eq w w')
  : eq_traceF eq (ret w) (ret w')
  | eq_step σ σ' k k'
    (EQσ : rel_nv (rel_wvl eq) σ σ')
    (EQk : eq k k')
  : eq_traceF eq (step σ k) (step σ' k')
.

Arguments eq_traceF : clear implicits.

Lemma eq_traceF_monotone {P} : monotone2 (eq_traceF P).
Proof.
  repeat intro. inversion IN; try constructor; on_ret; auto.
  all: eapply rel_monotone; eauto.
Qed.

Hint Resolve eq_traceF_monotone : paco.
Definition eq_trace P := paco2 (eq_traceF P) bot2.

Fixpoint nth_trace {P} (n : nat) (t : trace P) : trace' P :=
  match n with
  | 0 => stuck'
  | S n' =>
    match obs_tr t with
    | Stuck => stuck'
    | Ret w =>
      let w' := map_wvl (nth_trace n') w in
      ret' w'
    | Step σ k =>
      let σ' := map_nv (map_wvl (nth_trace n')) σ in
      step' σ' (nth_trace n' k)
    end
  end.

Section subst.
  Context {P trace : Type}.
  Let Walue := walue P trace.
  Let Env := env P trace.
  Let Value := value P trace.
  Let Shadow := shadow P trace.

  (** Operations for on_retitution *)
  (* open the bound location i with ℓ *)
  Definition open_loc_shdw fw fn (i : nat) (ℓ : loc) :=
    fix open (s : shadow P trace) : Shadow :=
    match s with
    | Init => Init
    | Rd s σ x => Rd (open s) (fn σ) x
    | Ap s w => Ap (open s) (fw w)
    end.

  Definition open_loc_nv fw (i : nat) (ℓ : loc) :=
    fix open (σ : Env) :=
    match σ with
    | nv_sh s => nv_sh (open_loc_shdw fw open i ℓ s)
    | nv_one x w => nv_one x (fw w)
    | nv_mrg σ σ' => nv_mrg (open σ) (open σ') 
    end.

  Definition open_loc_vl fw (i : nat) (ℓ : loc) :=
    let open (v : Value) :=
      match v with
      | vl_prim p => vl_prim p
      | vl_nv σ => vl_nv (open_loc_nv fw i ℓ σ)
      | vl_sh s => vl_sh (open_loc_shdw fw (open_loc_nv fw i ℓ) i ℓ s)
      | vl_clos x k σ => vl_clos x k (open_loc_nv fw i ℓ σ)
      end in
    open.

  Fixpoint open_loc_walue (i : nat) (ℓ : loc) (w : Walue) : Walue :=
    match w with
    | wvl_v v => wvl_v (open_loc_vl (open_loc_walue i ℓ) i ℓ v)
    | wvl_recv v => wvl_recv (open_loc_vl (open_loc_walue (S i) ℓ) (S i) ℓ v)
    | wvl_bloc n => if Nat.eqb i n then wvl_floc ℓ else wvl_bloc n
    | wvl_floc ℓ => wvl_floc ℓ
    end.

  Definition open_loc_value i ℓ := open_loc_vl (open_loc_walue i ℓ) i ℓ.
  Definition open_loc_env i ℓ := open_loc_nv (open_loc_walue i ℓ) i ℓ.
  Definition open_loc_shadow i ℓ := open_loc_shdw (open_loc_walue i ℓ) (open_loc_env i ℓ).

  (* close the free location ℓ with the binding depth i *)
  Definition close_loc_shdw fw fn (i : nat) (ℓ : loc) :=
    fix close (s : shadow P trace) : Shadow :=
    match s with
    | Init => Init
    | Rd s σ x => Rd (close s) (fn σ) x
    | Ap s w => Ap (close s) (fw w)
    end.

  Definition close_loc_nv fw (i : nat) (ℓ : loc) :=
    fix close (σ : Env) :=
    match σ with
    | nv_sh s => nv_sh (close_loc_shdw fw close i ℓ s)
    | nv_one x w => nv_one x (fw w)
    | nv_mrg σ σ' => nv_mrg (close σ) (close σ') 
    end.

  Definition close_loc_vl fw (i : nat) (ℓ : loc) :=
    let close (v : Value) :=
      match v with
      | vl_prim p => vl_prim p
      | vl_nv σ => vl_nv (close_loc_nv fw i ℓ σ)
      | vl_sh s => vl_sh (close_loc_shdw fw (close_loc_nv fw i ℓ) i ℓ s)
      | vl_clos x k σ => vl_clos x k (close_loc_nv fw i ℓ σ)
      end in
    close.

  Fixpoint close_loc_walue (i : nat) (ℓ : loc) (w : Walue) : Walue :=
    match w with
    | wvl_v v => wvl_v (close_loc_vl (close_loc_walue i ℓ) i ℓ v)
    | wvl_recv v => wvl_recv (close_loc_vl (close_loc_walue (S i) ℓ) (S i) ℓ v)
    | wvl_bloc n => wvl_bloc n
    | wvl_floc ℓ' => if Pos.eqb ℓ ℓ' then wvl_bloc i else wvl_floc ℓ'
    end.

  Definition close_loc_value i ℓ := close_loc_vl (close_loc_walue i ℓ) i ℓ.
  Definition close_loc_env i ℓ := close_loc_nv (close_loc_walue i ℓ) i ℓ.
  Definition close_loc_shadow i ℓ := close_loc_shdw (close_loc_walue i ℓ) (close_loc_env i ℓ).

  (* open the bound location i with u *)
  Definition open_wvl_shdw fw fn (i : nat) (u : Walue) :=
    fix open (s : shadow P trace) : Shadow :=
    match s with
    | Init => Init
    | Rd s σ x => Rd (open s) (fn σ) x
    | Ap s w => Ap (open s) (fw w)
    end.

  Definition open_wvl_nv fw (i : nat) (u : Walue) :=
    fix open (σ : Env) :=
    match σ with
    | nv_sh s => nv_sh (open_wvl_shdw fw open i u s)
    | nv_one x w => nv_one x (fw w)
    | nv_mrg σ σ' => nv_mrg (open σ) (open σ') 
    end.

  Definition open_wvl_vl fw (i : nat) (u : Walue) :=
    let open (v : Value) :=
      match v with
      | vl_prim p => vl_prim p
      | vl_nv σ => vl_nv (open_wvl_nv fw i u σ)
      | vl_sh s => vl_sh (open_wvl_shdw fw (open_wvl_nv fw i u) i u s)
      | vl_clos x k σ => vl_clos x k (open_wvl_nv fw i u σ)
      end in
    open.

  Fixpoint open_wvl_walue (i : nat) (u : Walue) (w : Walue) : Walue :=
    match w with
    | wvl_v v => wvl_v (open_wvl_vl (open_wvl_walue i u) i u v)
    | wvl_recv v => wvl_recv (open_wvl_vl (open_wvl_walue (S i) u) (S i) u v)
    | wvl_bloc n => if Nat.eqb i n then u else wvl_bloc n
    | wvl_floc ℓ => wvl_floc ℓ
    end.

  Definition open_wvl_value i ℓ := open_wvl_vl (open_wvl_walue i ℓ) i ℓ.
  Definition open_wvl_env i ℓ := open_wvl_nv (open_wvl_walue i ℓ) i ℓ.
  Definition open_wvl_shadow i ℓ := open_wvl_shdw (open_wvl_walue i ℓ) (open_wvl_env i ℓ).
End subst.

(* Define : coinductive version of traces *)
(* Define : strong bisimilarity between traces *)
(* Define : depth-n approximation between traces *)
(* Prove : strong bisimilarity ↔ equality of approximation for all n *)
(* Conclusion : represent coinductive trace with a stream of "increasing" approximations *)
