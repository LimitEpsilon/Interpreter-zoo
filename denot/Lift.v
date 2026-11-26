(** * Values of the interpreter as values of the domain

    This file defines [lift]. It puts the denotation of a term in the place
    of the term of each closure. [Adequacy.v] states its theorems with
    [lift].

    ** Main definitions

    - [lift], [lift_env], [lift_list]: lift a value, an environment and a
      list of values of the interpreter.

    ** Main results

    - [lift_close], [lift_unr], [read_lift]: [lift] moves through close,
      through the replacement of an index, and through a read.
    - [fresh_lift]: the anchor that the interpreter selects is fresh for the
      lifted environment.
    - [ev_mono]: more fuel keeps a value of the interpreter. *)
From Stdlib Require Import Utf8 String Bool Arith Lia List.
From Denot Require Import Syntax Anchor Domain Nominal Semantics Laws Wf Order
  Conv Reference.

(** Lift a value of the interpreter. The body of each closure becomes the
    denotation of its term. *)
Fixpoint lift (v : rvl) : vl :=
  match v with
  | r_exp ρ => vl_exp (lift_env ρ)
  | r_clos x e ρ => vl_clos x (den e) (lift_env ρ)
  | r_cstr c vs => vl_cstr c (lift_list vs)
  end
with lift_env (ρ : renv) : nv :=
  match ρ with
  | rnil => nv_mt
  | rcons x v ρ' => nv_bd x (lift v) (lift_env ρ')
  | rmu x v ρ' => nv_mu x (lift v) (lift_env ρ')
  | ran x a ρ' => nv_an x a (lift_env ρ')
  end
with lift_list (vs : rvls) : vls :=
  match vs with
  | rvnil => vnil
  | rvcons v vs' => vcons (lift v) (lift_list vs')
  end.

(** [lift] moves through close. *)
Lemma lift_close :
  (∀ v k ℓ, lift (rclose k ℓ v) = am_vl (fclose ℓ) k (lift v)) ∧
  (∀ ρ k ℓ, lift_env (rclose_env k ℓ ρ) = am_nv (fclose ℓ) k (lift_env ρ)) ∧
  (∀ vs k ℓ, lift_list (rclose_list k ℓ vs) = am_vls (fclose ℓ) k (lift_list vs)).
Proof. apply ref_mutind; simpl; intros; f_equal; auto. Qed.

(** [lift] moves through the replacement of an index by a recursive value. *)
Lemma lift_unr :
  (∀ v k u, lift (runr k u v) = su_vl (funr (lift u)) k (lift v)) ∧
  (∀ ρ k u, lift_env (runr_env k u ρ) = su_nv (funr (lift u)) k (lift_env ρ)) ∧
  (∀ vs k u, lift_list (runr_list k u vs) = su_vls (funr (lift u)) k (lift_list vs)).
Proof.
  apply ref_mutind; simpl; intros; try (f_equal; auto).
  destruct a as [j|z]; simpl; [destruct (Nat.eqb j k)|]; simpl; f_equal; auto.
Qed.

(** [lift] keeps the largest free anchor. *)
Lemma sup_lift :
  (∀ v, sup_vl (lift v) = rsup v) ∧ (∀ ρ, sup_nv (lift_env ρ) = rsup_env ρ) ∧
  (∀ vs, sup_vls (lift_list vs) = rsup_list vs).
Proof. apply ref_mutind; simpl; intros; auto. Qed.

(** A read in the lifted environment gives the lifted value. *)
Lemma read_lift x ρ : read x (lift_env ρ) = option_map lift (rread x ρ).
Proof.
  induction ρ as [|y v ρ IH|y v ρ IH|y a ρ IH]; simpl; auto;
    destruct (String.eqb x y); auto.
  simpl. f_equal. unfold unroll. symmetry. apply lift_unr.
Qed.

(** [lift_list] keeps the length. *)
Lemma vlen_lift vs : vlen (lift_list vs) = rlen vs.
Proof. induction vs; simpl; auto. Qed.

(** A lifted value is not a shadow. *)
Lemma lift_not_sh v s : lift v ≠ vl_sh s.
Proof. destruct v; simpl; discriminate. Qed.

(** The anchor that the interpreter selects for a binding is fresh for the
    lifted environment. *)
Lemma fresh_lift ρ : aan_nv (fun a => a ≠ F (S (rsup_env ρ))) (lift_env ρ).
Proof. apply sup_nf_nv. rewrite (proj1 (proj2 sup_lift)). lia. Qed.

(** ** More fuel for the interpreter *)

(** [ev_list] keeps its value for a function that gives each value of [f]. *)
Lemma ev_list_mono (f g : tm → renv → option rvl)
  (H : ∀ e ρ v, f e ρ = Some v → g e ρ = Some v) :
  ∀ es ρ vs, ev_list f es ρ = Some vs → ev_list g es ρ = Some vs.
Proof.
  induction es as [|e es IH]; simpl; intros ρ vs E; auto.
  destruct (f e ρ) as [v|] eqn:E1; try discriminate. rewrite (H _ _ _ E1).
  destruct (ev_list f es ρ) as [vs'|] eqn:E2; try discriminate.
  rewrite (IH _ _ E2). auto.
Qed.

(** [ev_sel] keeps its value for a function that gives each value of [f]. *)
Lemma ev_sel_mono (f g : tm → renv → option rvl)
  (H : ∀ e ρ v, f e ρ = Some v → g e ρ = Some v) :
  ∀ bs c vs ρ v, ev_sel f c vs bs ρ = Some v → ev_sel g c vs bs ρ = Some v.
Proof.
  induction bs as [|c' xs e bs IH]; simpl; intros c vs ρ v E; auto.
  destruct (_ && _); auto.
Qed.

(** [ev_step] keeps its value for a function that gives each value of [f]. *)
Lemma ev_step_mono (f g : tm → renv → option rvl)
  (H : ∀ e ρ v, f e ρ = Some v → g e ρ = Some v) :
  ∀ e ρ v, ev_step f e ρ = Some v → ev_step g e ρ = Some v.
Proof.
  intros e ρ v E. destruct e; simpl in *; auto.
  - destruct (f e1 ρ) as [[| |]|] eqn:E1; try discriminate.
    rewrite (H _ _ _ E1).
    destruct (f e2 ρ) as [a|] eqn:E2; try discriminate.
    rewrite (H _ _ _ E2). auto.
  - destruct (f e1 ρ) as [[| |]|] eqn:E1; try discriminate.
    rewrite (H _ _ _ E1). auto.
  - destruct (f e1 (ran x (F (S (rsup_env ρ))) ρ)) as [v1|] eqn:E1;
      try discriminate.
    rewrite (H _ _ _ E1).
    destruct (f e2 (rmu x (rclose 0 (S (rsup_env ρ)) v1) ρ)) as [[| |]|] eqn:E2;
      try discriminate.
    rewrite (H _ _ _ E2). auto.
  - destruct (ev_list f es ρ) as [vs|] eqn:E1; try discriminate.
    rewrite (ev_list_mono f g H _ _ _ E1). auto.
  - destruct (f e ρ) as [[| |]|] eqn:E1; try discriminate.
    rewrite (H _ _ _ E1). eapply ev_sel_mono; eauto.
Qed.

(** One more unit of fuel keeps a value of the interpreter. *)
Lemma ev_mono_S n : ∀ e ρ v, ev n e ρ = Some v → ev (S n) e ρ = Some v.
Proof.
  induction n; intros e ρ v E; [discriminate|].
  change (ev_step (ev (S n)) e ρ = Some v). change (ev_step (ev n) e ρ = Some v) in E.
  eapply ev_step_mono; eauto.
Qed.

(** More fuel keeps a value of the interpreter. *)
Lemma ev_mono n m (LE : n ≤ m) e ρ v (E : ev n e ρ = Some v) : ev m e ρ = Some v.
Proof. induction LE; auto using ev_mono_S. Qed.
