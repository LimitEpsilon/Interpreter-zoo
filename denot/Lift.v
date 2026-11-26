(** * Reference values as semantic values

    [lift] replaces the syntax inside a closure by its denotation.  The image
    of [lift] contains no shadows, so linking leaves it alone. *)
From Stdlib Require Import Utf8 String Bool Arith Lia List.
From Denot Require Import Syntax Domain Semantics Laws Wf Order Conv Reference.

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
  end
with lift_list (vs : rvls) : vls :=
  match vs with
  | rvnil => vnil
  | rvcons v vs' => vcons (lift v) (lift_list vs')
  end.

Lemma wf_lift :
  (∀ v, wf_vl (lift v)) ∧ (∀ ρ, wf_nv (lift_env ρ)) ∧ (∀ vs, wf_vls (lift_list vs)).
Proof. apply ref_mutind; simpl; auto using wfb_den. Qed.

Lemma wf_lift_env ρ : wf_nv (lift_env ρ).
Proof. apply wf_lift. Qed.

Lemma read_lift x ρ : read x (lift_env ρ) = option_map lift (rread x ρ).
Proof.
  induction ρ as [|y v ρ IH]; simpl; auto. destruct (String.eqb x y); auto.
Qed.

Lemma vlen_lift vs : vlen (lift_list vs) = rlen vs.
Proof. induction vs; simpl; auto. Qed.

(** Linking does nothing to a lifted value. *)
Lemma link_lift cl σ0 :
  (∀ v, link_vl cl σ0 (lift v) = Ret (lift v)) ∧
  (∀ ρ, link_nv cl σ0 (lift_env ρ) = Ret (vl_exp (lift_env ρ))) ∧
  (∀ vs c, link_vls cl σ0 c (lift_list vs) = Ret (vl_cstr c (lift_list vs))).
Proof.
  apply ref_mutind; simpl; auto.
  - intros x e ρ IH. rewrite IH. reflexivity.
  - intros x v IHv ρ IHρ. rewrite IHv. simpl. rewrite IHρ. reflexivity.
  - intros v IHv vs IHvs c. rewrite IHv. simpl. rewrite IHvs. reflexivity.
Qed.

(** Nothing in the image of [lift] is a shadow. *)
Lemma lift_not_sh v s : lift v ≠ vl_sh s.
Proof. destruct v; simpl; discriminate. Qed.

(** ** The reference interpreter is monotone in its fuel *)

Lemma ev_list_mono (f g : tm → renv → option rvl)
  (H : ∀ e ρ v, f e ρ = Some v → g e ρ = Some v) :
  ∀ es ρ vs, ev_list f es ρ = Some vs → ev_list g es ρ = Some vs.
Proof.
  induction es as [|e es IH]; simpl; intros ρ vs E; auto.
  destruct (f e ρ) as [v|] eqn:E1; try discriminate. rewrite (H _ _ _ E1).
  destruct (ev_list f es ρ) as [vs'|] eqn:E2; try discriminate.
  rewrite (IH _ _ E2). auto.
Qed.

Lemma ev_sel_mono (f g : tm → renv → option rvl)
  (H : ∀ e ρ v, f e ρ = Some v → g e ρ = Some v) :
  ∀ bs c vs ρ v, ev_sel f c vs bs ρ = Some v → ev_sel g c vs bs ρ = Some v.
Proof.
  induction bs as [|c' xs e bs IH]; simpl; intros c vs ρ v E; auto.
  destruct (_ && _); auto.
Qed.

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
  - destruct (f e1 ρ) as [v1|] eqn:E1; try discriminate.
    rewrite (H _ _ _ E1).
    destruct (f e2 (rcons x v1 ρ)) as [[| |]|] eqn:E2; try discriminate.
    rewrite (H _ _ _ E2). auto.
  - destruct (ev_list f es ρ) as [vs|] eqn:E1; try discriminate.
    rewrite (ev_list_mono f g H _ _ _ E1). auto.
  - destruct (f e ρ) as [[| |]|] eqn:E1; try discriminate.
    rewrite (H _ _ _ E1). eapply ev_sel_mono; eauto.
Qed.

Lemma ev_mono_S n : ∀ e ρ v, ev n e ρ = Some v → ev (S n) e ρ = Some v.
Proof.
  induction n; intros e ρ v E; [discriminate|].
  change (ev_step (ev (S n)) e ρ = Some v). change (ev_step (ev n) e ρ = Some v) in E.
  eapply ev_step_mono; eauto.
Qed.

Lemma ev_mono n m (LE : n ≤ m) e ρ v (E : ev n e ρ = Some v) : ev m e ρ = Some v.
Proof. induction LE; auto using ev_mono_S. Qed.
