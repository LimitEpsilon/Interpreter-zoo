(** * Well-formed semantic objects

    A value is well formed when every closure in it carries the denotation
    of some term.  Everything the semantics produces is well formed, and
    this is what makes denotations increasing chains. *)
From Stdlib Require Import Utf8 String Bool Arith Lia List.
From Denot Require Import Syntax Domain Semantics Laws.

Definition wfb (b : body) : Prop := ∃ e, b = den e.

Fixpoint wf_shdw (s : shdw) : Prop :=
  match s with
  | Init => True
  | Read s' _ => wf_shdw s'
  | Call s' v => wf_shdw s' ∧ wf_vl v
  | Dstr s' _ _ => wf_shdw s'
  end
with wf_nv (σ : nv) : Prop :=
  match σ with
  | nv_mt => True
  | nv_sh s => wf_shdw s
  | nv_bd _ v σ' => wf_vl v ∧ wf_nv σ'
  end
with wf_vl (v : vl) : Prop :=
  match v with
  | vl_exp σ => wf_nv σ
  | vl_sh s => wf_shdw s
  | vl_clos _ b σ => wfb b ∧ wf_nv σ
  | vl_cstr _ vs => wf_vls vs
  end
with wf_vls (vs : vls) : Prop :=
  match vs with
  | vnil => True
  | vcons v vs' => wf_vl v ∧ wf_vls vs'
  end.

Fixpoint wf_tr (t : trace) : Prop :=
  match t with
  | Bot => True
  | Ret v => wf_vl v
  | Guard u t' => wf_vl u ∧ wf_tr t'
  | Match s bs => wf_shdw s ∧ wf_brs bs
  end
with wf_brs (bs : brs) : Prop :=
  match bs with
  | bnil => True
  | bcons _ _ t bs' => wf_tr t ∧ wf_brs bs'
  end.

Lemma wf_bind_mut k (Hk : ∀ v, wf_vl v → wf_tr (k v)) :
  (∀ t, wf_tr t → wf_tr (bind k t)) ∧ (∀ bs, wf_brs bs → wf_brs (bind_brs k bs)).
Proof. apply tr_mutind; simpl; intuition auto. Qed.

Lemma wf_bind k t (Hk : ∀ v, wf_vl v → wf_tr (k v)) (Ht : wf_tr t) : wf_tr (bind k t).
Proof. apply wf_bind_mut; auto. Qed.

Lemma wf_read x σ v (Hσ : wf_nv σ) (R : read x σ = Some v) : wf_vl v.
Proof.
  induction σ; simpl in *; try discriminate.
  - inversion R; subst. simpl. auto.
  - destruct (String.eqb x x0); [inversion R; subst|]; intuition auto.
Qed.

Lemma wf_vnth vs : ∀ i v, wf_vls vs → vnth i vs = Some v → wf_vl v.
Proof.
  induction vs as [|u vs IH]; simpl; intros i w Hw N; try discriminate.
  destruct Hw as [Hu Hvs]. destruct i as [|i].
  - inversion N; subst; auto.
  - eapply IH; eauto.
Qed.

Lemma wf_bindV xs : ∀ vs σ, wf_vls vs → wf_nv σ → wf_nv (bindV xs vs σ).
Proof.
  induction xs as [|x xs IH]; simpl; intros vs σ Hvs Hσ; auto.
  destruct vs as [|v vs]; simpl in *; auto.
  destruct Hvs. split; auto.
Qed.

Lemma wf_bindD xs s c : ∀ i σ, wf_shdw s → wf_nv σ → wf_nv (bindD xs s c i σ).
Proof.
  induction xs as [|x xs IH]; simpl; intros i σ Hs Hσ; auto.
Qed.

Lemma wf_dest t v (Ht : wf_tr t) (D : dest t = Some v) : wf_vl v.
Proof.
  induction t; simpl in *; try discriminate; intuition auto.
  inversion D; subst; auto.
Qed.

Ltac wf_step :=
  match goal with
  | |- wf_tr (bind _ _) => apply wf_bind; [intros ? ?|]
  | H : _ ∧ _ |- _ => destruct H
  | |- _ ∧ _ => split
  | |- wf_tr (on_env _ ?m) => destruct m; simpl
  | |- wf_tr (on_mod _ ?m) => destruct m; simpl
  | |- wf_tr (on_cstr _ ?m) => destruct m; simpl
  | |- wf_tr (match ?m with _ => _ end) => destruct m eqn:?; simpl
  | |- wf_tr (if ?b then _ else _) => destruct b eqn:?; simpl
  | _ => progress (simpl in *)
  | _ => solve [eauto using wf_read, wf_vnth, wf_bindV, wf_bindD]
  end.
Ltac wf_tac := repeat wf_step.

Section wf_link.
  Context (cl : nv → body → trace).
  Context (Hcl : ∀ σ b, wf_nv σ → wfb b → wf_tr (cl σ b)).
  Context (σ0 : nv) (Hσ0 : wf_nv σ0).

  Lemma wf_ap f a (Hf : wf_vl f) (Ha : wf_vl a) : wf_tr (ap cl f a).
  Proof. destruct f; simpl in *; intuition auto. apply Hcl; simpl; auto. Qed.

  Lemma wf_rd x m (Hm : wf_vl m) : wf_tr (rd x m).
  Proof. unfold rd. destruct m; wf_tac. Qed.

  Lemma wf_ds c i m (Hm : wf_vl m) : wf_tr (ds c i m).
  Proof. unfold ds. destruct m; wf_tac. Qed.

  Lemma wf_link :
    (∀ s, wf_shdw s → wf_tr (link_shdw cl σ0 s)) ∧
    (∀ σ, wf_nv σ → wf_tr (link_nv cl σ0 σ)) ∧
    (∀ v, wf_vl v → wf_tr (link_vl cl σ0 v)) ∧
    (∀ vs, wf_vls vs → ∀ c, wf_tr (link_vls cl σ0 c vs)).
  Proof.
    apply val_mutind; intros; simpl in *;
      repeat first [apply wf_rd | apply wf_ds | apply wf_ap | wf_step]; auto.
  Qed.

  Lemma wf_link_tr :
    (∀ t, wf_tr t → wf_tr (link_tr cl σ0 t)) ∧
    (∀ bs, wf_brs bs →
       wf_brs (link_brs cl σ0 bs) ∧ ∀ c n, wf_tr (link_sel cl σ0 c n bs)).
  Proof.
    destruct wf_link as (Hs & Hn & Hv & Hvs).
    apply tr_mutind; simpl.
    - auto.
    - auto.
    - intros u t IH [Hu Ht]. wf_tac; auto.
    - intros s bs IH [Hs' Hb]. destruct (IH Hb) as [Hb1 Hb2]. wf_tac; auto.
    - auto.
    - intros c n t bs IHt IHb [Ht Hb]. destruct (IHb Hb) as [Hb1 Hb2].
      repeat split; auto. intros c' n'. destruct (_ && _); auto.
  Qed.

  Lemma wf_link_trace t (Ht : wf_tr t) : wf_tr (link_trace cl σ0 t).
  Proof.
    unfold link_trace. apply wf_bind.
    - intros. apply wf_link; auto.
    - apply wf_link_tr; auto.
  Qed.
End wf_link.

(** Denotations are well formed, at every approximation. *)

Lemma wf_denote n (Hcl : ∀ σ b, wf_nv σ → wfb b → wf_tr (call n σ b)) :
  (∀ e, wf_tr (denote n e)) ∧
  (∀ es c, wf_tr (denote_list n c es)) ∧
  (∀ bs, (∀ c vs, wf_vls vs → wf_tr (denote_sel n c vs bs)) ∧
         (∀ s, wf_shdw s → wf_brs (denote_brs n s bs))).
Proof.
  assert (∀ e, wfb (fun m => denote m e)) as Hb by (intros e; exists e; reflexivity).
  apply tm_mutind; intros; simpl;
    repeat first [progress intros | apply wf_ap | apply Hcl | wf_step]; auto;
    first [apply wf_bindV | apply wf_bindD]; simpl; auto.
Qed.

Lemma wf_linkb n : ∀ σ b, wf_nv σ → wfb b → wf_tr (linkb n σ b).
Proof.
  induction n; intros σ b Hσ [e ->].
  - rewrite linkb_0. simpl; auto.
  - assert (∀ σ b, wf_nv σ → wfb b → wf_tr (call n σ b)) as Hcl.
    { intros. rewrite call_eq. simpl. auto. }
    rewrite linkb_S. apply wf_link_trace; auto.
    unfold den. apply wf_denote; auto.
Qed.

Lemma wf_call n σ b (Hσ : wf_nv σ) (Hb : wfb b) : wf_tr (call n σ b).
Proof. rewrite call_eq. simpl. split; auto. apply wf_linkb; auto. Qed.

Lemma wf_den n e : wf_tr (denote n e).
Proof. apply wf_denote. intros. apply wf_call; auto. Qed.

Lemma wfb_den e : wfb (den e).
Proof. exists e; reflexivity. Qed.
