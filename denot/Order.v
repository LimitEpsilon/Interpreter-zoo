(** * The approximation order, and monotonicity in the fuel

    [le_tr t t'] : [t'] is [t] with some of its [Bot]s filled in.  Values are
    compared by equality, so a finished trace is maximal. *)
From Stdlib Require Import Utf8 String Bool Arith Lia List.
From Denot Require Import Syntax Domain Semantics Laws Wf.

Fixpoint le_tr (t t' : trace) : Prop :=
  match t with
  | Bot => True
  | Ret v => t' = Ret v
  | Guard u t1 =>
    match t' with Guard u' t1' => u = u' ∧ le_tr t1 t1' | _ => False end
  | Match s bs =>
    match t' with Match s' bs' => s = s' ∧ le_brs bs bs' | _ => False end
  end
with le_brs (bs bs' : brs) : Prop :=
  match bs with
  | bnil => bs' = bnil
  | bcons c n t bs1 =>
    match bs' with
    | bcons c' n' t' bs1' => c = c' ∧ n = n' ∧ le_tr t t' ∧ le_brs bs1 bs1'
    | _ => False
    end
  end.

Lemma le_refl_mut : (∀ t, le_tr t t) ∧ (∀ bs, le_brs bs bs).
Proof. apply tr_mutind; simpl; auto. Qed.

Lemma le_refl t : le_tr t t.
Proof. apply le_refl_mut. Qed.

Lemma le_trans_mut :
  (∀ t t' t'', le_tr t t' → le_tr t' t'' → le_tr t t'') ∧
  (∀ bs bs' bs'', le_brs bs bs' → le_brs bs' bs'' → le_brs bs bs'').
Proof.
  apply tr_mutind; simpl; auto.
  - intros v t' t'' -> H. auto.
  - intros u t IH [| |u' t'|] t''; simpl; try tauto.
    intros [-> H]. destruct t''; simpl; try tauto. intros [-> H']. eauto.
  - intros s bs IH [| | |s' bs'] t''; simpl; try tauto.
    intros [-> H]. destruct t''; simpl; try tauto. intros [-> H']. eauto.
  - intros bs' bs'' -> H. auto.
  - intros c n t bs IHt IHb [|c' n' t' bs'] bs''; simpl; try tauto.
    intros (-> & -> & Ht & Hb). destruct bs''; simpl; try tauto.
    intros (-> & -> & Ht' & Hb'). eauto 6.
Qed.

Lemma le_trans t t' t'' : le_tr t t' → le_tr t' t'' → le_tr t t''.
Proof. apply le_trans_mut. Qed.

Lemma le_bind_mut k k' (Hk : ∀ v, wf_vl v → le_tr (k v) (k' v)) :
  (∀ t, wf_tr t → ∀ t', le_tr t t' → le_tr (bind k t) (bind k' t')) ∧
  (∀ bs, wf_brs bs → ∀ bs', le_brs bs bs' → le_brs (bind_brs k bs) (bind_brs k' bs')).
Proof.
  apply tr_mutind; simpl; auto.
  - intros v Hv t' ->. simpl. auto.
  - intros u t IH [Hu Ht] [| |u' t'|]; simpl; try tauto. intros [-> H]. auto.
  - intros s bs IH [Hs Hb] [| | |s' bs']; simpl; try tauto. intros [-> H]. auto.
  - intros _ bs' ->. simpl. auto.
  - intros c n t bs IHt IHb [Ht Hb] [|c' n' t' bs']; simpl; try tauto.
    intros (-> & -> & Ht' & Hb'). auto.
Qed.

Lemma le_bind k k' t t' (Hk : ∀ v, wf_vl v → le_tr (k v) (k' v))
  (Ht : wf_tr t) (LE : le_tr t t') : le_tr (bind k t) (bind k' t').
Proof. eapply le_bind_mut; eauto. Qed.

(** A finished trace is maximal. *)
Lemma le_total t : ∀ t' v, le_tr t t' → dest t = Some v → t' = t.
Proof.
  induction t; simpl; intros t' w LE D; try discriminate; auto.
  destruct t'; simpl in *; try tauto. destruct LE as [-> LE].
  f_equal. eauto.
Qed.

Lemma le_dest t t' v (LE : le_tr t t') (D : dest t = Some v) : dest t' = Some v.
Proof. rewrite (le_total _ _ _ LE D). auto. Qed.

(** ** Linking is monotone in the call function and in the trace *)

Section le_link.
  Context (cl cl' : nv → body → trace).
  Context (Hwf : ∀ σ b, wf_nv σ → wfb b → wf_tr (cl σ b)).
  Context (Hle : ∀ σ b, wf_nv σ → wfb b → le_tr (cl σ b) (cl' σ b)).
  Context (σ0 : nv) (Hσ0 : wf_nv σ0).

  Lemma le_ap f a (Hf : wf_vl f) (Ha : wf_vl a) : le_tr (ap cl f a) (ap cl' f a).
  Proof.
    destruct f; simpl in *; auto. destruct Hf. apply Hle; simpl; auto.
  Qed.

  Lemma le_link :
    (∀ s, wf_shdw s → le_tr (link_shdw cl σ0 s) (link_shdw cl' σ0 s)) ∧
    (∀ σ, wf_nv σ → le_tr (link_nv cl σ0 σ) (link_nv cl' σ0 σ)) ∧
    (∀ v, wf_vl v → le_tr (link_vl cl σ0 v) (link_vl cl' σ0 v)) ∧
    (∀ vs, wf_vls vs → ∀ c, le_tr (link_vls cl σ0 c vs) (link_vls cl' σ0 c vs)).
  Proof.
    destruct (wf_link cl Hwf σ0 Hσ0) as (Ws & Wn & Wv & Wvs).
    apply val_mutind; simpl.
    - auto.
    - intros s x IH Hs. apply le_bind; auto using le_refl.
    - intros s v IHs IHv [Hs Hv]. apply le_bind; auto.
      intros f Hf. apply le_bind; auto. intros a Ha. apply le_ap; auto.
    - intros s c i IH Hs. apply le_bind; auto using le_refl.
    - auto.
    - intros s IH Hs. apply le_bind; auto using le_refl.
    - intros x v σ IHv IHσ [Hv Hσ]. apply le_bind; auto.
      intros v' Hv'. apply le_bind; auto using le_refl.
    - auto.
    - auto.
    - intros x b σ IH [Hb Hσ]. apply le_bind; auto using le_refl.
    - auto.
    - auto.
    - intros v vs IHv IHvs [Hv Hvs] c. apply le_bind; auto.
      intros v' Hv'. apply le_bind; auto using le_refl.
  Qed.

  Lemma le_link_tr :
    (∀ t, wf_tr t → ∀ t', le_tr t t' →
       le_tr (link_tr cl σ0 t) (link_tr cl' σ0 t')) ∧
    (∀ bs, wf_brs bs → ∀ bs', le_brs bs bs' →
       le_brs (link_brs cl σ0 bs) (link_brs cl' σ0 bs') ∧
       ∀ c n, le_tr (link_sel cl σ0 c n bs) (link_sel cl' σ0 c n bs')).
  Proof.
    destruct (wf_link cl Hwf σ0 Hσ0) as (Ws & Wn & Wv & Wvs).
    destruct le_link as (Ls & Ln & Lv & Lvs).
    apply tr_mutind; simpl.
    - auto.
    - intros v Hv t' ->. simpl. auto.
    - intros u t IH [Hu Ht] [| |u' t'|]; simpl; try tauto. intros [<- LE].
      apply le_bind; auto. intros w Hw. simpl. auto.
    - intros s bs IH [Hs Hb] [| | |s' bs']; simpl; try tauto. intros [<- LE].
      destruct (IH Hb _ LE) as [IH1 IH2].
      apply le_bind; auto. intros m Hm. destruct m; simpl; auto.
    - intros _ bs' ->. simpl. auto.
    - intros c n t bs IHt IHb [Ht Hb] [|c' n' t' bs']; simpl; try tauto.
      intros (<- & <- & LEt & LEb). destruct (IHb Hb _ LEb) as [IH1 IH2].
      repeat split; auto. intros c0 n0. destruct (_ && _); auto.
  Qed.

  Lemma le_link_trace t t' (Ht : wf_tr t) (LE : le_tr t t') :
    le_tr (link_trace cl σ0 t) (link_trace cl' σ0 t').
  Proof.
    unfold link_trace. apply le_bind.
    - intros. apply le_link; auto.
    - apply wf_link_tr; auto.
    - apply le_link_tr; auto.
  Qed.
End le_link.

(** ** Denotations are increasing chains *)

Lemma le_denote n
  (Hle : ∀ σ b, wf_nv σ → wfb b → le_tr (call n σ b) (call (S n) σ b)) :
  (∀ e, le_tr (denote n e) (denote (S n) e)) ∧
  (∀ es c, le_tr (denote_list n c es) (denote_list (S n) c es)) ∧
  (∀ bs, (∀ c vs, wf_vls vs →
            le_tr (denote_sel n c vs bs) (denote_sel (S n) c vs bs)) ∧
         (∀ s, wf_shdw s → le_brs (denote_brs n s bs) (denote_brs (S n) s bs))).
Proof.
  assert (∀ e, wfb (fun m => denote m e)) as Hb by (intros e; exists e; reflexivity).
  assert (∀ e, wf_tr (denote n e)) as Wd by (intros; apply wf_den).
  assert (∀ σ b, wf_nv σ → wfb b → wf_tr (call n σ b)) as Wc
      by (intros; apply wf_call; auto).
  apply tm_mutind; simpl.
  - auto.
  - auto.
  - intros e1 IH1 e2 IH2. apply le_bind; auto. intros f Hf.
    apply le_bind; auto. intros a Ha. apply le_ap; auto.
  - intros e1 IH1 e2 IH2. apply le_bind; auto. intros m Hm.
    destruct m; simpl; auto.
  - auto.
  - intros x e1 IH1 e2 IH2. apply le_bind; auto. intros v Hv.
    assert (wf_nv (nv_bd x v (nv_sh Init))) as Hσ by (simpl; auto).
    apply le_bind; auto using le_refl.
  - auto.
  - intros e IH bs [IHs IHb]. apply le_bind; auto. intros m Hm.
    destruct m; simpl; auto.
  - auto.
  - intros e IH es IHes c. apply le_bind; auto. intros v Hv.
    apply le_bind; auto using le_refl.
    assert (∀ es c, wf_tr (denote_list n c es)) as Wl
        by (apply wf_denote; auto).
    auto.
  - auto.
  - intros c xs e IH bs [IHs IHb]. split.
    + intros c0 vs Hvs. destruct (_ && _); auto.
      apply Hle; auto. apply wf_bindV; simpl; auto.
    + intros s Hs. repeat split; auto.
      apply Hle; auto. apply wf_bindD; simpl; auto.
Qed.

Lemma le_linkb_S n : ∀ σ b, wf_nv σ → wfb b → le_tr (linkb n σ b) (linkb (S n) σ b).
Proof.
  induction n; intros σ b Hσ Hb.
  - rewrite linkb_0. simpl. auto.
  - assert (∀ σ b, wf_nv σ → wfb b → le_tr (call n σ b) (call (S n) σ b)) as Hle.
    { intros. rewrite !call_eq. simpl. auto. }
    destruct Hb as [e ->]. rewrite !linkb_S. unfold den.
    apply le_link_trace; auto.
    + intros. apply wf_call; auto.
    + apply wf_den.
    + apply le_denote; auto.
Qed.

Lemma le_call_S n σ b (Hσ : wf_nv σ) (Hb : wfb b) :
  le_tr (call n σ b) (call (S n) σ b).
Proof. rewrite !call_eq. simpl. split; auto. apply le_linkb_S; auto. Qed.

Lemma le_denote_S n e : le_tr (denote n e) (denote (S n) e).
Proof. apply le_denote. intros. apply le_call_S; auto. Qed.

Lemma le_linkb n m (LE : n ≤ m) σ b (Hσ : wf_nv σ) (Hb : wfb b) :
  le_tr (linkb n σ b) (linkb m σ b).
Proof.
  induction LE; [apply le_refl|].
  eapply le_trans; [eassumption|]. apply le_linkb_S; auto.
Qed.

Lemma le_call n m (LE : n ≤ m) σ b (Hσ : wf_nv σ) (Hb : wfb b) :
  le_tr (call n σ b) (call m σ b).
Proof. rewrite !call_eq. simpl. split; auto. apply le_linkb; auto. Qed.

Lemma le_den n m (LE : n ≤ m) e : le_tr (denote n e) (denote m e).
Proof.
  induction LE; [apply le_refl|].
  eapply le_trans; [eassumption|]. apply le_denote_S.
Qed.
