(** * The order on traces

    This file defines when a trace extends another trace, and proves that
    more fuel extends each trace of the semantics. A finished trace has no
    proper extension. So more fuel does not change a finished trace
    ([Conv.v]).

    ** Main definitions

    - [le_tr t t']: the trace [t'] extends [t]. That is, [t'] is [t] with a
      trace in the place of some [Bot]. The values of the 2 traces are equal.

    ** Main results

    - [le_total]: a trace that extends a finished trace is equal to it.
    - [le_bind], [le_link], [le_link_tr], [le_link_trace]: [bind] and linking
      are monotone.
    - [le_linkb], [le_linkv], [le_call], [le_den]: more fuel extends each
      trace of the semantics. *)
From Stdlib Require Import Utf8 String Bool Arith Lia List.
From Denot Require Import Syntax Anchor Domain Nominal Semantics Laws Wf.

(** The trace [t'] extends [t]. [le_brs] is the same relation on lists of
    branches. *)
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

(** The mutual form of [le_refl]. *)
Lemma le_refl_mut : (∀ t, le_tr t t) ∧ (∀ bs, le_brs bs bs).
Proof. apply tr_mutind; simpl; auto. Qed.

(** Each trace extends itself. *)
Lemma le_refl t : le_tr t t.
Proof. apply le_refl_mut. Qed.

(** The mutual form of [le_trans]. *)
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

(** The relation is transitive. *)
Lemma le_trans t t' t'' : le_tr t t' → le_tr t' t'' → le_tr t t''.
Proof. apply le_trans_mut. Qed.

(** The mutual form of [le_bind]. *)
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

(** [bind] is monotone in the continuation and in the trace. *)
Lemma le_bind k k' t t' (Hk : ∀ v, wf_vl v → le_tr (k v) (k' v))
  (Ht : wf_tr t) (LE : le_tr t t') : le_tr (bind k t) (bind k' t').
Proof. eapply le_bind_mut; eauto. Qed.

(** The mutual form of [le_tmap]. *)
Lemma le_tmap_mut g gs h :
  (∀ t t', le_tr t t' → le_tr (tmap g gs h t) (tmap g gs h t')) ∧
  (∀ bs bs', le_brs bs bs' → le_brs (tmap_brs g gs h bs) (tmap_brs g gs h bs')).
Proof.
  apply tr_mutind; simpl; auto.
  - intros v t' ->. reflexivity.
  - intros u t IH [| |u' t'|]; simpl; try tauto. intros [-> H]. auto.
  - intros s bs IH [| | |s' bs']; simpl; try tauto. intros [-> H]. auto.
  - intros bs' ->. reflexivity.
  - intros c n t bs IHt IHb [|c' n' t' bs']; simpl; try tauto.
    intros (-> & -> & Ht & Hb). auto.
Qed.

(** [tmap] is monotone. *)
Lemma le_tmap g gs h t t' : le_tr t t' → le_tr (tmap g gs h t) (tmap g gs h t').
Proof. apply le_tmap_mut. Qed.

(** [killg] is monotone. *)
Lemma le_killg ℓ t t' : le_tr t t' → le_tr (killg ℓ t) (killg ℓ t').
Proof. apply le_tmap. Qed.

(** A trace that extends a finished trace is equal to it. *)
Lemma le_total t : ∀ t' v, le_tr t t' → dest t = Some v → t' = t.
Proof.
  induction t; simpl; intros t' w LE D; try discriminate; auto.
  destruct t'; simpl in *; try tauto. destruct LE as [-> LE].
  f_equal. eauto.
Qed.

(** A trace that extends a finished trace has the same result. *)
Lemma le_dest t t' v (LE : le_tr t t') (D : dest t = Some v) : dest t' = Some v.
Proof. rewrite (le_total _ _ _ LE D). auto. Qed.

Section le_link.
  Context (cl cl' : nv → body → trace) (lk lk' : nv → vl → trace).
  Context (Hwf : ∀ σ b, wf_nv σ → wfb b → wf_tr (cl σ b)).
  Context (Hle : ∀ σ b, wf_nv σ → wfb b → le_tr (cl σ b) (cl' σ b)).
  Context (Hwfl : ∀ σ v, wf_nv σ → wf_vl v → wf_tr (lk σ v)).
  Context (Hlel : ∀ σ v, wf_nv σ → wf_vl v → le_tr (lk σ v) (lk' σ v)).
  Context (σ0 : nv) (Hσ0 : wf_nv σ0).

  (** ** Linking is monotone *)

  (** [ap] is monotone in the call function. *)
  Lemma le_ap f a (Hf : wf_vl f) (Ha : wf_vl a) : le_tr (ap cl f a) (ap cl' f a).
  Proof.
    destruct f; simpl in *; auto. destruct Hf. apply Hle; simpl; auto.
  Qed.

  (** Linking into a value is monotone in the call function [cl] and in the
      function [lk] for recursive values. *)
  Lemma le_link :
    (∀ s, wf_shdw s → le_tr (link_shdw cl lk σ0 s) (link_shdw cl' lk' σ0 s)) ∧
    (∀ σ, wf_nv σ → le_tr (link_nv cl lk σ0 σ) (link_nv cl' lk' σ0 σ)) ∧
    (∀ v, wf_vl v → le_tr (link_vl cl lk σ0 v) (link_vl cl' lk' σ0 v)) ∧
    (∀ vs, wf_vls vs → ∀ c, le_tr (link_vls cl lk σ0 c vs) (link_vls cl' lk' σ0 c vs)).
  Proof.
    destruct (wf_link cl lk Hwf Hwfl σ0 Hσ0) as (Ws & Wn & Wv & Wvs).
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
    - intros x w σ _ IHσ [Hw Hσ].
      assert (wf_vl (open_vl 0 (fresh σ0 w) w)) as Ho by (apply wf_open; auto).
      apply le_bind.
      + intros w' Hw'. apply le_bind; auto using le_refl.
      + apply wf_killg. auto.
      + apply le_killg. auto.
    - intros x a σ IH [Ha Hσ]. apply le_bind; auto using le_refl.
    - auto.
    - auto.
    - intros x b σ IH [Hb Hσ]. apply le_bind; auto using le_refl.
    - auto.
    - auto.
    - intros v vs IHv IHvs [Hv Hvs] c. apply le_bind; auto.
      intros v' Hv'. apply le_bind; auto using le_refl.
  Qed.

  (** Linking into a spine is monotone in [cl], in [lk] and in the trace. *)
  Lemma le_link_tr :
    (∀ t, wf_tr t → ∀ t', le_tr t t' →
       le_tr (link_tr cl lk σ0 t) (link_tr cl' lk' σ0 t')) ∧
    (∀ bs, wf_brs bs → ∀ bs', le_brs bs bs' →
       le_brs (link_brs cl lk σ0 bs) (link_brs cl' lk' σ0 bs') ∧
       ∀ c n, le_tr (link_sel cl lk σ0 c n bs) (link_sel cl' lk' σ0 c n bs')).
  Proof.
    destruct (wf_link cl lk Hwf Hwfl σ0 Hσ0) as (Ws & Wn & Wv & Wvs).
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

  (** Linking into a trace is monotone in [cl], in [lk] and in the trace. *)
  Lemma le_link_trace t t' (Ht : wf_tr t) (LE : le_tr t t') :
    le_tr (link_trace cl lk σ0 t) (link_trace cl' lk' σ0 t').
  Proof.
    unfold link_trace. apply le_bind.
    - intros. apply le_link; auto.
    - apply wf_link_tr; auto.
    - apply le_link_tr; auto.
  Qed.
End le_link.

(** ** More fuel extends each trace *)

(** One more unit of fuel extends the trace of each term, when it extends
    each [call]. *)
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
  - intros x e1 IH1 e2 IH2.
    assert (wf_nv (nv_an x (F 1) (nv_sh Init))) as Hσ1 by (simpl; auto).
    apply le_bind.
    + intros v Hv.
      assert (wf_nv (nv_mu x (close_vl 0 1 v) (nv_sh Init))) as Hσ.
      { simpl. split; auto. apply wf_close; auto. }
      apply le_bind; auto using le_refl.
    + apply wf_killg. auto.
    + apply le_killg. auto.
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

(** One more unit of fuel extends [linkb] and [linkv], by induction on the
    fuel. *)
Lemma le_linkbv_S n :
  (∀ σ b, wf_nv σ → wfb b → le_tr (linkb n σ b) (linkb (S n) σ b)) ∧
  (∀ σ v, wf_nv σ → wf_vl v → le_tr (linkv n σ v) (linkv (S n) σ v)).
Proof.
  induction n as [|n [IHb IHv]].
  - split; intros; [rewrite linkb_0|rewrite linkv_0]; simpl; auto.
  - assert (∀ σ b, wf_nv σ → wfb b → le_tr (call n σ b) (call (S n) σ b)) as Hle.
    { intros. rewrite !call_eq. simpl. auto. }
    assert (∀ σ b, wf_nv σ → wfb b → wf_tr (call n σ b)) as Hwf
        by (intros; apply wf_call; auto).
    assert (∀ σ v, wf_nv σ → wf_vl v → wf_tr (linkv n σ v)) as Hwfl
        by (intros; apply wf_linkv; auto).
    split.
    + intros σ b Hσ [e ->]. rewrite !linkb_S. unfold den.
      apply le_link_trace; auto.
      * apply wf_den.
      * apply le_denote; auto.
    + intros σ v Hσ Hv. rewrite !linkv_S. apply le_link; auto.
Qed.

(** One more unit of fuel extends [linkb]. *)
Lemma le_linkb_S n σ b : wf_nv σ → wfb b → le_tr (linkb n σ b) (linkb (S n) σ b).
Proof. apply le_linkbv_S. Qed.

(** One more unit of fuel extends [linkv]. *)
Lemma le_linkv_S n σ v : wf_nv σ → wf_vl v → le_tr (linkv n σ v) (linkv (S n) σ v).
Proof. apply le_linkbv_S. Qed.

(** One more unit of fuel extends [call]. *)
Lemma le_call_S n σ b (Hσ : wf_nv σ) (Hb : wfb b) :
  le_tr (call n σ b) (call (S n) σ b).
Proof. rewrite !call_eq. simpl. split; auto. apply le_linkb_S; auto. Qed.

(** One more unit of fuel extends the trace of a term. *)
Lemma le_denote_S n e : le_tr (denote n e) (denote (S n) e).
Proof. apply le_denote. intros. apply le_call_S; auto. Qed.

(** More fuel extends [linkb]. *)
Lemma le_linkb n m (LE : n ≤ m) σ b (Hσ : wf_nv σ) (Hb : wfb b) :
  le_tr (linkb n σ b) (linkb m σ b).
Proof.
  induction LE; [apply le_refl|].
  eapply le_trans; [eassumption|]. apply le_linkb_S; auto.
Qed.

(** More fuel extends [linkv]. *)
Lemma le_linkv n m (LE : n ≤ m) σ v (Hσ : wf_nv σ) (Hv : wf_vl v) :
  le_tr (linkv n σ v) (linkv m σ v).
Proof.
  induction LE; [apply le_refl|].
  eapply le_trans; [eassumption|]. apply le_linkv_S; auto.
Qed.

(** More fuel extends [call]. *)
Lemma le_call n m (LE : n ≤ m) σ b (Hσ : wf_nv σ) (Hb : wfb b) :
  le_tr (call n σ b) (call m σ b).
Proof. rewrite !call_eq. simpl. split; auto. apply le_linkb; auto. Qed.

(** More fuel extends the trace of a term. *)
Lemma le_den n m (LE : n ≤ m) e : le_tr (denote n e) (denote m e).
Proof.
  induction LE; [apply le_refl|].
  eapply le_trans; [eassumption|]. apply le_denote_S.
Qed.
