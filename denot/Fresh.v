(** * Linking adds no free anchor

    This file proves that an anchor that is fresh for the environment and for
    the value is fresh for each value of the linked trace. The dead anchor is
    the exception, because linking kills an anchor when it closes a recursive
    value. [Equiv.v] and [Subst.v] use this bound to rename and to replace
    anchors.

    ** Main results

    - [nf_link], [nf_link_tr], [nf_link_trace]: the bound for linking, for
      each call function and each function for recursive values that satisfy
      it.
    - [nf_linkb], [nf_linkv], [nf_call]: the bound at each fuel.
    - [nf_den]: each anchor but the dead anchor is fresh for the trace of a
      term. *)
From Stdlib Require Import Utf8 String Bool Arith Lia List.
From Denot Require Import Syntax Anchor Domain Nominal Semantics Laws Wf.
Set Warnings "-notation-for-abbreviation".

(** ** The dead anchor *)

(** The trivial predicate holds of each anchor. *)
Lemma aan_True v : aan_vl (fun _ => True) v.
Proof. induction v using vl_ind1; simpl in *; auto. Qed.

(** [kap ℓ] keeps each name but [ℓ]. *)
Lemma kap_fix ℓ x (NE : x ≠ ℓ) : kap ℓ x = x.
Proof. unfold kap. apply Nat.eqb_neq in NE. rewrite NE. reflexivity. Qed.

(** [kap ℓ] takes [ℓ] to the dead anchor. *)
Lemma kap_self ℓ : kap ℓ ℓ = 0.
Proof. unfold kap. rewrite Nat.eqb_refl. reflexivity. Qed.

(** [kap ℓ] keeps the dead anchor. *)
Lemma kap_0 ℓ : kap ℓ 0 = 0.
Proof. unfold kap. destruct (Nat.eqb 0 ℓ); reflexivity. Qed.

(** After [kap ℓ], the anchor [ℓ] is fresh. *)
Lemma nf_kap ℓ v k (NZ : ℓ ≠ 0) : nf_vl ℓ (am_vl (fren (kap ℓ)) k v).
Proof.
  apply nf_ren. eapply aan_impl; [|apply aan_True].
  intros a _ z _. unfold kap. destruct (Nat.eqb z ℓ) eqn:E; [congruence|].
  apply Nat.eqb_neq in E. exact E.
Qed.

(** [kap ℓ] keeps each anchor but the dead anchor fresh. *)
Lemma nf_kap_other ℓ x v k (NZ : x ≠ 0) :
  nf_vl x v → nf_vl x (am_vl (fren (kap ℓ)) k v).
Proof.
  intros H. apply nf_ren. eapply aan_impl; [|exact H].
  intros a Ha z ->. unfold kap. destruct (Nat.eqb z ℓ); congruence.
Qed.

(** ** Traces *)

(** 2 instances of [tall] give the instance for the conjunctions. *)
Lemma tall_and_mut (Pg Pg' : vl → Prop) (Ps Ps' : shdw → Prop) (Pl Pl' : vl → Prop) :
  (∀ t, tall Pg Ps Pl t → tall Pg' Ps' Pl' t →
        tall (fun u => Pg u ∧ Pg' u) (fun s => Ps s ∧ Ps' s) (fun v => Pl v ∧ Pl' v) t) ∧
  (∀ bs, tall_brs Pg Ps Pl bs → tall_brs Pg' Ps' Pl' bs →
         tall_brs (fun u => Pg u ∧ Pg' u) (fun s => Ps s ∧ Ps' s)
           (fun v => Pl v ∧ Pl' v) bs).
Proof. apply tr_mutind; simpl; intuition auto. Qed.

(** An instance of [tall] for a well-formed trace also holds with "well
    formed" at each value. *)
Lemma tall_wf (Pg : vl → Prop) (Ps : shdw → Prop) (Pl : vl → Prop) t :
  wf_tr t → tall Pg Ps Pl t →
  tall (fun u => wf_vl u ∧ Pg u) (fun s => wf_shdw s ∧ Ps s) (fun v => wf_vl v ∧ Pl v) t.
Proof. intros W H. apply tall_and_mut; auto. apply wf_tall; auto. Qed.

(** An anchor is fresh for [bind k t] when it is fresh for [t] and for [k v]
    at each leaf [v]. *)
Lemma nft_bind x k t (W : wf_tr t) (N : nft x t)
  (Hk : ∀ v, wf_vl v → nf_vl x v → nft x (k v)) : nft x (bind k t).
Proof.
  eapply tall_bind with (Q := fun v => wf_vl v ∧ nf_vl x v).
  - intros v [? ?]; auto.
  - eapply tall_impl; [| | |apply tall_wf; eassumption]; simpl; tauto.
Qed.

(** [killg] keeps each anchor but the dead anchor fresh. *)
Lemma nft_killg x ℓ t (NZ : x ≠ 0) : nft x t → nft x (killg ℓ t).
Proof.
  intros H. unfold killg. apply tall_tmap.
  eapply tall_impl; [| | |exact H]; simpl; auto.
  - intros u Hu. apply nf_kap_other; auto.
  - intros s Hs. apply (nf_kap_other ℓ x (vl_sh s) 0 NZ Hs).
Qed.

(** [bindV] keeps an anchor fresh. *)
Lemma nf_bindV x xs : ∀ vs σ, nf_vls x vs → nf_nv x σ → nf_nv x (bindV xs vs σ).
Proof.
  induction xs as [|y xs IH]; simpl; intros vs σ Hvs Hσ; auto.
  destruct vs as [|v vs]; simpl in *; auto. destruct Hvs. split; auto.
Qed.

(** [bindD] keeps an anchor fresh. *)
Lemma nf_bindD x xs s c : ∀ i σ, nf_shdw x s → nf_nv x σ → nf_nv x (bindD xs s c i σ).
Proof. induction xs as [|y xs IH]; simpl; intros i σ Hs Hσ; auto. Qed.

Section nf_link.
  Context (cl : nv → body → trace) (lk : nv → vl → trace).
  Context (Wcl : ∀ σ b, wf_nv σ → wfb b → wf_tr (cl σ b)).
  Context (Wlk : ∀ σ v, wf_nv σ → wf_vl v → wf_tr (lk σ v)).
  Context (x : loc) (NZ : x ≠ 0).
  Context (Ncl : ∀ σ b, wf_nv σ → wfb b → nf_nv x σ → nft x (cl σ b)).
  Context (Nlk : ∀ σ v, wf_nv σ → wf_vl v → nf_nv x σ → nf_vl x v → nft x (lk σ v)).
  Context (σ0 : nv) (Wσ0 : wf_nv σ0) (Nσ0 : nf_nv x σ0).

  (** ** Linking *)

  (** The anchor [x] stays fresh through [ap]. *)
  Lemma nf_ap f a (Wf : wf_vl f) (Wa : wf_vl a) (Nf : nf_vl x f) (Na : nf_vl x a) :
    nft x (ap cl f a).
  Proof.
    destruct f; simpl in *; auto. destruct Wf. apply Ncl; simpl; auto.
  Qed.

  (** The anchor [x] stays fresh through a read. *)
  Lemma nf_rd y m (Wm : wf_vl m) (Nm : nf_vl x m) : nft x (rd y m).
  Proof.
    unfold rd. destruct m; simpl in *; auto.
    destruct (read y σ) eqn:R; simpl; auto. split; auto.
    eapply read_aan; eauto.
  Qed.

  (** The anchor [x] stays fresh through a field. *)
  Lemma nf_ds c i m (Wm : wf_vl m) (Nm : nf_vl x m) : nft x (ds c i m).
  Proof.
    unfold ds. destruct m; simpl in *; auto.
    destruct (String.eqb c c0); simpl; auto.
    destruct (vnth i vs) eqn:N; simpl; auto. split; auto.
    eapply vnth_aan; eauto.
  Qed.

  (** The anchor [x] is fresh for the linking into a value, when it is fresh
      for the environment and for the value. *)
  Lemma nf_link :
    (∀ s, wf_shdw s → nf_shdw x s → nft x (link_shdw cl lk σ0 s)) ∧
    (∀ σ, wf_nv σ → nf_nv x σ → nft x (link_nv cl lk σ0 σ)) ∧
    (∀ v, wf_vl v → nf_vl x v → nft x (link_vl cl lk σ0 v)) ∧
    (∀ vs, wf_vls vs → nf_vls x vs → ∀ c, nft x (link_vls cl lk σ0 c vs)).
  Proof.
    destruct (wf_link cl lk Wcl Wlk σ0 Wσ0) as (Ws & Wn & Wv & Wvs).
    apply val_mutind; simpl.
    - auto.
    - intros s y IH W N. apply nft_bind; auto. intros; apply nf_rd; auto.
    - intros s v IHs IHv [W1 W2] [N1 N2]. apply nft_bind; auto.
      intros f Wf Nf. apply nft_bind; auto. intros a Wa Na. apply nf_ap; auto.
    - intros s c i IH W N. apply nft_bind; auto. intros; apply nf_ds; auto.
    - auto.
    - intros s IH W N. apply nft_bind; auto.
      intros m Wm Nm. destruct m; simpl in *; auto.
    - intros y v σ IHv IHσ [W1 W2] [N1 N2]. apply nft_bind; auto.
      intros v' Wv' Nv'. apply nft_bind; auto.
      intros m Wm Nm. destruct m; simpl in *; auto.
    - (* The case of a recursive value. *)
      intros y w σ _ IHσ [W1 W2] [N1 N2].
      set (ℓ := fresh σ0 w).
      assert (wf_vl (open_vl 0 ℓ w)) as Wo by (apply wf_open; auto).
      eapply tall_bind with
        (Q := fun w' => wf_vl w' ∧ nf_vl x (close_vl 0 ℓ w')).
      + intros w' [Ww' Nw']. apply nft_bind; auto.
        intros m Wm Nm. destruct m; simpl in *; auto.
      + unfold killg. apply tall_tmap.
        destruct (Nat.eq_dec x ℓ) as [E|NE].
        * (* [x] is the anchor of this recursive value. *)
          subst x. eapply tall_impl; [| | |apply wf_tall; apply Wlk; auto]; simpl.
          -- intros u _. apply nf_kap; auto.
          -- intros s _. apply (nf_kap ℓ (vl_sh s) 0 NZ).
          -- intros v Wv'. split; auto. apply nf_close_self.
        * assert (nft x (lk σ0 (open_vl 0 ℓ w))) as N.
          { apply Nlk; auto. apply nf_open; auto. }
          eapply tall_impl; [| | |apply tall_wf; [apply Wlk; auto|exact N]]; simpl.
          -- intros u [_ Hu]. apply nf_kap_other; auto.
          -- intros s [_ Hs]. apply (nf_kap_other ℓ x (vl_sh s) 0 NZ Hs).
          -- intros v [Wv' Nv']. split; auto. apply nf_close; auto.
    - intros y a σ IH [W1 W2] [N1 N2]. apply nft_bind; auto.
      intros m Wm Nm. destruct m; simpl in *; auto.
    - auto.
    - auto.
    - intros y b σ IH [W1 W2] N. apply nft_bind; auto.
      intros m Wm Nm. destruct m; simpl in *; auto.
    - auto.
    - auto.
    - intros v vs IHv IHvs [W1 W2] [N1 N2] c. apply nft_bind; auto.
      intros v' Wv' Nv'. apply nft_bind; auto.
      intros m Wm Nm. destruct m; simpl in *; auto.
  Qed.

  (** The anchor [x] is fresh for the linking into a spine, when it is fresh
      for the environment and for the trace. *)
  Lemma nf_link_tr :
    (∀ t, wf_tr t → nft x t → nft x (link_tr cl lk σ0 t)) ∧
    (∀ bs, wf_brs bs →
       tall_brs (aan_vl (fun a => a ≠ F x)) (aan_shdw (fun a => a ≠ F x))
         (aan_vl (fun a => a ≠ F x)) bs →
       tall_brs (aan_vl (fun a => a ≠ F x)) (aan_shdw (fun a => a ≠ F x))
         (aan_vl (fun a => a ≠ F x)) (link_brs cl lk σ0 bs) ∧
       ∀ c n, nft x (link_sel cl lk σ0 c n bs)).
  Proof.
    destruct (wf_link cl lk Wcl Wlk σ0 Wσ0) as (Ws & Wn & Wv & Wvs).
    destruct (wf_link_tr cl lk Wcl Wlk σ0 Wσ0) as (Wt & Wb).
    destruct nf_link as (Ns & Nn & Nv & Nvs).
    apply tr_mutind; simpl.
    - auto.
    - auto.
    - intros u t IH [W1 W2] [N1 N2]. apply nft_bind; auto.
      intros u' Wu' Nu'. simpl. auto.
    - intros s bs IH [W1 W2] [N1 N2]. destruct (IH W2 N2) as [IH1 IH2].
      apply nft_bind; auto.
      intros m Wm Nm. destruct m; simpl in *; auto.
    - auto.
    - intros c n t bs IHt IHb [W1 W2] [N1 N2]. destruct (IHb W2 N2) as [IH1 IH2].
      repeat split; auto. intros c' n'. destruct (_ && _); auto.
  Qed.

  (** The anchor [x] is fresh for the linking into a trace, when it is fresh
      for the environment and for the trace. *)
  Lemma nf_link_trace t (W : wf_tr t) (N : nft x t) : nft x (link_trace cl lk σ0 t).
  Proof.
    unfold link_trace. apply nft_bind.
    - apply wf_link_tr; auto.
    - apply nf_link_tr; auto.
    - intros. apply nf_link; auto.
  Qed.
End nf_link.

(** ** The trace of a term *)

(** Each anchor but the dead anchor is fresh for the trace of a term at the
    fuel [n], when [call n] satisfies the bound. *)
Lemma nf_denote n x (NZ : x ≠ 0)
  (Ncl : ∀ σ b, wf_nv σ → wfb b → nf_nv x σ → nft x (call n σ b)) :
  (∀ e, nft x (denote n e)) ∧
  (∀ es c, nft x (denote_list n c es)) ∧
  (∀ bs, (∀ c vs, wf_vls vs → nf_vls x vs → nft x (denote_sel n c vs bs)) ∧
         (∀ s, wf_shdw s → nf_shdw x s →
            tall_brs (aan_vl (fun a => a ≠ F x)) (aan_shdw (fun a => a ≠ F x))
              (aan_vl (fun a => a ≠ F x)) (denote_brs n s bs))).
Proof.
  assert (∀ e, wfb (fun m => denote m e)) as Hb by (intros e; exists e; reflexivity).
  assert (∀ σ b, wf_nv σ → wfb b → wf_tr (call n σ b)) as Wcl
      by (intros; apply wf_call; auto).
  assert (∀ e, wf_tr (denote n e)) as Wd by (intros; apply wf_den).
  apply tm_mutind; simpl.
  - auto.
  - auto.
  - intros e1 IH1 e2 IH2. apply nft_bind; auto.
    intros f Wf Nf. apply nft_bind; auto.
    intros a Wa Na. destruct f; simpl in *; auto.
    destruct Wf. apply Ncl; simpl; auto.
  - intros e1 IH1 e2 IH2. apply nft_bind; auto.
    intros m Wm Nm. destruct m; simpl in *; auto.
  - auto.
  - (* The case of a binding. *)
    intros y e1 IH1 e2 IH2.
    assert (wf_nv (nv_bd y (wvl_an (F 1)) (nv_sh Init))) as W1 by (simpl; auto).
    eapply tall_bind with (Q := fun v => wf_vl v ∧ nf_vl x (close_vl 0 1 v)).
    + intros v [Wv Nv].
      assert (wf_nv (nv_bd y (wvl_mu (close_vl 0 1 v)) (nv_sh Init))) as W2.
      { simpl. split; auto. apply wf_close; auto. }
      apply nft_bind; auto.
      * apply Ncl; simpl; auto.
      * intros m Wm Nm. destruct m; simpl in *; auto.
    + unfold killg. apply tall_tmap.
      destruct (Nat.eq_dec x 1) as [E|NE].
      * subst x. eapply tall_impl; [| | |apply wf_tall; apply Wcl; auto]; simpl.
        -- intros u _. apply nf_kap; auto.
        -- intros s _. apply (nf_kap 1 (vl_sh s) 0 NZ).
        -- intros v Wv'. split; auto. apply nf_close_self.
      * assert (nft x (call n (nv_bd y (wvl_an (F 1)) (nv_sh Init))
                         (fun m => denote m e1))) as N.
        { apply Ncl; simpl; auto. split; auto. congruence. }
        eapply tall_impl; [| | |apply tall_wf; [apply Wcl; auto|exact N]]; simpl.
        -- intros u [_ Hu]. apply nf_kap_other; auto.
        -- intros s [_ Hs]. apply (nf_kap_other 1 x (vl_sh s) 0 NZ Hs).
        -- intros v [Wv' Nv']. split; auto. apply nf_close; auto.
  - auto.
  - intros e IH bs [IHs IHb]. apply nft_bind; auto.
    intros m Wm Nm. destruct m; simpl in *; auto.
  - auto.
  - intros e IH es IHes c. apply nft_bind; auto.
    intros v Wv Nv. apply nft_bind; auto.
    + apply wf_denote; auto.
    + intros m Wm Nm. destruct m; simpl in *; auto.
  - auto.
  - intros c xs e IH bs [IHs IHb]. split.
    + intros c0 vs Wvs Nvs. destruct (_ && _); auto.
      apply Ncl; auto.
      * apply wf_bindV; simpl; auto.
      * apply nf_bindV; simpl; auto.
    + intros s Ws Ns. split; auto.
      apply Ncl; auto.
      * apply wf_bindD; simpl; auto.
      * apply nf_bindD; simpl; auto.
Qed.

(** The bound for [linkb n] and [linkv n], by induction on the fuel. *)
Lemma nf_linkbv n x (NZ : x ≠ 0) :
  (∀ σ b, wf_nv σ → wfb b → nf_nv x σ → nft x (linkb n σ b)) ∧
  (∀ σ v, wf_nv σ → wf_vl v → nf_nv x σ → nf_vl x v → nft x (linkv n σ v)).
Proof.
  induction n as [|n [IHb IHv]].
  - split; intros; [rewrite linkb_0|rewrite linkv_0]; simpl; auto.
  - assert (∀ σ b, wf_nv σ → wfb b → nf_nv x σ → nft x (call n σ b)) as Ncl.
    { intros. rewrite call_eq. simpl. auto. }
    assert (∀ σ b, wf_nv σ → wfb b → wf_tr (call n σ b)) as Wcl
        by (intros; apply wf_call; auto).
    assert (∀ σ v, wf_nv σ → wf_vl v → wf_tr (linkv n σ v)) as Wlk
        by (intros; apply wf_linkv; auto).
    split.
    + intros σ b Wσ [e ->] Nσ. rewrite linkb_S. apply nf_link_trace; auto.
      * apply wf_den.
      * apply nf_denote; auto.
    + intros σ v Wσ Wv Nσ Nv. rewrite linkv_S. apply nf_link; auto.
Qed.

(** An anchor that is fresh for the environment is fresh for [linkb]. *)
Lemma nf_linkb n x σ b (NZ : x ≠ 0) :
  wf_nv σ → wfb b → nf_nv x σ → nft x (linkb n σ b).
Proof. apply nf_linkbv; auto. Qed.

(** An anchor that is fresh for the environment and for the value is fresh
    for [linkv]. *)
Lemma nf_linkv n x σ v (NZ : x ≠ 0) :
  wf_nv σ → wf_vl v → nf_nv x σ → nf_vl x v → nft x (linkv n σ v).
Proof. apply nf_linkbv; auto. Qed.

(** An anchor that is fresh for the environment is fresh for [call]. *)
Lemma nf_call n x σ b (NZ : x ≠ 0) :
  wf_nv σ → wfb b → nf_nv x σ → nft x (call n σ b).
Proof. intros. rewrite call_eq. simpl. split; auto. apply nf_linkb; auto. Qed.

(** Each anchor but the dead anchor is fresh for the trace of a term. *)
Lemma nf_den n e x (NZ : x ≠ 0) : nft x (denote n e).
Proof. apply nf_denote; auto. intros. apply nf_call; auto. Qed.
