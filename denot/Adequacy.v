(** * Adequacy

    This file proves that the denotation and the reference interpreter agree.
    Link an environment into the denotation of a term. The result is the
    lifted value that the interpreter gives, and one exists exactly when the
    other exists.

    ** Main definitions

    - [closed_env ρ]: the environment [ρ] is locally closed.

    ** Main results

    - [adequacy_fwd]: when the interpreter gives a value, the denotation
      gives the lifted value at some fuel.
    - [adequacy_bwd]: when the denotation gives a value, the interpreter
      gives a value at some fuel, and the first is the lift of the second.
    - [termination]: a closed term has a value in the interpreter exactly
      when its denotation has a result.

    ** Notes

    - The forward direction is an induction on the fuel of the interpreter.
      It uses direction (b) of [LinkLink.v].
    - The backward direction is an induction on the cost of the finished
      trace. Each entry into a body is behind a guard, so the trace of the
      body has a smaller cost. It uses direction (a) of [LinkLink.v]. *)
From Stdlib Require Import Utf8 String Bool Arith Lia List Wf_nat.
From Denot Require Import Syntax Anchor Domain Nominal Semantics Laws Wf Order
  Conv Fresh Equiv Subst Reference LinkLink Lift.
Set Warnings "-notation-for-abbreviation".

(** From some fuel, the trace [F m] is finished with the result [r]. *)
Definition evd (F : nat → trace) (r : vl) : Prop :=
  ∃ m0, ∀ m, m0 ≤ m → dest (F m) = Some r.

Section closed.
  Context (ρ : renv) (HΣ : wf_nv (lift_env ρ)).
  Local Notation Σ := (lift_env ρ) (only parsing).
  Local Notation O m := (link_trace (call m) (linkv m) (lift_env ρ)) (only parsing).

  (** ** Linking a lifted environment *)

  (** More fuel keeps the result of a finished linking into the spine of a
      call. *)
  Lemma sel_call_up m1 m σ b w (LE : m1 ≤ m) (Wσ : wf_nv σ) (Wb : wfb b)
    (D : dest (link_tr (call m1) (linkv m1) Σ (call m1 σ b)) = Some w) :
    dest (link_tr (call m) (linkv m) Σ (call m σ b)) = Some w.
  Proof.
    eapply Ltr_up; eauto. - apply wf_call; auto. - apply le_call; auto.
  Qed.

  (** More fuel keeps the result of a finished [linkv]. *)
  Lemma linkv_up m1 m v r (LE : m1 ≤ m) (W : wf_vl v)
    (D : dest (linkv m1 Σ v) = Some r) : dest (linkv m Σ v) = Some r.
  Proof. rewrite (up_linkv m1 m LE Σ v r HΣ W D). exact D. Qed.

  (** A finished linking into the spine of a call resolves the environment of
      the call, at less cost. *)
  Lemma tr_call_inv m n σ b w
    (D : dest (link_tr (call m) (linkv m) Σ (call n σ b)) = Some w) :
    ∃ u, dest (link_nv (call m) (linkv m) Σ σ) = Some u ∧
         cost (link_nv (call m) (linkv m) Σ σ)
           < cost (link_tr (call m) (linkv m) Σ (call n σ b)).
  Proof.
    rewrite call_eq in *. simpl in *.
    apply inv_bind in D as (u & D1 & D2 & C). exists u. split; auto.
    rewrite C. simpl. lia.
  Qed.

  (** A lifted environment that a well-formed environment resolves to is well
      formed. *)
  Lemma res_wf m1 σ ρ' (Wσ : wf_nv σ)
    (R : dest (link_nv (call m1) (linkv m1) Σ σ) = Some (vl_exp (lift_env ρ'))) :
    wf_nv (lift_env ρ').
  Proof.
    exact (wf_Lvl _ HΣ m1 (vl_exp σ) (vl_exp (lift_env ρ')) Wσ R).
  Qed.

  (** More fuel keeps the result of a finished linking into the spine of the
      trace of a term. *)
  Lemma sel_den_up m1 m e w (LE : m1 ≤ m)
    (D : dest (link_tr (call m1) (linkv m1) Σ (denote m1 e)) = Some w) :
    dest (link_tr (call m) (linkv m) Σ (denote m e)) = Some w.
  Proof.
    eapply Ltr_up; eauto. - apply wf_den. - apply le_den; auto.
  Qed.

  (** More fuel keeps the result of a finished linking into a value. *)
  Lemma vl_up m1 m v r (LE : m1 ≤ m) (W : wf_vl v)
    (D : dest (link_vl (call m1) (linkv m1) Σ v) = Some r) :
    dest (link_vl (call m) (linkv m) Σ v) = Some r.
  Proof. rewrite (up_vl m1 m LE Σ HΣ v r W D). exact D. Qed.

  (** A result from some fuel gives one fuel, the leaf of the spine at that
      fuel, and the result of linking into the leaf. *)
  Lemma evd_split e r (E : evd (fun m => O m (denote m e)) r) :
    ∃ m1 w, wf_vl w ∧ dest (link_tr (call m1) (linkv m1) Σ (denote m1 e)) = Some w ∧
            dest (link_vl (call m1) (linkv m1) Σ w) = Some r.
  Proof.
    destruct E as (m1 & E). specialize (E m1 (Nat.le_refl _)).
    apply L_split in E as (w & D1 & D2 & _). exists m1, w. repeat split; auto.
    eapply wf_Ltr; [| |exact D1]; auto. apply wf_den.
  Qed.

  (** A value that resolves to a module is a module or a shadow. [on_mod]
      gives its environment, and that environment resolves to the environment
      of the module. *)
  Lemma mod_res cl lk w σ' (W : wf_vl w)
    (D : dest (link_vl cl lk Σ w) = Some (vl_exp σ')) :
    ∃ σ, wf_nv σ ∧ (∀ K, on_mod K w = K σ) ∧
         dest (link_nv cl lk Σ σ) = Some (vl_exp σ').
  Proof.
    destruct w as [σ1|s|?|?]; simpl in D.
    - exists σ1. auto.
    - exists (nv_sh s). repeat split; auto. simpl. eapply dest_bind_intro; eauto.
    - apply dest_bind_inv in D as (m & _ & D). destruct m; simpl in D; discriminate.
    - destruct (link_vls_leaf _ _ _ _ _ _ D) as (? & E & _). discriminate.
  Qed.

  (** Linking into the unknown environment gives the linked environment. *)
  Lemma link_Init cl lk : link_nv cl lk Σ (nv_sh Init) = Ret (vl_exp Σ).
  Proof. reflexivity. Qed.

  (** When the fields of a constructor value resolve to lifted values, the
      environment of [bindV] resolves to the lift of [rbind]. *)
  Lemma bindV_res cl lk c xs : ∀ ws vs,
    dest (link_vls cl lk Σ c ws) = Some (vl_cstr c (lift_list vs)) →
    vlen ws = length xs →
    dest (link_nv cl lk Σ (bindV xs ws (nv_sh Init))) =
    Some (vl_exp (lift_env (rbind xs vs ρ))).
  Proof.
    induction xs as [|x xs IH]; intros ws vs D Hlen.
    - destruct ws; simpl in *; auto.
    - destruct ws as [|w ws]; simpl in Hlen; try discriminate.
      simpl in D. apply dest_bind_inv in D as (v' & D1 & D).
      apply dest_bind_inv in D as (m & D2 & D).
      destruct (link_vls_leaf _ _ _ _ _ _ D2) as (vs1 & -> & _). simpl in D.
      destruct vs as [|v0 vs0]; simpl in D; inversion D; subst; clear D.
      simpl. eapply dest_bind_intro; [exact D1|].
      eapply dest_bind_intro; [apply IH; eauto|]. reflexivity.
  Qed.

  (** When a shadow resolves to a constructor value with lifted fields, the
      environment of [bindD] resolves to the lift of [rbind]. *)
  Lemma bindD_res cl lk s c vs
    (D : dest (link_shdw cl lk Σ s) = Some (vl_cstr c (lift_list vs))) :
    ∀ xs i vs', length xs = rlen vs' →
      (∀ j, vnth (i + j) (lift_list vs) = vnth j (lift_list vs')) →
      dest (link_nv cl lk Σ (bindD xs s c i (nv_sh Init))) =
      Some (vl_exp (lift_env (rbind xs vs' ρ))).
  Proof.
    induction xs as [|x xs IH]; intros i vs' Hlen Hn.
    - destruct vs'; simpl in *; auto.
    - destruct vs' as [|v0 vs0]; simpl in Hlen; try discriminate.
      simpl. eapply dest_bind_intro.
      + eapply dest_bind_intro; [exact D|]. unfold ds.
        rewrite String.eqb_refl. specialize (Hn 0).
        rewrite Nat.add_0_r in Hn. rewrite Hn. reflexivity.
      + eapply dest_bind_intro.
        * apply IH with (vs' := vs0); [lia|]. intros j.
          specialize (Hn (S j)). simpl in Hn. rewrite <- Hn. f_equal. lia.
        * reflexivity.
  Qed.

  (** When the environment of [bindV] resolves, the fields resolve, at no
      more cost. *)
  Lemma bindV_inv cl lk c xs : ∀ ws σ',
    dest (link_nv cl lk Σ (bindV xs ws (nv_sh Init))) = Some (vl_exp σ') →
    vlen ws = length xs →
    ∃ ws', dest (link_vls cl lk Σ c ws) = Some (vl_cstr c ws') ∧
           cost (link_vls cl lk Σ c ws) ≤ cost (link_nv cl lk Σ (bindV xs ws (nv_sh Init))).
  Proof.
    induction xs as [|x xs IH]; intros ws σ' D Hlen.
    - destruct ws; simpl in Hlen; try discriminate. simpl. eexists; split; eauto.
    - destruct ws as [|w ws]; simpl in Hlen; try discriminate. simpl in D |- *.
      apply inv_bind in D as (v' & D1 & D2 & C1).
      apply inv_bind in D2 as (mσ & D3 & D4 & C2).
      destruct (link_nv_leaf _ _ _ _ _ D3) as (σ'' & ->).
      destruct (IH ws σ'' D3 ltac:(lia)) as (ws' & D5 & C5).
      exists (vcons v' ws'). split.
      + eapply dest_bind_intro; [exact D1|].
        eapply dest_bind_intro; [exact D5|]. reflexivity.
      + rewrite C1, C2. erewrite cost_bind by exact D1.
        erewrite cost_bind by exact D5. simpl. lia.
  Qed.

  (** A finished linking into an environment that starts with a closed
      recursive value resolves the value before the close, then the rest. The
      costs add. *)
  Lemma mu_env_inv m x v σr u ℓ (Wv : wf_vl v) (Z : ℓ ≠ 0) (N : nf_nv ℓ Σ)
    (D : dest (link_nv (call m) (linkv m) Σ (nv_bd x (wvl_mu (close_vl 0 ℓ v)) σr)) =
         Some u) :
    ∃ v' σr', dest (linkv m Σ v) = Some v' ∧
      dest (link_nv (call m) (linkv m) Σ σr) = Some (vl_exp σr') ∧
      u = vl_exp (nv_bd x (wvl_mu (close_vl 0 ℓ v')) σr') ∧
      cost (link_nv (call m) (linkv m) Σ (nv_bd x (wvl_mu (close_vl 0 ℓ v)) σr)) =
      cost (linkv m Σ v) + cost (link_nv (call m) (linkv m) Σ σr).
  Proof.
    assert (wfk_vl 1 (close_vl 0 ℓ v)) as Wc by (apply wf_close; auto).
    rewrite (linkn_mu m Σ x _ σr ℓ HΣ Wc Z N (nf_close_self ℓ v 0)) in D |- *.
    rewrite (open_close ℓ v 0 Wv) in D |- *.
    apply inv_bind in D as (v' & D1 & D2 & C1).
    rewrite dest_killg in D1. rewrite cost_killg in C1.
    apply inv_bind in D2 as (mσ & D3 & D4 & C2).
    destruct (link_nv_leaf _ _ _ _ _ D3) as (σr' & ->). simpl in D4, C2.
    inversion D4; subst u. exists v', σr'. repeat split; auto.
    rewrite C1, C2. lia.
  Qed.

  (** The inverse of [mu_env_inv], without the costs. *)
  Lemma mu_env_intro m x v σr v' σr' ℓ (Wv : wf_vl v) (Z : ℓ ≠ 0) (N : nf_nv ℓ Σ)
    (D1 : dest (linkv m Σ v) = Some v')
    (D2 : dest (link_nv (call m) (linkv m) Σ σr) = Some (vl_exp σr')) :
    dest (link_nv (call m) (linkv m) Σ (nv_bd x (wvl_mu (close_vl 0 ℓ v)) σr)) =
    Some (vl_exp (nv_bd x (wvl_mu (close_vl 0 ℓ v')) σr')).
  Proof.
    assert (wfk_vl 1 (close_vl 0 ℓ v)) as Wc by (apply wf_close; auto).
    rewrite (linkn_mu m Σ x _ σr ℓ HΣ Wc Z N (nf_close_self ℓ v 0)).
    rewrite (open_close ℓ v 0 Wv).
    eapply dest_bind_intro; [rewrite dest_killg; exact D1|].
    eapply dest_bind_intro; [exact D2|]. reflexivity.
  Qed.

  (** The last step of a binding. A finished linking into the module that the
      binding gives resolves the value of [e1] and the module of [e2]. *)
  Lemma bind_mu_inv m x v1r w2 w ℓ (Wv : wf_vl v1r) (Z : ℓ ≠ 0) (N : nf_nv ℓ Σ)
    (D : dest (O m (on_mod (fun σ2 =>
                              Ret (vl_exp (nv_bd x (wvl_mu (close_vl 0 ℓ v1r)) σ2)))
                      w2)) = Some w) :
    ∃ v1' r2,
      dest (linkv m Σ v1r) = Some v1' ∧
      dest (link_vl (call m) (linkv m) Σ w2) = Some r2 ∧
      cost (link_vl (call m) (linkv m) Σ w2)
        ≤ cost (O m (on_mod (fun σ2 =>
                               Ret (vl_exp (nv_bd x (wvl_mu (close_vl 0 ℓ v1r)) σ2)))
                       w2)) ∧
      (∀ v2, r2 = lift v2 →
         ∃ ρ2, v2 = r_exp ρ2 ∧
               w = vl_exp (nv_bd x (wvl_mu (close_vl 0 ℓ v1')) (lift_env ρ2))).
  Proof.
    destruct w2 as [σ2|s2|?|?]; try (simpl in D; discriminate).
    - cbn [on_mod] in D |- *. rewrite L_Ret in D |- *.
      change (link_vl (call m) (linkv m) Σ (vl_exp ?s))
        with (link_nv (call m) (linkv m) Σ s) in D |- *.
      destruct (mu_env_inv m x v1r σ2 w ℓ Wv Z N D) as (v1' & σ2' & D1 & D2 & -> & C).
      exists v1', (vl_exp σ2'). repeat split; auto.
      + rewrite C. lia.
      + intros v2 Hv2. destruct v2; simpl in Hv2; inversion Hv2; subst. eauto.
    - cbn [on_mod] in D |- *. rewrite L_Ret in D |- *.
      change (link_vl (call m) (linkv m) Σ (vl_exp ?s))
        with (link_nv (call m) (linkv m) Σ s) in D |- *.
      destruct (mu_env_inv m x v1r (nv_sh s2) w ℓ Wv Z N D)
        as (v1' & σ2' & D1 & D2 & -> & C).
      change (link_nv (call m) (linkv m) Σ (nv_sh s2))
        with (bind (on_mod (fun σ' => Ret (vl_exp σ')))
                (link_shdw (call m) (linkv m) Σ s2)) in D2, C.
      apply inv_bind in D2 as (m2 & D5 & D6 & C3).
      exists v1', m2. repeat split; auto.
      + change (link_vl (call m) (linkv m) Σ (vl_sh s2))
          with (link_shdw (call m) (linkv m) Σ s2).
        rewrite C, C3. lia.
      + intros v2 ->. destruct v2; simpl in D6; try discriminate.
        inversion D6; subst σ2'. eauto.
  Qed.

  (** Assume that [σ] resolves to the lift of [ρ']. Assume also that the
      trace of [e'] in the lift of [ρ'] has the result [r] from some fuel.
      Then linking into the call of [e'] with [σ] has the result [r] from
      some fuel. *)
  Lemma call_fwd σ ρ' e' r m1 (Wσ : wf_nv σ)
    (R : dest (link_nv (call m1) (linkv m1) Σ σ) = Some (vl_exp (lift_env ρ')))
    (E : evd (fun m => link_trace (call m) (linkv m) (lift_env ρ') (denote m e')) r) :
    evd (fun m => O m (call m σ (den e'))) r.
  Proof.
    destruct E as (m0 & E). specialize (E m0 (Nat.le_refl _)).
    assert (dest (linkb (S m0) (lift_env ρ') (den e')) = Some r) as D
        by (rewrite linkb_S; exact E).
    destruct (call_b Σ HΣ (S m0) σ (lift_env ρ') (den e') r Wσ (wfb_den e')
                (ex_intro _ m1 R) D) as (n1 & m2 & H).
    exists (Nat.max n1 m2). intros m Hm. apply H; lia.
  Qed.
End closed.

(** ** Forward, from the interpreter to the denotation *)

(** Each leaf of [denote_list n c es] is a constructor value of the name [c]. *)
Lemma denote_list_leaves n es : ∀ c, leaves (is_cstr c) (denote_list n c es).
Proof.
  induction es as [|e es IH]; simpl; intros c; auto.
  eapply leaves_bind; [|apply leaves_True]. intros v _.
  eapply leaves_bind; [|apply IH]. intros [] Hc; simpl in *; auto; tauto.
Qed.

Section fwd.
  Context (N : nat).
  Context (IHN : ∀ e ρ v, wf_nv (lift_env ρ) → ev N e ρ = Some v →
    evd (fun m => link_trace (call m) (linkv m) (lift_env ρ) (denote m e)) (lift v)).

  (** The forward direction for the arguments of a constructor. *)
  Lemma fwd_list : ∀ es c ρ vs, wf_nv (lift_env ρ) →
    ev_list (ev N) es ρ = Some vs →
    evd (fun m => link_trace (call m) (linkv m) (lift_env ρ) (denote_list m c es))
        (vl_cstr c (lift_list vs)).
  Proof.
    induction es as [|e es IH]; intros c ρ vs Wρ E; simpl in E.
    - inversion E; subst. exists 0. intros. reflexivity.
    - destruct (ev N e ρ) as [v|] eqn:E1; try discriminate.
      destruct (ev_list (ev N) es ρ) as [vs'|] eqn:E2; try discriminate.
      inversion E; subst; clear E.
      destruct (IHN _ _ _ Wρ E1) as (m1 & H1).
      destruct (IH c _ _ Wρ E2) as (m2 & H2).
      exists (Nat.max m1 m2). intros m Hm. simpl.
      pose proof (H1 m ltac:(lia)) as D1. pose proof (H2 m ltac:(lia)) as D2.
      apply L_split in D1 as (vr & F1 & F2 & _).
      apply L_split in D2 as (w & G1 & G2 & _).
      assert (is_cstr c w) as Hw
          by (eapply sel_leaf; [apply denote_list_leaves|exact G1]).
      destruct w as [?|?|?|c1 ws]; simpl in Hw; try tauto. subst c1.
      eapply L_bind_intro; [exact F1|]. eapply L_bind_intro; [exact G1|].
      simpl. rewrite ?L_Ret. simpl.
      eapply dest_bind_intro; [exact F2|].
      eapply dest_bind_intro; [exact G2|]. reflexivity.
  Qed.

  (** The forward direction for a match whose scrutinee is a constructor
      value before linking. *)
  Lemma fwd_sel : ∀ bs c ws vs ρ v m1, wf_nv (lift_env ρ) → wf_vls ws →
    dest (link_vls (call m1) (linkv m1) (lift_env ρ) c ws) =
      Some (vl_cstr c (lift_list vs)) →
    ev_sel (ev N) c vs bs ρ = Some v →
    evd (fun m => link_trace (call m) (linkv m) (lift_env ρ) (denote_sel m c ws bs))
        (lift v).
  Proof.
    induction bs as [|c' xs e bs IH]; intros c ws vs ρ v m1 Wρ Wws D E; simpl in E;
      try discriminate.
    assert (vlen ws = rlen vs) as Hlen.
    { destruct (link_vls_leaf _ _ _ _ _ _ D) as (vs1 & E1 & Hl).
      inversion E1; subst. rewrite <- Hl. apply vlen_lift. }
    rewrite <- Hlen in E.
    destruct (String.eqb c c' && Nat.eqb (vlen ws) (length xs)) eqn:B.
    - apply andb_true_iff in B as B'. destruct B' as [_ B2].
      apply Nat.eqb_eq in B2.
      assert (wf_nv (bindV xs ws (nv_sh Init))) as Wσ
          by (apply wf_bindV; simpl; auto).
      pose proof (bindV_res ρ _ _ c xs ws vs D B2) as R.
      pose proof (res_wf ρ Wρ _ _ _ Wσ R) as Wρ'.
      destruct (call_fwd ρ Wρ _ (rbind xs vs ρ) e (lift v) m1 Wσ R
                  (IHN _ _ _ Wρ' E)) as (m0 & H).
      exists m0. intros m Hm. simpl. rewrite B. apply H; auto.
    - destruct (IH c ws vs ρ v m1 Wρ Wws D E) as (m0 & H).
      exists m0. intros m Hm. simpl. rewrite B. apply H; auto.
  Qed.

  (** The forward direction for a match whose scrutinee is a shadow before
      linking. *)
  Lemma fwd_brs : ∀ bs s c vs ρ v m1, wf_nv (lift_env ρ) → wf_shdw s →
    dest (link_shdw (call m1) (linkv m1) (lift_env ρ) s) =
      Some (vl_cstr c (lift_list vs)) →
    ev_sel (ev N) c vs bs ρ = Some v →
    evd (fun m => bind (link_vl (call m) (linkv m) (lift_env ρ))
                    (link_sel (call m) (linkv m) (lift_env ρ) c (rlen vs)
                       (denote_brs m s bs)))
        (lift v).
  Proof.
    induction bs as [|c' xs e bs IH]; intros s c vs ρ v m1 Wρ Ws D E; simpl in E;
      try discriminate.
    destruct (String.eqb c c' && Nat.eqb (rlen vs) (length xs)) eqn:B.
    - apply andb_true_iff in B as B'. destruct B' as [B1 B2].
      apply String.eqb_eq in B1. apply Nat.eqb_eq in B2. subst c'.
      assert (wf_nv (bindD xs s c 0 (nv_sh Init))) as Wσ
          by (apply wf_bindD; simpl; auto).
      pose proof (bindD_res ρ _ _ s c vs D xs 0 vs (eq_sym B2) (fun j => eq_refl))
        as R.
      pose proof (res_wf ρ Wρ _ _ _ Wσ R) as Wρ'.
      destruct (call_fwd ρ Wρ _ (rbind xs vs ρ) e (lift v) m1 Wσ R
                  (IHN _ _ _ Wρ' E)) as (m0 & H).
      exists m0. intros m Hm. simpl. rewrite B. apply H; auto.
    - destruct (IH s c vs ρ v m1 Wρ Ws D E) as (m0 & H).
      exists m0. intros m Hm. simpl. rewrite B. apply H; auto.
  Qed.

  (** The forward direction for a binding. *)
  Lemma fwd_bind x e1 e2 ρ v1 ρ2 (Wρ : wf_nv (lift_env ρ)) :
    let ℓ := S (rsup_env ρ) in
    ev N e1 (rcons x (rw_an (F ℓ)) ρ) = Some v1 →
    ev N e2 (rcons x (rw_mu (rclose 0 ℓ v1)) ρ) = Some (r_exp ρ2) →
    evd (fun m => link_trace (call m) (linkv m) (lift_env ρ) (denote m (Bind x e1 e2)))
        (lift (r_exp (rcons x (rw_mu (rclose 0 ℓ v1)) ρ2))).
  Proof.
    intros ℓ E1 E2.
    assert (ℓ ≠ 0) as Z by (unfold ℓ; lia).
    pose proof (fresh_lift ρ) as Nρ. fold ℓ in Nρ.
    (* [e1] runs with [x] bound to the anchor. *)
    set (σ1 := nv_bd x (wvl_an (F ℓ)) (nv_sh Init)).
    assert (wf_nv σ1) as Wσ1 by (simpl; auto).
    assert (wf_nv (lift_env (rcons x (rw_an (F ℓ)) ρ))) as Wρ1 by (simpl; auto).
    assert (dest (link_nv (call 0) (linkv 0) (lift_env ρ) σ1) =
            Some (vl_exp (lift_env (rcons x (rw_an (F ℓ)) ρ)))) as R1 by reflexivity.
    destruct (call_fwd ρ Wρ σ1 _ e1 _ 0 Wσ1 R1 (IHN _ _ _ Wρ1 E1)) as (m1 & H1).
    pose proof (H1 m1 (Nat.le_refl _)) as D1.
    apply L_split in D1 as (v1r & G1 & G2 & _).
    assert (wf_vl v1r) as Wv1r.
    { eapply wf_Ltr; [exact Wρ| |exact G1]. apply wf_call; auto. apply wfb_den. }
    assert (wf_vl (lift v1)) as Wv1 by (eapply wf_Lvl; [exact Wρ|exact Wv1r|exact G2]).
    rewrite <- linkv_S in G2.
    (* [e2] runs with [x] bound to the recursive value. *)
    set (σ2 := nv_bd x (wvl_mu (close_vl 0 ℓ v1r)) (nv_sh Init)).
    assert (wf_nv σ2) as Wσ2.
    { simpl. split; auto. apply wf_close; auto. }
    assert (dest (link_nv (call (S m1)) (linkv (S m1)) (lift_env ρ) σ2) =
            Some (vl_exp (lift_env (rcons x (rw_mu (rclose 0 ℓ v1)) ρ)))) as R2.
    { simpl lift_env. rewrite (proj1 lift_close).
      apply mu_env_intro; auto. }
    pose proof (res_wf ρ Wρ _ _ _ Wσ2 R2) as Wρ2.
    destruct (call_fwd ρ Wρ σ2 _ e2 _ (S m1) Wσ2 R2 (IHN _ _ _ Wρ2 E2))
      as (m2 & H2).
    exists (Nat.max (S m1) m2). intros m Hm.
    rewrite (denote_bind m x e1 e2 ℓ Z).
    eapply L_bind_intro.
    { rewrite linkn_tr_killg; auto; [|apply wf_call; auto; apply wfb_den].
      rewrite dest_killg.
      apply (sel_call_up ρ Wρ m1 m σ1 (den e1) v1r ltac:(lia) Wσ1 (wfb_den e1) G1). }
    fold σ2.
    pose proof (H2 m ltac:(lia)) as D2.
    apply L_split in D2 as (w2 & G3 & G4 & _).
    eapply L_bind_intro; [exact G3|].
    assert (wf_vl w2) as Ww2.
    { eapply wf_Ltr; [exact Wρ| |exact G3]. apply wf_call; auto. apply wfb_den. }
    simpl in G4. destruct (mod_res ρ _ _ _ _ Ww2 G4) as (σw & Wσw & Hσw & Rw).
    rewrite Hσw. rewrite L_Ret.
    change (link_vl (call m) (linkv m) (lift_env ρ) (vl_exp ?s))
      with (link_nv (call m) (linkv m) (lift_env ρ) s).
    simpl lift. rewrite (proj1 lift_close).
    apply mu_env_intro; auto.
    apply (linkv_up ρ Wρ (S m1) m v1r _ ltac:(lia) Wv1r G2).
  Qed.

  (** The forward direction for one more unit of fuel of the interpreter. *)
  Lemma fwd_step e ρ v (Wρ : wf_nv (lift_env ρ)) (E : ev_step (ev N) e ρ = Some v) :
    evd (fun m => link_trace (call m) (linkv m) (lift_env ρ) (denote m e)) (lift v).
  Proof.
    destruct e; simpl in E.
    - (* Var *)
      exists 0. intros m _. simpl. rewrite ?L_Ret. simpl. unfold rd.
      rewrite read_lift, E. reflexivity.
    - (* Fn *)
      inversion E; subst. exists 0. intros. reflexivity.
    - (* App *)
      destruct (ev N e1 ρ) as [[|x eb ρf|]|] eqn:E1; try discriminate.
      destruct (ev N e2 ρ) as [va|] eqn:E2; try discriminate.
      destruct (evd_split ρ Wρ _ _ (IHN _ _ _ Wρ E1)) as (m1 & f & Wf & F1 & F2).
      destruct (evd_split ρ Wρ _ _ (IHN _ _ _ Wρ E2)) as (m2 & a & Wa & A1 & A2).
      assert (wf_nv (lift_env (rcons x va ρf))) as Wρ'.
      { pose proof (wf_Lvl _ Wρ _ _ _ Wf F2) as W1.
        pose proof (wf_Lvl _ Wρ _ _ _ Wa A2) as W2.
        simpl in W1 |- *. tauto. }
      destruct (IHN _ _ _ Wρ' E) as (m3 & H3).
      assert (dest (ap (call (S m3)) (lift (r_clos x eb ρf)) (lift va)) =
              Some (lift v)) as D.
      { simpl. rewrite call_eq. simpl. rewrite linkb_S. apply (H3 m3). lia. }
      destruct (ap_b (lift_env ρ) Wρ (S m3) f a _ _ _
                  (Nat.max m1 m2) Wf Wa
                  (vl_up ρ Wρ m1 (Nat.max m1 m2) _ _ (Nat.le_max_l _ _) Wf F2)
                  (vl_up ρ Wρ m2 (Nat.max m1 m2) _ _ (Nat.le_max_r _ _) Wa A2) D)
        as (n4 & m4 & H4).
      exists (Nat.max (Nat.max m1 m2) (Nat.max n4 m4)). intros m Hm. simpl.
      eapply L_bind_intro; [eapply sel_den_up; [exact Wρ| |exact F1]; lia|].
      eapply L_bind_intro; [eapply sel_den_up; [exact Wρ| |exact A1]; lia|].
      apply H4; lia.
    - (* Link *)
      destruct (ev N e1 ρ) as [[ρ1| |]|] eqn:E1; try discriminate.
      destruct (evd_split ρ Wρ _ _ (IHN _ _ _ Wρ E1)) as (m1 & w & Ww & F1 & F2).
      destruct (mod_res ρ _ _ _ _ Ww F2) as (σ & Wσ & Hσ & R).
      pose proof (res_wf ρ Wρ _ _ _ Wσ R) as Wρ1.
      destruct (call_fwd ρ Wρ σ ρ1 e2 (lift v) m1 Wσ R (IHN _ _ _ Wρ1 E))
        as (m2 & H2).
      exists (Nat.max m1 m2). intros m Hm. simpl.
      eapply L_bind_intro; [eapply sel_den_up; [exact Wρ| |exact F1]; lia|].
      rewrite Hσ. apply H2; lia.
    - (* Mt *)
      inversion E; subst. exists 0. intros. reflexivity.
    - (* Bind *)
      destruct (ev N e1 (rcons x (rw_an (F (S (rsup_env ρ)))) ρ)) as [v1|] eqn:E1;
        try discriminate.
      destruct (ev N e2 (rcons x (rw_mu (rclose 0 (S (rsup_env ρ)) v1)) ρ))
        as [[ρ2| |]|] eqn:E2; try discriminate.
      inversion E; subst v; clear E.
      exact (fwd_bind x e1 e2 ρ v1 ρ2 Wρ E1 E2).
    - (* Cstr *)
      destruct (ev_list (ev N) es ρ) as [vs|] eqn:E1; try discriminate.
      inversion E; subst. exact (fwd_list es c ρ vs Wρ E1).
    - (* Case *)
      destruct (ev N e ρ) as [[| |c vs]|] eqn:E1; try discriminate.
      destruct (evd_split ρ Wρ _ _ (IHN _ _ _ Wρ E1)) as (m1 & w & Ww & F1 & F2).
      simpl in F2. destruct w as [σ1|s|?|c1 ws].
      + destruct (link_nv_leaf _ _ _ _ _ F2) as (? & E'). discriminate.
      + destruct (fwd_brs bs s c vs ρ v m1 Wρ Ww F2 E) as (m2 & H2).
        exists (Nat.max m1 m2). intros m Hm. simpl.
        eapply L_bind_intro; [eapply sel_den_up; [exact Wρ| |exact F1]; lia|].
        unfold link_trace. simpl. rewrite bind_bind.
        eapply dest_bind_intro.
        * apply (vl_up ρ Wρ m1 m (vl_sh s) _ ltac:(lia) Ww F2).
        * simpl. rewrite vlen_lift. apply H2; lia.
      + apply dest_bind_inv in F2 as (mσ & _ & F2).
        destruct mσ; simpl in F2; discriminate.
      + destruct (link_vls_leaf _ _ _ _ _ _ F2) as (vs1 & E' & _).
        inversion E'; subst c1 vs1; clear E'.
        destruct (fwd_sel bs c ws vs ρ v m1 Wρ Ww F2 E) as (m2 & H2).
        exists (Nat.max m1 m2). intros m Hm. simpl.
        eapply L_bind_intro; [eapply sel_den_up; [exact Wρ| |exact F1]; lia|].
        apply H2; lia.
  Qed.
End fwd.

(** The forward direction. A value of the interpreter is the result of the
    denotation from some fuel. *)
Lemma fwd : ∀ N e ρ v, wf_nv (lift_env ρ) → ev N e ρ = Some v →
  evd (fun m => link_trace (call m) (linkv m) (lift_env ρ) (denote m e)) (lift v).
Proof.
  induction N; intros e ρ v Wρ E; [discriminate|].
  apply (fwd_step N IHN); auto.
Qed.

(** ** Backward, from the denotation to the interpreter *)

(** Rewrite a value of the interpreter to the same value at a larger fuel. *)
Ltac rew_ev E :=
  match type of E with
  | ev ?n ?e ?ρ = Some ?v =>
    match goal with
    | |- context [ev ?m e ρ] => rewrite (ev_mono n m ltac:(lia) e ρ v E)
    end
  end.

Section bwd.
  Context (G : nat).
  Context (IHG : ∀ e ρ m w, wf_nv (lift_env ρ) →
    dest (link_trace (call m) (linkv m) (lift_env ρ) (denote m e)) = Some w →
    cost (link_trace (call m) (linkv m) (lift_env ρ) (denote m e)) < G →
    ∃ N v, ev N e ρ = Some v ∧ w = lift v).

  Local Notation O ρ m := (link_trace (call m) (linkv m) (lift_env ρ)) (only parsing).

  (** When [linkb] into the denotation of [e'] has the result [r] at a cost
      below [G], the interpreter gives a value whose lift is [r]. *)
  Lemma callee ρ' e' r c (Wρ' : wf_nv (lift_env ρ'))
    (E : evc (fun m2 => linkb m2 (lift_env ρ') (den e')) r c) (C : c < G) :
    ∃ N v, ev N e' ρ' = Some v ∧ r = lift v.
  Proof.
    destruct E as (m0 & E). destruct (E (S m0) ltac:(lia)) as [D Cc].
    rewrite linkb_S in D, Cc. unfold den in D, Cc.
    eapply IHG; eauto. lia.
  Qed.

  (** The same for a call that the trace holds. The environment of the call
      must resolve to the lift of [ρ']. *)
  Lemma enter ρ m σ ρ' e' w (Wρ : wf_nv (lift_env ρ)) (Wσ : wf_nv σ)
    (D : dest (O ρ m (call m σ (den e'))) = Some w)
    (C : cost (O ρ m (call m σ (den e'))) ≤ G)
    (R : ∀ σ', dest (link_nv (call m) (linkv m) (lift_env ρ) σ) = Some (vl_exp σ') →
               σ' = lift_env ρ') :
    ∃ N v, ev N e' ρ' = Some v ∧ w = lift v.
  Proof.
    destruct (call_a (lift_env ρ) Wρ m σ (den e') m w Wσ (wfb_den e') D)
      as (σ' & D1 & E & C1).
    pose proof (R _ D1) as Eσ. subst σ'.
    pose proof (res_wf ρ Wρ _ _ _ Wσ D1) as Wρ'.
    eapply callee; eauto. lia.
  Qed.

  (** The backward direction for a match whose scrutinee is a constructor
      value before linking. *)
  Lemma bwd_sel : ∀ bs c ws ρ m w, wf_nv (lift_env ρ) → wf_vls ws →
    dest (O ρ m (denote_sel m c ws bs)) = Some w →
    cost (O ρ m (denote_sel m c ws bs)) ≤ G →
    ∃ ws', dest (link_vls (call m) (linkv m) (lift_env ρ) c ws) = Some (vl_cstr c ws') ∧
           cost (link_vls (call m) (linkv m) (lift_env ρ) c ws)
             ≤ cost (O ρ m (denote_sel m c ws bs)) ∧
           (∀ vs, ws' = lift_list vs →
              ∃ N v, ev_sel (ev N) c vs bs ρ = Some v ∧ w = lift v).
  Proof.
    induction bs as [|c' xs e bs IH]; intros c ws ρ m w Wρ Wws D C;
      simpl in D, C |- *; try discriminate.
    change (fun m0 : nat => denote m0 e) with (den e) in *.
    destruct (String.eqb c c' && Nat.eqb (vlen ws) (length xs)) eqn:B.
    - apply andb_true_iff in B as B'. destruct B' as [_ B2].
      apply Nat.eqb_eq in B2.
      assert (wf_nv (bindV xs ws (nv_sh Init))) as Wσ
          by (apply wf_bindV; simpl; auto).
      destruct (call_a (lift_env ρ) Wρ m _ (den e) m w Wσ (wfb_den e) D)
        as (σ' & D1 & E & C1).
      destruct (bindV_inv ρ _ _ c xs ws σ' D1 B2) as (ws' & D2 & C2).
      exists ws'. repeat split; auto; [lia|].
      intros vs ->.
      pose proof (bindV_res ρ _ _ c xs ws vs D2 B2) as D3.
      pose proof (res_wf ρ Wρ _ _ _ Wσ D3) as Wρ'.
      rewrite D1 in D3. inversion D3; subst σ'; clear D3.
      destruct (callee _ _ _ _ Wρ' E ltac:(lia)) as (N & v & Ev & ->).
      exists N, v. split; auto.
      assert (vlen ws = rlen vs) as Hlen.
      { destruct (link_vls_leaf _ _ _ _ _ _ D2) as (vs1 & E1 & Hl).
        inversion E1; subst. rewrite <- Hl. apply vlen_lift. }
      rewrite <- Hlen, B. exact Ev.
    - destruct (IH c ws ρ m w Wρ Wws D C) as (ws' & D2 & C2 & H).
      exists ws'. repeat split; auto.
      intros vs ->. destruct (H vs eq_refl) as (N & v & Ev & ->).
      exists N, v. split; auto.
      assert (vlen ws = rlen vs) as Hlen.
      { destruct (link_vls_leaf _ _ _ _ _ _ D2) as (vs1 & E1 & Hl).
        inversion E1; subst. rewrite <- Hl. apply vlen_lift. }
      rewrite <- Hlen, B. exact Ev.
  Qed.

  (** The backward direction for a match whose scrutinee is a shadow before
      linking. *)
  Lemma bwd_brs : ∀ bs s c vs ρ m w, wf_nv (lift_env ρ) → wf_shdw s →
    dest (link_shdw (call m) (linkv m) (lift_env ρ) s) =
      Some (vl_cstr c (lift_list vs)) →
    dest (bind (link_vl (call m) (linkv m) (lift_env ρ))
            (link_sel (call m) (linkv m) (lift_env ρ) c (rlen vs)
               (denote_brs m s bs))) = Some w →
    cost (bind (link_vl (call m) (linkv m) (lift_env ρ))
            (link_sel (call m) (linkv m) (lift_env ρ) c (rlen vs)
               (denote_brs m s bs))) ≤ G →
    ∃ N v, ev_sel (ev N) c vs bs ρ = Some v ∧ w = lift v.
  Proof.
    induction bs as [|c' xs e bs IH]; intros s c vs ρ m w Wρ Ws Ds D C;
      simpl in D, C |- *; try discriminate.
    change (fun m0 : nat => denote m0 e) with (den e) in *.
    destruct (String.eqb c c' && Nat.eqb (rlen vs) (length xs)) eqn:B.
    - apply andb_true_iff in B as B'. destruct B' as [B1 B2].
      apply String.eqb_eq in B1. apply Nat.eqb_eq in B2. subst c'.
      assert (wf_nv (bindD xs s c 0 (nv_sh Init))) as Wσ
          by (apply wf_bindD; simpl; auto).
      eapply enter with (σ := bindD xs s c 0 (nv_sh Init)); eauto.
      intros σ' D1.
      pose proof (bindD_res ρ _ _ s c vs Ds xs 0 vs (eq_sym B2) (fun j => eq_refl))
        as D2.
      rewrite D1 in D2. inversion D2; auto.
    - eapply IH; eauto.
  Qed.

  (** The backward direction for a binding. *)
  Lemma bwd_bind x e1 e2 ρ m w (Wρ : wf_nv (lift_env ρ))
    (D : dest (O ρ m (denote m (Bind x e1 e2))) = Some w)
    (C : cost (O ρ m (denote m (Bind x e1 e2))) ≤ G) :
    ∃ N v, ev N (Bind x e1 e2) ρ = Some v ∧ w = lift v.
  Proof.
    set (ℓ := S (rsup_env ρ)).
    assert (ℓ ≠ 0) as Z by (unfold ℓ; lia).
    pose proof (fresh_lift ρ) as Nρ. fold ℓ in Nρ.
    set (σ1 := nv_bd x (wvl_an (F ℓ)) (nv_sh Init)).
    assert (wf_nv σ1) as Wσ1 by (simpl; auto).
    assert (wf_tr (call m σ1 (den e1))) as Wc1 by (apply wf_call; auto; apply wfb_den).
    rewrite (denote_bind m x e1 e2 ℓ Z) in D, C. fold σ1 in D, C.
    (* The spine of the trace of [e1]. *)
    apply L_bind in D as (v1r & D1 & D2 & C1).
    rewrite linkn_tr_killg in D1, C1; auto.
    rewrite dest_killg in D1. rewrite cost_killg in C1.
    assert (wf_vl v1r) as Wv1r by (eapply wf_Ltr; [exact Wρ|exact Wc1|exact D1]).
    set (σ2 := nv_bd x (wvl_mu (close_vl 0 ℓ v1r)) (nv_sh Init)) in *.
    assert (wf_nv σ2) as Wσ2.
    { simpl. split; auto. apply wf_close; auto. }
    assert (wf_tr (call m σ2 (den e2))) as Wc2 by (apply wf_call; auto; apply wfb_den).
    (* The spine of the trace of [e2] starts with its environment. Linking into it
       resolves the result of [e1]. *)
    apply L_bind in D2 as (w2 & D3 & D4 & C2).
    assert (wf_vl w2) as Ww2 by (eapply wf_Ltr; [exact Wρ|exact Wc2|exact D3]).
    destruct (tr_call_inv ρ m m σ2 (den e2) w2 D3) as (u & D5 & C4).
    destruct (mu_env_inv ρ Wρ m x v1r (nv_sh Init) u ℓ Wv1r Z Nρ D5)
      as (v1' & σi & D7 & D8 & Eu & C5).
    simpl in D8. inversion D8; subst σi; clear D8.
    (* Thus the trace of [e1] is finished, and the induction hypothesis applies. *)
    destruct m as [|mp]; [rewrite linkv_0 in D7; discriminate|].
    assert (dest (link_vl (call (S mp)) (linkv (S mp)) (lift_env ρ) v1r) = Some v1' ∧
            cost (link_vl (call (S mp)) (linkv (S mp)) (lift_env ρ) v1r) =
            cost (linkv (S mp) (lift_env ρ) v1r)) as [D9 C9].
    { rewrite linkv_S in D7 |- *.
      rewrite (up_vl mp (S mp) ltac:(lia) (lift_env ρ) Wρ v1r v1' Wv1r D7). auto. }
    destruct (L_join _ _ _ _ _ _ D1 D9) as [D10 C10].
    destruct (enter ρ (S mp) σ1 (rcons x (rw_an (F ℓ)) ρ) e1 v1' Wρ Wσ1 D10)
      as (N1 & v1 & E1 & ->).
    { rewrite C10, C9. rewrite C1, C2 in C. subst σ2. lia. }
    { intros σ' R. simpl in R. inversion R. reflexivity. }
    (* The trace of [e2]. *)
    destruct (bind_mu_inv ρ Wρ (S mp) x v1r w2 w ℓ Wv1r Z Nρ D4)
      as (v1'' & r2 & D11 & D12 & C12 & H).
    rewrite D7 in D11. inversion D11; subst v1''; clear D11.
    destruct (L_join _ _ _ _ _ _ D3 D12) as [D13 C13].
    destruct (enter ρ (S mp) σ2 (rcons x (rw_mu (rclose 0 ℓ v1)) ρ) e2 r2 Wρ Wσ2 D13)
      as (N2 & v2 & E2 & Hr2).
    { rewrite C13. rewrite C1, C2 in C. lia. }
    { intros σ' R. rewrite D5 in R. rewrite Eu in R. inversion R.
      simpl. rewrite (proj1 lift_close). reflexivity. }
    destruct (H v2 Hr2) as (ρ2 & -> & ->).
    exists (S (Nat.max N1 N2)), (r_exp (rcons x (rw_mu (rclose 0 ℓ v1)) ρ2)). split.
    - simpl. fold ℓ. rew_ev E1. rew_ev E2. reflexivity.
    - simpl. rewrite (proj1 lift_close). reflexivity.
  Qed.

  (** The statement of the backward direction for a term, at a cost of at
      most [G]. *)
  Definition Qtm (e : tm) : Prop := ∀ ρ m w, wf_nv (lift_env ρ) →
    dest (O ρ m (denote m e)) = Some w → cost (O ρ m (denote m e)) ≤ G →
    ∃ N v, ev N e ρ = Some v ∧ w = lift v.

  (** The statement of the backward direction for the arguments of a
      constructor. *)
  Definition Qtms (es : tms) : Prop := ∀ c ρ m w, wf_nv (lift_env ρ) →
    dest (O ρ m (denote_list m c es)) = Some w →
    cost (O ρ m (denote_list m c es)) ≤ G →
    ∃ N vs, ev_list (ev N) es ρ = Some vs ∧ w = vl_cstr c (lift_list vs).

  (** The backward direction at a cost of at most [G], from the statement at
      each smaller cost. *)
  Lemma bwd_tm : (∀ e, Qtm e) ∧ (∀ es, Qtms es) ∧ (∀ bs : branches, True).
  Proof.
    apply tm_mutind; unfold Qtm, Qtms; auto.
    - (* Var *)
      intros x ρ m w _ D _. simpl in D. rewrite ?L_Ret in D. simpl in D.
      unfold rd in D. rewrite read_lift in D.
      destruct (rread x ρ) as [v|] eqn:R; simpl in D; inversion D; subst.
      exists 1, v. auto.
    - (* Fn *)
      intros x e _ ρ m w _ D _. simpl in D. inversion D; subst.
      exists 1, (r_clos x e ρ). auto.
    - (* App *)
      intros e1 IH1 e2 IH2 ρ m w Wρ D C. simpl in D, C.
      apply L_bind in D as (f & D1 & D2 & C1).
      apply L_bind in D2 as (a & D3 & D4 & C2).
      assert (wf_vl f) as Wf
          by (eapply wf_Ltr; [exact Wρ|apply wf_den|exact D1]).
      assert (wf_vl a) as Wa
          by (eapply wf_Ltr; [exact Wρ|apply wf_den|exact D3]).
      destruct (ap_a (lift_env ρ) Wρ m m f a w Wf Wa D4)
        as (f' & a' & c' & D5 & D6 & E & C3).
      destruct (L_join _ _ _ _ _ _ D1 D5) as [D7 C7].
      destruct (L_join _ _ _ _ _ _ D3 D6) as [D8 C8].
      pose proof (wf_Lvl _ Wρ _ _ _ Wf D5) as Wf'.
      pose proof (wf_Lvl _ Wρ _ _ _ Wa D6) as Wa'.
      destruct (IH1 ρ m f' Wρ D7 ltac:(lia)) as (N1 & vf & E1 & ->).
      destruct (IH2 ρ m a' Wρ D8 ltac:(lia)) as (N2 & va & E2 & ->).
      destruct E as (m0 & E). destruct (E m0 (Nat.le_refl _)) as [D0 C0].
      destruct vf as [?|x eb ρf|?]; simpl in D0, C0; try discriminate.
      rewrite call_eq in D0, C0. simpl in D0, C0.
      assert (evc (fun m2 => linkb m2 (lift_env (rcons x va ρf)) (den eb)) w
                (c' - 1)) as E'.
      { exists m0. intros m2 Hm2. destruct (E m2 Hm2) as [D' C'].
        simpl in D', C'. rewrite call_eq in D', C'. simpl in D', C'.
        split; [exact D'|simpl; lia]. }
      assert (wf_nv (lift_env (rcons x va ρf))) as Wρ'.
      { simpl in Wf' |- *. tauto. }
      destruct (callee _ _ _ _ Wρ' E' ltac:(lia)) as (N3 & v & E3 & ->).
      exists (S (Nat.max N1 (Nat.max N2 N3))), v. split; auto.
      simpl. rew_ev E1.
      rew_ev E2.
      eapply ev_mono; [|exact E3]; lia.
    - (* Link *)
      intros e1 IH1 e2 _ ρ m w Wρ D C. simpl in D, C.
      change (fun m0 : nat => denote m0 e2) with (den e2) in *.
      apply L_bind in D as (mraw & D1 & D2 & C1).
      assert (wf_vl mraw) as Wm
          by (eapply wf_Ltr; [exact Wρ|apply wf_den|exact D1]).
      destruct mraw as [σ1|s|?|?]; simpl in D2, C1; try discriminate.
      + destruct (call_a (lift_env ρ) Wρ m σ1 (den e2) m w Wm (wfb_den e2) D2)
          as (σ' & R & E & C2).
        destruct (L_join _ _ _ _ _ _ D1 R) as [D3 C3]. simpl in C3.
        destruct (IH1 ρ m _ Wρ D3 ltac:(lia)) as (N1 & v1 & E1 & Hv).
        destruct v1 as [ρ1|?|?]; simpl in Hv; inversion Hv; subst σ'; clear Hv.
        pose proof (res_wf ρ Wρ _ _ _ Wm R) as Wρ1.
        destruct (callee _ _ _ _ Wρ1 E ltac:(lia)) as (N2 & v & E2 & ->).
        exists (S (Nat.max N1 N2)), v. split; auto.
        simpl. rew_ev E1.
        eapply ev_mono; [|exact E2]; lia.
      + destruct (call_a (lift_env ρ) Wρ m (nv_sh s) (den e2) m w Wm (wfb_den e2) D2)
          as (σ' & R & E & C2).
        pose proof R as R'. simpl in R', C2.
        apply inv_bind in R' as (m1 & R1 & R2 & CR).
        rewrite CR in C2.
        destruct (L_join _ _ _ _ _ _ D1 R1) as [D3 C3]. simpl in C3.
        destruct (IH1 ρ m _ Wρ D3 ltac:(lia)) as (N1 & v1 & E1 & ->).
        destruct v1 as [ρ1|?|?]; simpl in R2; inversion R2; subst σ'; clear R2.
        pose proof (res_wf ρ Wρ _ (nv_sh s) _ Wm R) as Wρ1.
        destruct (callee _ _ _ _ Wρ1 E ltac:(lia)) as (N2 & v & E2 & ->).
        exists (S (Nat.max N1 N2)), v. split; auto.
        simpl. rew_ev E1.
        eapply ev_mono; [|exact E2]; lia.
    - (* Mt *)
      intros ρ m w _ D _. simpl in D. inversion D; subst.
      exists 1, (r_exp rnil). auto.
    - (* Bind *)
      intros x e1 _ e2 _ ρ m w Wρ D C. exact (bwd_bind x e1 e2 ρ m w Wρ D C).
    - (* Cstr *)
      intros c es IH ρ m w Wρ D C. simpl in D, C.
      destruct (IH c ρ m w Wρ D C) as (N & vs & E & ->).
      exists (S N), (r_cstr c vs). split; auto. simpl. rewrite E. reflexivity.
    - (* Case *)
      intros e IH bs _ ρ m w Wρ D C. simpl in D, C.
      apply L_bind in D as (mraw & D1 & D2 & C1).
      assert (wf_vl mraw) as Wm
          by (eapply wf_Ltr; [exact Wρ|apply wf_den|exact D1]).
      destruct mraw as [?|s|?|c1 ws]; simpl in D2, C1; try discriminate.
      + (* The scrutinee is a shadow. *)
        apply L_match in D2 as (c & vs1 & D3 & D4 & C2).
        destruct (L_join _ _ _ _ _ _ D1 D3) as [D5 C5]. simpl in C5.
        destruct (IH ρ m _ Wρ D5 ltac:(lia)) as (N1 & v0 & E1 & Hv).
        destruct v0 as [?|?|c0 vs]; simpl in Hv; inversion Hv; subst c0 vs1;
          clear Hv.
        rewrite vlen_lift in D4, C2.
        destruct (bwd_brs bs s c vs ρ m w Wρ Wm D3 D4 ltac:(lia))
          as (N2 & v & E2 & ->).
        exists (S (Nat.max N1 N2)), v. split; auto.
        simpl. rew_ev E1.
        eapply ev_sel_mono; [|exact E2]. intros. eapply ev_mono; [|eassumption]. lia.
      + (* The scrutinee is a constructor value. *)
        destruct (bwd_sel bs c1 ws ρ m w Wρ Wm D2 ltac:(lia)) as (ws' & D3 & C3 & H).
        destruct (L_join _ _ _ _ _ _ D1 D3) as [D5 C5]. simpl in C5.
        destruct (IH ρ m _ Wρ D5 ltac:(lia)) as (N1 & v0 & E1 & Hv).
        destruct v0 as [?|?|c0 vs]; simpl in Hv; inversion Hv; subst c0 ws';
          clear Hv.
        destruct (H vs eq_refl) as (N2 & v & E2 & ->).
        exists (S (Nat.max N1 N2)), v. split; auto.
        simpl. rew_ev E1.
        eapply ev_sel_mono; [|exact E2]. intros. eapply ev_mono; [|eassumption]. lia.
    - (* tnil *)
      intros c ρ m w _ D _. simpl in D. inversion D; subst.
      exists 0, rvnil. auto.
    - (* tcons *)
      intros e IHe es IHes c ρ m w Wρ D C. simpl in D, C.
      apply L_bind in D as (vr & D1 & D2 & C1).
      apply L_bind in D2 as (wl & D3 & D4 & C2).
      destruct wl as [?|?|?|c1 ws]; simpl in D4, C2; try discriminate.
      rewrite ?L_Ret in D4, C2. simpl in D4, C2.
      apply inv_bind in D4 as (v' & D5 & D6 & C3).
      apply inv_bind in D6 as (ml & D7 & D8 & C4).
      destruct (link_vls_leaf _ _ _ _ _ _ D7) as (ws' & -> & _). simpl in D8, C4.
      inversion D8; subst w; clear D8.
      destruct (L_join _ _ _ _ _ _ D1 D5) as [D9 C9].
      destruct (L_join _ _ _ _ _ _ D3 D7) as [D10 C10]. simpl in C10.
      destruct (IHe ρ m v' Wρ D9 ltac:(lia)) as (N1 & v0 & E1 & ->).
      destruct (IHes c ρ m _ Wρ D10 ltac:(lia)) as (N2 & vs & E2 & Hw).
      inversion Hw; subst c1 ws'; clear Hw.
      exists (Nat.max N1 N2), (rvcons v0 vs). split; auto.
      simpl. rew_ev E1.
      erewrite ev_list_mono; [reflexivity| |exact E2].
      intros. eapply ev_mono; [|eassumption]. lia.
  Qed.
End bwd.

(** The backward direction. A result of the denotation is the lift of a value
    of the interpreter. *)
Lemma bwd : ∀ G e ρ m w, wf_nv (lift_env ρ) →
  dest (link_trace (call m) (linkv m) (lift_env ρ) (denote m e)) = Some w →
  cost (link_trace (call m) (linkv m) (lift_env ρ) (denote m e)) ≤ G →
  ∃ N v, ev N e ρ = Some v ∧ w = lift v.
Proof.
  induction G as [G IH] using lt_wf_ind. intros e ρ m w Wρ D C.
  destruct (bwd_tm G) as [H _].
  - intros e' ρ' m' w' Wρ' D' C'. eapply (IH _ C'); eauto.
  - exact (H e ρ m w Wρ D C).
Qed.

(** ** The theorems *)

(** An environment of the interpreter is locally closed. That is, a recursive
    value around each index binds the index. The empty environment is locally
    closed. *)
Definition closed_env (ρ : renv) : Prop := wf_nv (lift_env ρ).

(** When the interpreter gives the value [v], the denotation gives the lift
    of [v] at some fuel. *)
Theorem adequacy_fwd N e ρ v : closed_env ρ →
  ev N e ρ = Some v → ∃ n, run n (lift_env ρ) e = Some (lift v).
Proof.
  intros Wρ E. destruct (fwd N e ρ v Wρ E) as (m0 & H).
  exists (S m0). unfold run. rewrite linkb_S. apply H. lia.
Qed.

(** When the denotation gives the value [w], the interpreter gives a value
    [v] at some fuel, and [w] is the lift of [v]. *)
Theorem adequacy_bwd n e ρ w : closed_env ρ →
  run n (lift_env ρ) e = Some w → ∃ N v, ev N e ρ = Some v ∧ w = lift v.
Proof.
  intros Wρ. unfold run. destruct n; [rewrite linkb_0; discriminate|].
  rewrite linkb_S. intros D. eapply bwd; eauto.
Qed.

(** The 2 directions for a closed term, in the empty environment. *)
Corollary adequacy e :
  (∀ N v, ev N e rnil = Some v → ∃ n, run n nv_mt e = Some (lift v)) ∧
  (∀ n w, run n nv_mt e = Some w → ∃ N v, ev N e rnil = Some v ∧ w = lift v).
Proof.
  split.
  - intros N v E. exact (adequacy_fwd N e rnil v I E).
  - intros n w R. exact (adequacy_bwd n e rnil w I R).
Qed.

(** A closed term has a value in the interpreter exactly when its denotation
    has a result. *)
Corollary termination e :
  (∃ N v, ev N e rnil = Some v) ↔ (∃ n w, run n nv_mt e = Some w).
Proof.
  split.
  - intros (N & v & E). destruct (adequacy_fwd N e rnil v I E) as (n & R). eauto.
  - intros (n & w & R).
    destruct (adequacy_bwd n e rnil w I R) as (N & v & E & _). eauto.
Qed.
