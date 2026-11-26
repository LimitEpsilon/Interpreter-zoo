(** * Adequacy

    Linking a closed environment into the denotation of a program returns
    exactly what the reference interpreter returns:

    - [adequacy_fwd] : if [ev N e ρ = Some v] then, for some [n],
      [run n (lift_env ρ) e = Some (lift v)];
    - [adequacy_bwd] : if [run n (lift_env ρ) e = Some w] then, for some [N]
      and [v], [ev N e ρ = Some v] and [w = lift v].

    In particular the denotational semantics diverges exactly when the
    interpreter does ([termination]). *)
From Stdlib Require Import Utf8 String Bool Arith Lia List Wf_nat.
From Denot Require Import Syntax Domain Semantics Laws Wf Order Conv
  Reference LinkLink Lift.

Definition evd (F : nat → trace) (r : vl) : Prop :=
  ∃ m0, ∀ m, m0 ≤ m → dest (F m) = Some r.

(** ** Helpers about resolving against a closed environment *)

Section closed.
  Context (ρ : renv).
  Local Notation Σ := (lift_env ρ) (only parsing).
  Local Notation O m := (link_trace (call m) (lift_env ρ)) (only parsing).

  Let HΣ : wf_nv Σ := wf_lift_env ρ.

  Lemma sel_den_up m1 m e w (LE : m1 ≤ m)
    (D : dest (link_tr (call m1) Σ (denote m1 e)) = Some w) :
    dest (link_tr (call m) Σ (denote m e)) = Some w.
  Proof.
    eapply Ltr_up; eauto. - apply wf_den. - apply le_den; auto.
  Qed.

  Lemma vl_up m1 m v r (LE : m1 ≤ m) (W : wf_vl v)
    (D : dest (link_vl (call m1) Σ v) = Some r) :
    dest (link_vl (call m) Σ v) = Some r.
  Proof. rewrite (up_vl m1 m LE Σ HΣ v r W D). exact D. Qed.

  Lemma evd_split e r (E : evd (fun m => O m (denote m e)) r) :
    ∃ m1 w, wf_vl w ∧ dest (link_tr (call m1) Σ (denote m1 e)) = Some w ∧
            dest (link_vl (call m1) Σ w) = Some r.
  Proof.
    destruct E as (m1 & E). specialize (E m1 (Nat.le_refl _)).
    apply L_split in E as (w & D1 & D2 & _). exists m1, w. repeat split; auto.
    eapply wf_Ltr; [| |exact D1]; auto. apply wf_den.
  Qed.

  (** a value that resolves to a module is a module, up to representation *)
  Lemma mod_res cl w σ' (W : wf_vl w)
    (D : dest (link_vl cl Σ w) = Some (vl_exp σ')) :
    ∃ σ, wf_nv σ ∧ (∀ K, on_mod K w = K σ) ∧
         dest (link_nv cl Σ σ) = Some (vl_exp σ').
  Proof.
    destruct w as [σ1|s|?|?]; simpl in D.
    - exists σ1. auto.
    - exists (nv_sh s). repeat split; auto. simpl. eapply dest_bind_intro; eauto.
    - apply dest_bind_inv in D as (m & _ & D). destruct m; simpl in D; discriminate.
    - destruct (link_vls_leaf _ _ _ _ _ D) as (? & E & _). discriminate.
  Qed.

  Lemma link_Init cl : link_nv cl Σ (nv_sh Init) = Ret (vl_exp Σ).
  Proof. reflexivity. Qed.

  Lemma bindV_res cl c xs : ∀ ws vs,
    dest (link_vls cl Σ c ws) = Some (vl_cstr c (lift_list vs)) →
    vlen ws = length xs →
    dest (link_nv cl Σ (bindV xs ws (nv_sh Init))) =
    Some (vl_exp (lift_env (rbind xs vs ρ))).
  Proof.
    induction xs as [|x xs IH]; intros ws vs D Hlen.
    - destruct ws; simpl in *; auto.
    - destruct ws as [|w ws]; simpl in Hlen; try discriminate.
      simpl in D. apply dest_bind_inv in D as (v' & D1 & D).
      apply dest_bind_inv in D as (m & D2 & D).
      destruct (link_vls_leaf _ _ _ _ _ D2) as (vs1 & -> & _). simpl in D.
      destruct vs as [|v0 vs0]; simpl in D; inversion D; subst; clear D.
      simpl. eapply dest_bind_intro; [exact D1|].
      eapply dest_bind_intro; [apply IH; eauto|]. reflexivity.
  Qed.

  Lemma bindD_res cl s c vs
    (D : dest (link_shdw cl Σ s) = Some (vl_cstr c (lift_list vs))) :
    ∀ xs i vs', length xs = rlen vs' →
      (∀ j, vnth (i + j) (lift_list vs) = vnth j (lift_list vs')) →
      dest (link_nv cl Σ (bindD xs s c i (nv_sh Init))) =
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

  Lemma bindV_inv cl c xs : ∀ ws σ',
    dest (link_nv cl Σ (bindV xs ws (nv_sh Init))) = Some (vl_exp σ') →
    vlen ws = length xs →
    ∃ ws', dest (link_vls cl Σ c ws) = Some (vl_cstr c ws') ∧
           cost (link_vls cl Σ c ws) ≤ cost (link_nv cl Σ (bindV xs ws (nv_sh Init))).
  Proof.
    induction xs as [|x xs IH]; intros ws σ' D Hlen.
    - destruct ws; simpl in Hlen; try discriminate. simpl. eexists; split; eauto.
    - destruct ws as [|w ws]; simpl in Hlen; try discriminate. simpl in D |- *.
      apply inv_bind in D as (v' & D1 & D2 & C1).
      apply inv_bind in D2 as (mσ & D3 & D4 & C2).
      destruct (link_nv_leaf _ _ _ _ D3) as (σ'' & ->).
      destruct (IH ws σ'' D3 ltac:(lia)) as (ws' & D5 & C5).
      exists (vcons v' ws'). split.
      + eapply dest_bind_intro; [exact D1|].
        eapply dest_bind_intro; [exact D5|]. reflexivity.
      + rewrite C1, C2. erewrite cost_bind by exact D1.
        erewrite cost_bind by exact D5. simpl. lia.
  Qed.

  (** what a [Bind] exports, once its body's module is resolved *)
  Lemma bind_mod_inv cl x v1r w2 w
    (D : dest (link_trace cl Σ
           (on_mod (fun σ2 => Ret (vl_exp (nv_bd x v1r σ2))) w2)) = Some w) :
    ∃ v1' r2,
      dest (link_vl cl Σ v1r) = Some v1' ∧ dest (link_vl cl Σ w2) = Some r2 ∧
      cost (link_vl cl Σ v1r) + cost (link_vl cl Σ w2)
        ≤ cost (link_trace cl Σ
                  (on_mod (fun σ2 => Ret (vl_exp (nv_bd x v1r σ2))) w2)) ∧
      (∀ v2, r2 = lift v2 →
         ∃ ρ2, v2 = r_exp ρ2 ∧ w = vl_exp (nv_bd x v1' (lift_env ρ2))).
  Proof.
    destruct w2 as [σ2|s2|?|?]; simpl in D |- *; try discriminate.
    - rewrite ?L_Ret in *. simpl in D |- *.
      apply inv_bind in D as (v1' & D1 & D2 & C1).
      apply inv_bind in D2 as (mσ & D3 & D4 & C2).
      destruct (link_nv_leaf _ _ _ _ D3) as (σ2' & ->). simpl in D4, C2.
      inversion D4; subst w; clear D4.
      exists v1', (vl_exp σ2'). repeat split; auto.
      + rewrite C1, C2. lia.
      + intros v2 Hv2. destruct v2; simpl in Hv2; inversion Hv2; subst. eauto.
    - rewrite ?L_Ret in *. simpl in D |- *.
      apply inv_bind in D as (v1' & D1 & D2 & C1).
      apply inv_bind in D2 as (mσ & D3 & D4 & C2).
      apply inv_bind in D3 as (m2 & D5 & D6 & C3).
      exists v1', m2. repeat split; auto.
      + rewrite C1, C2, C3. lia.
      + intros v2 ->. destruct v2; simpl in D6; try discriminate.
        inversion D6; subst mσ. simpl in D4. inversion D4; subst w. eauto.
  Qed.

  (** entering a body whose environment resolves to a closed one *)
  Lemma call_fwd σ ρ' e' r m1 (Wσ : wf_nv σ)
    (R : dest (link_nv (call m1) Σ σ) = Some (vl_exp (lift_env ρ')))
    (E : evd (fun m => link_trace (call m) (lift_env ρ') (denote m e')) r) :
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

Lemma denote_list_leaves n es : ∀ c, leaves (is_cstr c) (denote_list n c es).
Proof.
  induction es as [|e es IH]; simpl; intros c; auto.
  eapply leaves_bind; [|apply leaves_True]. intros v _.
  eapply leaves_bind; [|apply IH]. intros [] Hc; simpl in *; auto; tauto.
Qed.

(** ** Forward: what the interpreter returns, the denotation returns *)

Section fwd.
  Context (N : nat).
  Context (IHN : ∀ e ρ v, ev N e ρ = Some v →
    evd (fun m => link_trace (call m) (lift_env ρ) (denote m e)) (lift v)).

  Lemma fwd_list : ∀ es c ρ vs, ev_list (ev N) es ρ = Some vs →
    evd (fun m => link_trace (call m) (lift_env ρ) (denote_list m c es))
        (vl_cstr c (lift_list vs)).
  Proof.
    induction es as [|e es IH]; intros c ρ vs E; simpl in E.
    - inversion E; subst. exists 0. intros. reflexivity.
    - destruct (ev N e ρ) as [v|] eqn:E1; try discriminate.
      destruct (ev_list (ev N) es ρ) as [vs'|] eqn:E2; try discriminate.
      inversion E; subst; clear E.
      destruct (IHN _ _ _ E1) as (m1 & H1). destruct (IH c _ _ E2) as (m2 & H2).
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

  (** matching on a constructor the symbolic run already knew *)
  Lemma fwd_sel : ∀ bs c ws vs ρ v m1, wf_vls ws →
    dest (link_vls (call m1) (lift_env ρ) c ws) = Some (vl_cstr c (lift_list vs)) →
    ev_sel (ev N) c vs bs ρ = Some v →
    evd (fun m => link_trace (call m) (lift_env ρ) (denote_sel m c ws bs)) (lift v).
  Proof.
    induction bs as [|c' xs e bs IH]; intros c ws vs ρ v m1 Wws D E; simpl in E;
      try discriminate.
    assert (vlen ws = rlen vs) as Hlen.
    { destruct (link_vls_leaf _ _ _ _ _ D) as (vs1 & E1 & Hl).
      inversion E1; subst. rewrite <- Hl. apply vlen_lift. }
    rewrite <- Hlen in E.
    destruct (String.eqb c c' && Nat.eqb (vlen ws) (length xs)) eqn:B.
    - apply andb_true_iff in B as B'. destruct B' as [_ B2].
      apply Nat.eqb_eq in B2.
      assert (wf_nv (bindV xs ws (nv_sh Init))) as Wσ
          by (apply wf_bindV; simpl; auto).
      destruct (call_fwd ρ _ (rbind xs vs ρ) e (lift v) m1 Wσ
                  (bindV_res ρ _ c xs ws vs D B2) (IHN _ _ _ E)) as (m0 & H).
      exists m0. intros m Hm. simpl. rewrite B. apply H; auto.
    - destruct (IH c ws vs ρ v m1 Wws D E) as (m0 & H).
      exists m0. intros m Hm. simpl. rewrite B. apply H; auto.
  Qed.

  (** matching on a constructor only the environment knows *)
  Lemma fwd_brs : ∀ bs s c vs ρ v m1, wf_shdw s →
    dest (link_shdw (call m1) (lift_env ρ) s) = Some (vl_cstr c (lift_list vs)) →
    ev_sel (ev N) c vs bs ρ = Some v →
    evd (fun m => bind (link_vl (call m) (lift_env ρ))
                    (link_sel (call m) (lift_env ρ) c (rlen vs) (denote_brs m s bs)))
        (lift v).
  Proof.
    induction bs as [|c' xs e bs IH]; intros s c vs ρ v m1 Ws D E; simpl in E;
      try discriminate.
    destruct (String.eqb c c' && Nat.eqb (rlen vs) (length xs)) eqn:B.
    - apply andb_true_iff in B as B'. destruct B' as [B1 B2].
      apply String.eqb_eq in B1. apply Nat.eqb_eq in B2. subst c'.
      assert (wf_nv (bindD xs s c 0 (nv_sh Init))) as Wσ
          by (apply wf_bindD; simpl; auto).
      destruct (call_fwd ρ _ (rbind xs vs ρ) e (lift v) m1 Wσ
                  (bindD_res ρ _ s c vs D xs 0 vs (eq_sym B2) (fun j => eq_refl))
                  (IHN _ _ _ E)) as (m0 & H).
      exists m0. intros m Hm. simpl. rewrite B. apply H; auto.
    - destruct (IH s c vs ρ v m1 Ws D E) as (m0 & H).
      exists m0. intros m Hm. simpl. rewrite B. apply H; auto.
  Qed.

  Lemma fwd_step e ρ v (E : ev_step (ev N) e ρ = Some v) :
    evd (fun m => link_trace (call m) (lift_env ρ) (denote m e)) (lift v).
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
      destruct (evd_split ρ _ _ (IHN _ _ _ E1)) as (m1 & f & Wf & F1 & F2).
      destruct (evd_split ρ _ _ (IHN _ _ _ E2)) as (m2 & a & Wa & A1 & A2).
      destruct (IHN _ _ _ E) as (m3 & H3).
      assert (dest (ap (call (S m3)) (lift (r_clos x eb ρf)) (lift va)) =
              Some (lift v)) as D.
      { simpl. rewrite call_eq. simpl. rewrite linkb_S. apply (H3 m3). lia. }
      destruct (ap_b (lift_env ρ) (wf_lift_env ρ) (S m3) f a _ _ _
                  (Nat.max m1 m2) Wf Wa
                  (vl_up ρ m1 (Nat.max m1 m2) _ _ (Nat.le_max_l _ _) Wf F2)
                  (vl_up ρ m2 (Nat.max m1 m2) _ _ (Nat.le_max_r _ _) Wa A2) D)
        as (n4 & m4 & H4).
      exists (Nat.max (Nat.max m1 m2) (Nat.max n4 m4)). intros m Hm. simpl.
      eapply L_bind_intro; [eapply sel_den_up; [|exact F1]; lia|].
      eapply L_bind_intro; [eapply sel_den_up; [|exact A1]; lia|].
      apply H4; lia.
    - (* Link *)
      destruct (ev N e1 ρ) as [[ρ1| |]|] eqn:E1; try discriminate.
      destruct (evd_split ρ _ _ (IHN _ _ _ E1)) as (m1 & w & Ww & F1 & F2).
      destruct (mod_res ρ _ _ _ Ww F2) as (σ & Wσ & Hσ & R).
      destruct (call_fwd ρ σ ρ1 e2 (lift v) m1 Wσ R (IHN _ _ _ E)) as (m2 & H2).
      exists (Nat.max m1 m2). intros m Hm. simpl.
      eapply L_bind_intro; [eapply sel_den_up; [|exact F1]; lia|].
      rewrite Hσ. apply H2; lia.
    - (* Mt *)
      inversion E; subst. exists 0. intros. reflexivity.
    - (* Bind *)
      destruct (ev N e1 ρ) as [v1|] eqn:E1; try discriminate.
      destruct (ev N e2 (rcons x v1 ρ)) as [[ρ2| |]|] eqn:E2; try discriminate.
      inversion E; subst v; clear E.
      destruct (evd_split ρ _ _ (IHN _ _ _ E1)) as (m1 & v1r & W1 & F1 & F2).
      assert (dest (link_nv (call m1) (lift_env ρ) (nv_bd x v1r (nv_sh Init))) =
              Some (vl_exp (lift_env (rcons x v1 ρ)))) as R.
      { simpl. eapply dest_bind_intro; [exact F2|]. reflexivity. }
      assert (wf_nv (nv_bd x v1r (nv_sh Init))) as Wσ by (simpl; auto).
      destruct (call_fwd ρ _ (rcons x v1 ρ) e2 _ m1 Wσ R (IHN _ _ _ E2))
        as (m2 & H2).
      exists (Nat.max m1 m2). intros m Hm. simpl.
      eapply L_bind_intro; [eapply sel_den_up; [|exact F1]; lia|].
      pose proof (H2 m ltac:(lia)) as D2.
      apply L_split in D2 as (w2 & G1 & G2 & _).
      eapply L_bind_intro; [exact G1|].
      assert (wf_vl w2) as W2.
      { eapply wf_Ltr; [apply wf_lift_env| |exact G1]. apply wf_call; auto.
        apply wfb_den. }
      simpl in G2. destruct (mod_res ρ _ _ _ W2 G2) as (σ2 & Wσ2 & Hσ2 & R2).
      rewrite Hσ2. rewrite ?L_Ret. simpl.
      eapply dest_bind_intro; [eapply vl_up; [|exact W1|exact F2]; lia|].
      eapply dest_bind_intro; [exact R2|]. reflexivity.
    - (* Cstr *)
      destruct (ev_list (ev N) es ρ) as [vs|] eqn:E1; try discriminate.
      inversion E; subst. exact (fwd_list es c ρ vs E1).
    - (* Case *)
      destruct (ev N e ρ) as [[| |c vs]|] eqn:E1; try discriminate.
      destruct (evd_split ρ _ _ (IHN _ _ _ E1)) as (m1 & w & Ww & F1 & F2).
      simpl in F2. destruct w as [σ1|s|?|c1 ws].
      + destruct (link_nv_leaf _ _ _ _ F2) as (? & E'). discriminate.
      + destruct (fwd_brs bs s c vs ρ v m1 Ww F2 E) as (m2 & H2).
        exists (Nat.max m1 m2). intros m Hm. simpl.
        eapply L_bind_intro; [eapply sel_den_up; [|exact F1]; lia|].
        unfold link_trace. simpl. rewrite bind_bind.
        eapply dest_bind_intro.
        * apply (vl_up ρ m1 m (vl_sh s) _ ltac:(lia) Ww F2).
        * simpl. rewrite vlen_lift. apply H2; lia.
      + apply dest_bind_inv in F2 as (mσ & _ & F2).
        destruct mσ; simpl in F2; discriminate.
      + destruct (link_vls_leaf _ _ _ _ _ F2) as (vs1 & E' & _).
        inversion E'; subst c1 vs1; clear E'.
        destruct (fwd_sel bs c ws vs ρ v m1 Ww F2 E) as (m2 & H2).
        exists (Nat.max m1 m2). intros m Hm. simpl.
        eapply L_bind_intro; [eapply sel_den_up; [|exact F1]; lia|].
        apply H2; lia.
  Qed.
End fwd.

Lemma fwd : ∀ N e ρ v, ev N e ρ = Some v →
  evd (fun m => link_trace (call m) (lift_env ρ) (denote m e)) (lift v).
Proof.
  induction N; intros e ρ v E; [discriminate|].
  apply (fwd_step N IHN). exact E.
Qed.


(** ** Backward: what the denotation returns, the interpreter returns

    By induction on the number of guards in the finished trace: every time
    the semantics enters a body it passes a guard, and the body's own run is
    strictly cheaper. *)

(** rewrite a reference run to a run with more fuel *)
Ltac rew_ev E :=
  match type of E with
  | ev ?n ?e ?ρ = Some ?v =>
    match goal with
    | |- context [ev ?m e ρ] => rewrite (ev_mono n m ltac:(lia) e ρ v E)
    end
  end.

Section bwd.
  Context (G : nat).
  Context (IHG : ∀ e ρ m w,
    dest (link_trace (call m) (lift_env ρ) (denote m e)) = Some w →
    cost (link_trace (call m) (lift_env ρ) (denote m e)) < G →
    ∃ N v, ev N e ρ = Some v ∧ w = lift v).

  Local Notation O ρ m := (link_trace (call m) (lift_env ρ)) (only parsing).

  Lemma callee ρ' e' r c
    (E : evc (fun m2 => linkb m2 (lift_env ρ') (den e')) r c) (C : c < G) :
    ∃ N v, ev N e' ρ' = Some v ∧ r = lift v.
  Proof.
    destruct E as (m0 & E). destruct (E (S m0) ltac:(lia)) as [D Cc].
    rewrite linkb_S in D, Cc. unfold den in D, Cc.
    eapply IHG; eauto. lia.
  Qed.

  (** entering a body from a call the symbolic run already made *)
  Lemma enter ρ m σ ρ' e' w (Wσ : wf_nv σ)
    (D : dest (O ρ m (call m σ (den e'))) = Some w)
    (C : cost (O ρ m (call m σ (den e'))) ≤ G)
    (R : ∀ σ', dest (link_nv (call m) (lift_env ρ) σ) = Some (vl_exp σ') →
               σ' = lift_env ρ') :
    ∃ N v, ev N e' ρ' = Some v ∧ w = lift v.
  Proof.
    destruct (call_a (lift_env ρ) (wf_lift_env ρ) m σ (den e') m w Wσ
                (wfb_den e') D) as (σ' & D1 & E & C1).
    rewrite (R _ D1) in E. eapply callee; eauto. lia.
  Qed.

  Lemma bwd_sel : ∀ bs c ws ρ m w, wf_vls ws →
    dest (O ρ m (denote_sel m c ws bs)) = Some w →
    cost (O ρ m (denote_sel m c ws bs)) ≤ G →
    ∃ ws', dest (link_vls (call m) (lift_env ρ) c ws) = Some (vl_cstr c ws') ∧
           cost (link_vls (call m) (lift_env ρ) c ws)
             ≤ cost (O ρ m (denote_sel m c ws bs)) ∧
           (∀ vs, ws' = lift_list vs →
              ∃ N v, ev_sel (ev N) c vs bs ρ = Some v ∧ w = lift v).
  Proof.
    induction bs as [|c' xs e bs IH]; intros c ws ρ m w Wws D C; simpl in D, C |- *;
      try discriminate.
    change (fun m0 : nat => denote m0 e) with (den e) in *.
    destruct (String.eqb c c' && Nat.eqb (vlen ws) (length xs)) eqn:B.
    - apply andb_true_iff in B as B'. destruct B' as [_ B2].
      apply Nat.eqb_eq in B2.
      assert (wf_nv (bindV xs ws (nv_sh Init))) as Wσ
          by (apply wf_bindV; simpl; auto).
      destruct (call_a (lift_env ρ) (wf_lift_env ρ) m _ (den e) m w Wσ
                  (wfb_den e) D) as (σ' & D1 & E & C1).
      destruct (bindV_inv ρ _ c xs ws σ' D1 B2) as (ws' & D2 & C2).
      exists ws'. repeat split; auto; [lia|].
      intros vs ->.
      pose proof (bindV_res ρ _ c xs ws vs D2 B2) as D3.
      rewrite D1 in D3. inversion D3; subst σ'; clear D3.
      destruct (callee _ _ _ _ E ltac:(lia)) as (N & v & Ev & ->).
      exists N, v. split; auto.
      assert (vlen ws = rlen vs) as Hlen.
      { destruct (link_vls_leaf _ _ _ _ _ D2) as (vs1 & E1 & Hl).
        inversion E1; subst. rewrite <- Hl. apply vlen_lift. }
      rewrite <- Hlen, B. exact Ev.
    - destruct (IH c ws ρ m w Wws D C) as (ws' & D2 & C2 & H).
      exists ws'. repeat split; auto.
      intros vs ->. destruct (H vs eq_refl) as (N & v & Ev & ->).
      exists N, v. split; auto.
      assert (vlen ws = rlen vs) as Hlen.
      { destruct (link_vls_leaf _ _ _ _ _ D2) as (vs1 & E1 & Hl).
        inversion E1; subst. rewrite <- Hl. apply vlen_lift. }
      rewrite <- Hlen, B. exact Ev.
  Qed.

  Lemma bwd_brs : ∀ bs s c vs ρ m w, wf_shdw s →
    dest (link_shdw (call m) (lift_env ρ) s) = Some (vl_cstr c (lift_list vs)) →
    dest (bind (link_vl (call m) (lift_env ρ))
            (link_sel (call m) (lift_env ρ) c (rlen vs) (denote_brs m s bs))) = Some w →
    cost (bind (link_vl (call m) (lift_env ρ))
            (link_sel (call m) (lift_env ρ) c (rlen vs) (denote_brs m s bs))) ≤ G →
    ∃ N v, ev_sel (ev N) c vs bs ρ = Some v ∧ w = lift v.
  Proof.
    induction bs as [|c' xs e bs IH]; intros s c vs ρ m w Ws Ds D C; simpl in D, C |- *;
      try discriminate.
    change (fun m0 : nat => denote m0 e) with (den e) in *.
    destruct (String.eqb c c' && Nat.eqb (rlen vs) (length xs)) eqn:B.
    - apply andb_true_iff in B as B'. destruct B' as [B1 B2].
      apply String.eqb_eq in B1. apply Nat.eqb_eq in B2. subst c'.
      assert (wf_nv (bindD xs s c 0 (nv_sh Init))) as Wσ
          by (apply wf_bindD; simpl; auto).
      eapply enter with (σ := bindD xs s c 0 (nv_sh Init)); eauto.
      intros σ' D1.
      pose proof (bindD_res ρ _ s c vs Ds xs 0 vs (eq_sym B2) (fun j => eq_refl))
        as D2.
      rewrite D1 in D2. inversion D2; auto.
    - eapply IH; eauto.
  Qed.

  Definition Qtm (e : tm) : Prop := ∀ ρ m w,
    dest (O ρ m (denote m e)) = Some w → cost (O ρ m (denote m e)) ≤ G →
    ∃ N v, ev N e ρ = Some v ∧ w = lift v.
  Definition Qtms (es : tms) : Prop := ∀ c ρ m w,
    dest (O ρ m (denote_list m c es)) = Some w →
    cost (O ρ m (denote_list m c es)) ≤ G →
    ∃ N vs, ev_list (ev N) es ρ = Some vs ∧ w = vl_cstr c (lift_list vs).

  Lemma bwd_tm : (∀ e, Qtm e) ∧ (∀ es, Qtms es) ∧ (∀ bs : branches, True).
  Proof.
    apply tm_mutind; unfold Qtm, Qtms; auto.
    - (* Var *)
      intros x ρ m w D _. simpl in D. rewrite ?L_Ret in D. simpl in D.
      unfold rd in D. rewrite read_lift in D.
      destruct (rread x ρ) as [v|] eqn:R; simpl in D; inversion D; subst.
      exists 1, v. auto.
    - (* Fn *)
      intros x e _ ρ m w D _. simpl in D. inversion D; subst.
      exists 1, (r_clos x e ρ). auto.
    - (* App *)
      intros e1 IH1 e2 IH2 ρ m w D C. simpl in D, C.
      apply L_bind in D as (f & D1 & D2 & C1).
      apply L_bind in D2 as (a & D3 & D4 & C2).
      assert (wf_vl f) as Wf
          by (eapply wf_Ltr; [apply wf_lift_env|apply wf_den|exact D1]).
      assert (wf_vl a) as Wa
          by (eapply wf_Ltr; [apply wf_lift_env|apply wf_den|exact D3]).
      destruct (ap_a (lift_env ρ) (wf_lift_env ρ) m m f a w Wf Wa D4)
        as (f' & a' & c' & D5 & D6 & E & C3).
      destruct (L_join _ _ _ _ _ D1 D5) as [D7 C7].
      destruct (L_join _ _ _ _ _ D3 D6) as [D8 C8].
      destruct (IH1 ρ m f' D7 ltac:(lia)) as (N1 & vf & E1 & ->).
      destruct (IH2 ρ m a' D8 ltac:(lia)) as (N2 & va & E2 & ->).
      destruct E as (m0 & E). destruct (E m0 (Nat.le_refl _)) as [D0 C0].
      destruct vf as [?|x eb ρf|?]; simpl in D0, C0; try discriminate.
      rewrite call_eq in D0, C0. simpl in D0, C0.
      assert (evc (fun m2 => linkb m2 (lift_env (rcons x va ρf)) (den eb)) w
                (c' - 1)) as E'.
      { exists m0. intros m2 Hm2. destruct (E m2 Hm2) as [D' C'].
        simpl in D', C'. rewrite call_eq in D', C'. simpl in D', C'.
        split; [exact D'|simpl; lia]. }
      destruct (callee _ _ _ _ E' ltac:(lia)) as (N3 & v & E3 & ->).
      exists (S (Nat.max N1 (Nat.max N2 N3))), v. split; auto.
      simpl. rew_ev E1.
      rew_ev E2.
      eapply ev_mono; [|exact E3]; lia.
    - (* Link *)
      intros e1 IH1 e2 _ ρ m w D C. simpl in D, C.
      change (fun m0 : nat => denote m0 e2) with (den e2) in *.
      apply L_bind in D as (mraw & D1 & D2 & C1).
      assert (wf_vl mraw) as Wm
          by (eapply wf_Ltr; [apply wf_lift_env|apply wf_den|exact D1]).
      destruct mraw as [σ1|s|?|?]; simpl in D2, C1; try discriminate.
      + destruct (call_a (lift_env ρ) (wf_lift_env ρ) m σ1 (den e2) m w Wm
                    (wfb_den e2) D2) as (σ' & R & E & C2).
        destruct (L_join _ _ _ _ _ D1 R) as [D3 C3]. simpl in C3.
        destruct (IH1 ρ m _ D3 ltac:(lia)) as (N1 & v1 & E1 & Hv).
        destruct v1 as [ρ1|?|?]; simpl in Hv; inversion Hv; subst σ'; clear Hv.
        destruct (callee _ _ _ _ E ltac:(lia)) as (N2 & v & E2 & ->).
        exists (S (Nat.max N1 N2)), v. split; auto.
        simpl. rew_ev E1.
        eapply ev_mono; [|exact E2]; lia.
      + destruct (call_a (lift_env ρ) (wf_lift_env ρ) m (nv_sh s) (den e2) m w Wm
                    (wfb_den e2) D2) as (σ' & R & E & C2).
        simpl in R, C2. apply inv_bind in R as (m1 & R1 & R2 & CR).
        rewrite CR in C2.
        destruct (L_join _ _ _ _ _ D1 R1) as [D3 C3]. simpl in C3.
        destruct (IH1 ρ m _ D3 ltac:(lia)) as (N1 & v1 & E1 & ->).
        destruct v1 as [ρ1|?|?]; simpl in R2; inversion R2; subst σ'; clear R2.
        destruct (callee _ _ _ _ E ltac:(lia)) as (N2 & v & E2 & ->).
        exists (S (Nat.max N1 N2)), v. split; auto.
        simpl. rew_ev E1.
        eapply ev_mono; [|exact E2]; lia.
    - (* Mt *)
      intros ρ m w D _. simpl in D. inversion D; subst.
      exists 1, (r_exp rnil). auto.
    - (* Bind *)
      intros x e1 IH1 e2 _ ρ m w D C. simpl in D, C.
      change (fun m0 : nat => denote m0 e2) with (den e2) in *.
      apply L_bind in D as (v1r & D1 & D2 & C1).
      assert (wf_vl v1r) as W1
          by (eapply wf_Ltr; [apply wf_lift_env|apply wf_den|exact D1]).
      apply L_bind in D2 as (w2 & D3 & D4 & C2).
      destruct (bind_mod_inv ρ _ _ _ _ _ D4) as (v1' & r2 & D5 & D6 & C3 & H).
      destruct (L_join _ _ _ _ _ D1 D5) as [D7 C7].
      destruct (IH1 ρ m v1' D7 ltac:(lia)) as (N1 & v1 & E1 & ->).
      destruct (L_join _ _ _ _ _ D3 D6) as [D8 C8].
      assert (wf_nv (nv_bd x v1r (nv_sh Init))) as Wσ by (simpl; auto).
      destruct (enter ρ m _ (rcons x v1 ρ) e2 r2 Wσ D8 ltac:(lia))
        as (N2 & v2 & E2 & Hr2).
      { intros σ' R. simpl in R. apply dest_bind_inv in R as (u & R1 & R2).
        rewrite D5 in R1. inversion R1; subst u. simpl in R2.
        inversion R2; auto. }
      destruct (H v2 Hr2) as (ρ2 & -> & ->).
      exists (S (Nat.max N1 N2)), (r_exp (rcons x v1 ρ2)). split; auto.
      simpl. rew_ev E1.
      rew_ev E2. reflexivity.
    - (* Cstr *)
      intros c es IH ρ m w D C. simpl in D, C.
      destruct (IH c ρ m w D C) as (N & vs & E & ->).
      exists (S N), (r_cstr c vs). split; auto. simpl. rewrite E. reflexivity.
    - (* Case *)
      intros e IH bs _ ρ m w D C. simpl in D, C.
      apply L_bind in D as (mraw & D1 & D2 & C1).
      assert (wf_vl mraw) as Wm
          by (eapply wf_Ltr; [apply wf_lift_env|apply wf_den|exact D1]).
      destruct mraw as [?|s|?|c1 ws]; simpl in D2, C1; try discriminate.
      + (* the scrutinee was still unknown *)
        apply L_match in D2 as (c & vs1 & D3 & D4 & C2).
        destruct (L_join _ _ _ _ _ D1 D3) as [D5 C5]. simpl in C5.
        destruct (IH ρ m _ D5 ltac:(lia)) as (N1 & v0 & E1 & Hv).
        destruct v0 as [?|?|c0 vs]; simpl in Hv; inversion Hv; subst c0 vs1;
          clear Hv.
        rewrite vlen_lift in D4, C2.
        destruct (bwd_brs bs s c vs ρ m w Wm D3 D4 ltac:(lia))
          as (N2 & v & E2 & ->).
        exists (S (Nat.max N1 N2)), v. split; auto.
        simpl. rew_ev E1.
        eapply ev_sel_mono; [|exact E2]. intros. eapply ev_mono; [|eassumption]. lia.
      + (* the scrutinee was known to the symbolic run *)
        destruct (bwd_sel bs c1 ws ρ m w Wm D2 ltac:(lia)) as (ws' & D3 & C3 & H).
        destruct (L_join _ _ _ _ _ D1 D3) as [D5 C5]. simpl in C5.
        destruct (IH ρ m _ D5 ltac:(lia)) as (N1 & v0 & E1 & Hv).
        destruct v0 as [?|?|c0 vs]; simpl in Hv; inversion Hv; subst c0 ws';
          clear Hv.
        destruct (H vs eq_refl) as (N2 & v & E2 & ->).
        exists (S (Nat.max N1 N2)), v. split; auto.
        simpl. rew_ev E1.
        eapply ev_sel_mono; [|exact E2]. intros. eapply ev_mono; [|eassumption]. lia.
    - (* tnil *)
      intros c ρ m w D _. simpl in D. inversion D; subst.
      exists 0, rvnil. auto.
    - (* tcons *)
      intros e IHe es IHes c ρ m w D C. simpl in D, C.
      apply L_bind in D as (vr & D1 & D2 & C1).
      apply L_bind in D2 as (wl & D3 & D4 & C2).
      destruct wl as [?|?|?|c1 ws]; simpl in D4, C2; try discriminate.
      rewrite ?L_Ret in D4, C2. simpl in D4, C2.
      apply inv_bind in D4 as (v' & D5 & D6 & C3).
      apply inv_bind in D6 as (ml & D7 & D8 & C4).
      destruct (link_vls_leaf _ _ _ _ _ D7) as (ws' & -> & _). simpl in D8, C4.
      inversion D8; subst w; clear D8.
      destruct (L_join _ _ _ _ _ D1 D5) as [D9 C9].
      destruct (L_join _ _ _ _ _ D3 D7) as [D10 C10]. simpl in C10.
      destruct (IHe ρ m v' D9 ltac:(lia)) as (N1 & v0 & E1 & ->).
      destruct (IHes c ρ m _ D10 ltac:(lia)) as (N2 & vs & E2 & Hw).
      inversion Hw; subst c1 ws'; clear Hw.
      exists (Nat.max N1 N2), (rvcons v0 vs). split; auto.
      simpl. rew_ev E1.
      erewrite ev_list_mono; [reflexivity| |exact E2].
      intros. eapply ev_mono; [|eassumption]. lia.
  Qed.
End bwd.

Lemma bwd : ∀ G e ρ m w,
  dest (link_trace (call m) (lift_env ρ) (denote m e)) = Some w →
  cost (link_trace (call m) (lift_env ρ) (denote m e)) ≤ G →
  ∃ N v, ev N e ρ = Some v ∧ w = lift v.
Proof.
  induction G as [G IH] using lt_wf_ind. intros e ρ m w D C.
  destruct (bwd_tm G) as [H _].
  - intros e' ρ' m' w' D' C'. eapply (IH _ C'); eauto.
  - exact (H e ρ m w D C).
Qed.

(** ** The theorem *)

Theorem adequacy_fwd N e ρ v :
  ev N e ρ = Some v → ∃ n, run n (lift_env ρ) e = Some (lift v).
Proof.
  intros E. destruct (fwd N e ρ v E) as (m0 & H).
  exists (S m0). unfold run. rewrite linkb_S. apply H. lia.
Qed.

Theorem adequacy_bwd n e ρ w :
  run n (lift_env ρ) e = Some w → ∃ N v, ev N e ρ = Some v ∧ w = lift v.
Proof.
  unfold run. destruct n; [rewrite linkb_0; discriminate|].
  rewrite linkb_S. intros D. eapply bwd; eauto.
Qed.

(** For a closed program: the denotation, linked with the empty environment,
    terminates exactly when the interpreter does, and with the same result. *)
Corollary adequacy e :
  (∀ N v, ev N e rnil = Some v → ∃ n, run n nv_mt e = Some (lift v)) ∧
  (∀ n w, run n nv_mt e = Some w → ∃ N v, ev N e rnil = Some v ∧ w = lift v).
Proof.
  split.
  - intros N v E. exact (adequacy_fwd N e rnil v E).
  - intros n w R. exact (adequacy_bwd n e rnil w R).
Qed.

Corollary termination e :
  (∃ N v, ev N e rnil = Some v) ↔ (∃ n w, run n nv_mt e = Some w).
Proof.
  split.
  - intros (N & v & E). destruct (adequacy_fwd N e rnil v E) as (n & R). eauto.
  - intros (n & w & R).
    destruct (adequacy_bwd n e rnil w R) as (N & v & E & _). eauto.
Qed.
