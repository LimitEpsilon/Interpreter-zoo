(** * Linking twice is linking once

    Fix an outer environment [Σ0].  If the inner environment [σ] resolves
    under [Σ0] to [σ'], then for any [X]

      link Σ0 into (link σ into X)   and   link σ' into X

    return the same value (when either returns at all).  This is the exact
    form of the Advance Lemma: nothing is lost by evaluating early.

    Direction (a), in this file's first half, also bounds the number of
    guards, which is the induction measure for adequacy. *)
From Stdlib Require Import Utf8 String Bool Arith Lia List.
From Denot Require Import Syntax Domain Semantics Laws Wf Order Conv.

(** ** Decomposing an outer link *)

Section outer.
  Context (cl : nv → body → trace) (Σ0 : nv).
  Local Notation L := (link_trace cl Σ0) (only parsing).

  Lemma L_Bot : L Bot = Bot.
  Proof. reflexivity. Qed.

  Lemma L_Ret v : L (Ret v) = link_vl cl Σ0 v.
  Proof. reflexivity. Qed.

  Lemma L_split t r (D : dest (L t) = Some r) :
    ∃ w, dest (link_tr cl Σ0 t) = Some w ∧ dest (link_vl cl Σ0 w) = Some r ∧
         cost (L t) = cost (link_tr cl Σ0 t) + cost (link_vl cl Σ0 w).
  Proof. unfold link_trace in *. apply inv_bind in D. auto. Qed.

  Lemma L_join t w r (D1 : dest (link_tr cl Σ0 t) = Some w)
    (D2 : dest (link_vl cl Σ0 w) = Some r) :
    dest (L t) = Some r ∧
    cost (L t) = cost (link_tr cl Σ0 t) + cost (link_vl cl Σ0 w).
  Proof.
    unfold link_trace. split.
    - eapply dest_bind_intro; eauto.
    - apply cost_bind; auto.
  Qed.

  Lemma L_bind K t r (D : dest (L (bind K t)) = Some r) :
    ∃ w, dest (link_tr cl Σ0 t) = Some w ∧ dest (L (K w)) = Some r ∧
         cost (L (bind K t)) = cost (link_tr cl Σ0 t) + cost (L (K w)).
  Proof. rewrite link_trace_bind in *. apply inv_bind in D. auto. Qed.

  Lemma L_bind_intro K t w r (D1 : dest (link_tr cl Σ0 t) = Some w)
    (D2 : dest (L (K w)) = Some r) : dest (L (bind K t)) = Some r.
  Proof. rewrite link_trace_bind. eapply dest_bind_intro; eauto. Qed.

  Lemma L_guard u t r (D : dest (L (Guard u t)) = Some r) :
    ∃ u', dest (link_vl cl Σ0 u) = Some u' ∧ dest (L t) = Some r ∧
          cost (L (Guard u t)) = cost (link_vl cl Σ0 u) + S (cost (L t)).
  Proof.
    unfold link_trace in *. simpl in *. rewrite bind_bind in *.
    apply inv_bind in D as (u' & D1 & D2 & C). simpl in *. eauto.
  Qed.

  Lemma L_guard_intro u u' t r (D1 : dest (link_vl cl Σ0 u) = Some u')
    (D2 : dest (L t) = Some r) : dest (L (Guard u t)) = Some r.
  Proof.
    unfold link_trace in *. simpl. rewrite bind_bind.
    eapply dest_bind_intro; eauto.
  Qed.

  Lemma L_match s bs r (D : dest (L (Match s bs)) = Some r) :
    ∃ c vs, dest (link_shdw cl Σ0 s) = Some (vl_cstr c vs) ∧
      dest (bind (link_vl cl Σ0) (link_sel cl Σ0 c (vlen vs) bs)) = Some r ∧
      cost (L (Match s bs)) =
      cost (link_shdw cl Σ0 s) +
      S (cost (bind (link_vl cl Σ0) (link_sel cl Σ0 c (vlen vs) bs))).
  Proof.
    unfold link_trace in *. simpl in *. rewrite bind_bind in *.
    apply inv_bind in D as (m & D1 & D2 & C).
    destruct m as [?|?|?|c vs]; simpl in D2, C; try discriminate.
    exists c, vs. auto.
  Qed.

  (** *** The continuations of linking commute with an outer link *)

  Definition Kcomm (K : vl → trace) : Prop := ∀ w r,
    dest (L (K w)) = Some r →
    ∃ w', dest (link_vl cl Σ0 w) = Some w' ∧ dest (K w') = Some r ∧
          cost (link_vl cl Σ0 w) + cost (K w') ≤ cost (L (K w)).

  Lemma rd_comm x : Kcomm (rd x).
  Proof.
    intros w r. unfold rd. destruct w as [σm|s1|?|?]; try discriminate.
    - destruct (read x σm) as [v|] eqn:R; try discriminate. intros D.
      apply L_guard in D as (w' & D1 & D2 & C). rewrite ?L_Ret in *.
      simpl in D1. destruct (link_nv_leaf _ _ _ _ D1) as (σm' & ->).
      pose proof (read_link _ _ _ _ _ _ _ D1 R D2) as R'.
      exists (vl_exp σm'). rewrite R'. rewrite C. simpl. repeat split; auto. lia.
    - intros D. rewrite ?L_Ret in *. simpl in D.
      apply inv_bind in D as (w' & D1 & D2 & C). exists w'. simpl. rewrite C.
      repeat split; auto.
  Qed.

  Lemma ds_comm c i : Kcomm (ds c i).
  Proof.
    intros w r. unfold ds. destruct w as [?|s1|?|c' vs]; try discriminate.
    - intros D. rewrite ?L_Ret in *. simpl in D.
      apply inv_bind in D as (w' & D1 & D2 & C). exists w'. simpl. rewrite C.
      repeat split; auto.
    - destruct (String.eqb c c') eqn:E; try discriminate.
      destruct (vnth i vs) as [v|] eqn:N; try discriminate. intros D.
      apply L_guard in D as (w' & D1 & D2 & C). rewrite ?L_Ret in *.
      simpl in D1. destruct (link_vls_leaf _ _ _ _ _ D1) as (vs' & -> & _).
      pose proof (vnth_link _ _ _ _ _ _ _ _ D1 N D2) as N'.
      exists (vl_cstr c' vs'). rewrite E, N'. rewrite C. simpl.
      repeat split; auto. lia.
  Qed.

  Lemma mod_comm : Kcomm (on_mod (fun σ1 => Ret (vl_exp σ1))).
  Proof.
    intros w r. destruct w as [σ1|s1|?|?]; simpl; try discriminate; intros D.
    - rewrite ?L_Ret in *. simpl in D.
      destruct (link_nv_leaf _ _ _ _ D) as (σ1' & ->).
      exists (vl_exp σ1'). simpl. repeat split; auto. lia.
    - rewrite ?L_Ret in *. simpl in D.
      apply inv_bind in D as (w' & D1 & D2 & C). exists w'. simpl. rewrite C.
      repeat split; auto.
  Qed.

  Lemma clos_comm x b : Kcomm (on_env (fun σ2 => Ret (vl_clos x b σ2))).
  Proof.
    intros w r. destruct w as [σ2|?|?|?]; simpl; try discriminate; intros D.
    rewrite ?L_Ret in *. simpl in D.
    apply inv_bind in D as (w' & D1 & D2 & C). exists w'. simpl. rewrite C.
    repeat split; auto.
  Qed.

  (** *** … and conversely *)

  Definition Kcomm_b (P : vl → Prop) (K : vl → trace) : Prop := ∀ w w' r,
    P w → dest (link_vl cl Σ0 w) = Some w' → dest (K w') = Some r →
    dest (L (K w)) = Some r.

  Lemma rd_comm_b x : Kcomm_b (fun _ => True) (rd x).
  Proof.
    intros w w' r _ D1 D2. destruct w as [σm|s1|?|?]; simpl in D1.
    - destruct (link_nv_leaf _ _ _ _ D1) as (σm' & ->). unfold rd in *.
      destruct (read x σm') as [r'|] eqn:R'; simpl in D2; inversion D2; subst.
      destruct (read_link_inv _ _ _ _ _ _ D1 R') as (v & R & Dv). rewrite R.
      eapply L_guard_intro; [exact D1|]. rewrite ?L_Ret. exact Dv.
    - simpl. rewrite ?L_Ret. simpl. eapply dest_bind_intro; eauto.
    - apply dest_bind_inv in D1 as (m & _ & D1).
      destruct m; simpl in D1; inversion D1; subst. discriminate.
    - destruct (link_vls_leaf _ _ _ _ _ D1) as (vs' & -> & _). discriminate.
  Qed.

  Lemma ds_comm_b c i : Kcomm_b (fun _ => True) (ds c i).
  Proof.
    intros w w' r _ D1 D2. destruct w as [σm|s1|?|c' vs]; simpl in D1.
    - destruct (link_nv_leaf _ _ _ _ D1) as (σm' & ->). discriminate.
    - simpl. rewrite ?L_Ret. simpl. eapply dest_bind_intro; eauto.
    - apply dest_bind_inv in D1 as (m & _ & D1).
      destruct m; simpl in D1; inversion D1; subst. discriminate.
    - destruct (link_vls_leaf _ _ _ _ _ D1) as (vs' & -> & _). unfold ds in *.
      destruct (String.eqb c c'); try discriminate.
      destruct (vnth i vs') as [r'|] eqn:N'; simpl in D2; inversion D2; subst.
      destruct (vnth_link_inv _ _ _ _ _ _ _ D1 N') as (v & N & Dv). rewrite N.
      eapply L_guard_intro; [exact D1|]. rewrite ?L_Ret. exact Dv.
  Qed.

  Lemma mod_comm_b : Kcomm_b (fun _ => True) (on_mod (fun σ1 => Ret (vl_exp σ1))).
  Proof.
    intros w w' r _ D1 D2. destruct w as [σ1|s1|?|?]; simpl in D1.
    - destruct (link_nv_leaf _ _ _ _ D1) as (σ1' & ->). simpl in D2.
      inversion D2; subst. simpl. rewrite ?L_Ret. exact D1.
    - simpl. rewrite ?L_Ret. simpl. eapply dest_bind_intro; eauto.
    - apply dest_bind_inv in D1 as (m & _ & D1).
      destruct m; simpl in D1; inversion D1; subst. discriminate.
    - destruct (link_vls_leaf _ _ _ _ _ D1) as (vs' & -> & _). discriminate.
  Qed.

  Lemma clos_comm_b x b :
    Kcomm_b is_exp (on_env (fun σ2 => Ret (vl_clos x b σ2))).
  Proof.
    intros w w' r Hw D1 D2. destruct w as [σ2|?|?|?]; simpl in Hw; try tauto.
    simpl. rewrite ?L_Ret. simpl. eapply dest_bind_intro; eauto.
  Qed.
End outer.

Section LL.
  Context (Σ0 : nv) (HΣ0 : wf_nv Σ0).
  Local Notation L m := (link_trace (call m) Σ0) (only parsing).

  (** [σ] resolves to [σ'] under [Σ0] *)
  Definition res (σ σ' : nv) : Prop :=
    ∃ m0, dest (link_nv (call m0) Σ0 σ) = Some (vl_exp σ').

  Let Hwfc : ∀ m σ b, wf_nv σ → wfb b → wf_tr (call m σ b).
  Proof. intros; apply wf_call; auto. Qed.

  Lemma wf_Lvl m v r (W : wf_vl v) (D : dest (link_vl (call m) Σ0 v) = Some r) : wf_vl r.
  Proof. eapply wf_dest; [|exact D]. apply wf_link; auto. Qed.

  Lemma wf_Ltr m t w (W : wf_tr t) (D : dest (link_tr (call m) Σ0 t) = Some w) : wf_vl w.
  Proof. eapply wf_dest; [|exact D]. apply wf_link_tr; auto. Qed.

  Lemma wf_res σ σ' (W : wf_nv σ) (R : res σ σ') : wf_nv σ'.
  Proof.
    destruct R as (m0 & D).
    change (wf_vl (vl_exp σ')). eapply wf_Lvl with (v := vl_exp σ); eauto.
  Qed.

  Lemma res_det σ σ' m w (W : wf_nv σ) (R : res σ σ')
    (D : dest (link_nv (call m) Σ0 σ) = Some w) : w = vl_exp σ'.
  Proof.
    destruct R as (m0 & D0).
    pose proof (up_nv m (Nat.max m m0) ltac:(lia) Σ0 HΣ0 σ _ W D) as E1.
    pose proof (up_nv m0 (Nat.max m m0) ltac:(lia) Σ0 HΣ0 σ _ W D0) as E2.
    rewrite <- E1, E2, D0 in D. congruence.
  Qed.

  Lemma step1 m K Tin F r
    (KC : Kcomm (call m) Σ0 K)
    (IH : ∀ w', dest (L m Tin) = Some w' → evc F w' (cost (L m Tin)))
    (D : dest (L m (bind K Tin)) = Some r) :
    evc (fun m2 => bind K (F m2)) r (cost (L m (bind K Tin))).
  Proof.
    apply L_bind in D as (w & D1 & D2 & C).
    apply KC in D2 as (w' & D3 & D4 & C').
    destruct (L_join _ _ _ _ _ D1 D3) as [D5 C5].
    specialize (IH _ D5).
    eapply evc_weaken.
    - apply evc_bind with (K := fun _ => K) (w := w'); [exact IH|].
      apply evc_const; [exact D4|apply Nat.le_refl].
    - rewrite C, C5. lia.
  Qed.

  (** ** Direction (a): from two links to one, with a bound on guards *)
  Section a.
    Context (n : nat).
    Context (Hcall : ∀ σc b σc' m r, wf_nv σc → wfb b → res σc σc' →
      dest (L m (linkb n σc b)) = Some r →
      evc (fun m2 => linkb m2 σc' b) r (cost (L m (linkb n σc b)))).

    Definition Pa_shdw (s : shdw) : Prop := ∀ σ σ' m r,
      wf_shdw s → wf_nv σ → res σ σ' →
      dest (L m (link_shdw (call n) σ s)) = Some r →
      evc (fun m2 => link_shdw (call m2) σ' s) r
          (cost (L m (link_shdw (call n) σ s))).
    Definition Pa_nv (σ1 : nv) : Prop := ∀ σ σ' m r,
      wf_nv σ1 → wf_nv σ → res σ σ' →
      dest (L m (link_nv (call n) σ σ1)) = Some r →
      evc (fun m2 => link_nv (call m2) σ' σ1) r
          (cost (L m (link_nv (call n) σ σ1))).
    Definition Pa_vl (v : vl) : Prop := ∀ σ σ' m r,
      wf_vl v → wf_nv σ → res σ σ' →
      dest (L m (link_vl (call n) σ v)) = Some r →
      evc (fun m2 => link_vl (call m2) σ' v) r
          (cost (L m (link_vl (call n) σ v))).
    Definition Pa_vls (vs : vls) : Prop := ∀ c σ σ' m r,
      wf_vls vs → wf_nv σ → res σ σ' →
      dest (L m (link_vls (call n) σ c vs)) = Some r →
      evc (fun m2 => link_vls (call m2) σ' c vs) r
          (cost (L m (link_vls (call n) σ c vs))).

    Lemma ap_comm m f a r (Wf : wf_vl f) (Wa : wf_vl a)
      (D : dest (L m (ap (call n) f a)) = Some r) :
      ∃ f' a' c',
        dest (link_vl (call m) Σ0 f) = Some f' ∧
        dest (link_vl (call m) Σ0 a) = Some a' ∧
        evc (fun m2 => ap (call m2) f' a') r c' ∧
        cost (link_vl (call m) Σ0 f) + cost (link_vl (call m) Σ0 a) + c'
          ≤ cost (L m (ap (call n) f a)).
    Proof.
      destruct f as [?|s1|x b σf|?]; simpl in D; try discriminate.
      - (* an unknown function: the call stays pending, the outer link runs it *)
        rewrite ?L_Ret in D. simpl in D.
        apply inv_bind in D as (f' & D1 & D2 & C1).
        apply inv_bind in D2 as (a' & D3 & D4 & C2).
        exists f', a', (cost (ap (call m) f' a')). repeat split; auto.
        + apply evc_up with (m0 := m); auto.
          intros m2 LE. eapply up_ap; eauto.
          * eapply wf_Lvl with (v := vl_sh s1); eauto.
          * eapply wf_Lvl; eauto.
        + simpl. rewrite ?L_Ret. simpl. rewrite C1, C2. lia.
      - (* a known closure: its body was linked by the inner link *)
        destruct Wf as [Wb Wσf].
        rewrite call_eq in D. apply L_guard in D as (u' & D1 & D2 & C1).
        simpl in D1. apply inv_bind in D1 as (a' & D3 & D4 & C2).
        apply inv_bind in D4 as (mσ & D5 & D6 & C3).
        destruct (link_nv_leaf _ _ _ _ D5) as (σf' & ->). simpl in D6, C3.
        inversion D6; subst u'; clear D6.
        assert (res (nv_bd x a σf) (nv_bd x a' σf')) as R.
        { exists m. simpl. eapply dest_bind_intro; eauto.
          eapply dest_bind_intro; eauto. }
        assert (wf_nv (nv_bd x a σf)) as Wc by (simpl; auto).
        pose proof (Hcall _ _ _ _ _ Wc Wb R D2) as E.
        exists (vl_clos x b σf'), a', (S (cost (L m (linkb n (nv_bd x a σf) b)))).
        repeat split; auto.
        + simpl. eapply dest_bind_intro; eauto.
        + simpl. eapply evc_ext; [|apply evc_guard; exact E].
          intros m2. simpl. rewrite call_eq. reflexivity.
        + simpl. erewrite cost_bind by eauto. simpl.
          rewrite call_eq, C1. simpl. rewrite C2, C3. lia.
    Qed.

    Lemma LLa_vals :
      (∀ s, Pa_shdw s) ∧ (∀ σ1, Pa_nv σ1) ∧ (∀ v, Pa_vl v) ∧ (∀ vs, Pa_vls vs).
    Proof.
      assert (∀ σ, wf_nv σ →
        (∀ s, wf_shdw s → wf_tr (link_shdw (call n) σ s)) ∧
        (∀ σ1, wf_nv σ1 → wf_tr (link_nv (call n) σ σ1)) ∧
        (∀ v, wf_vl v → wf_tr (link_vl (call n) σ v)) ∧
        (∀ vs, wf_vls vs → ∀ c, wf_tr (link_vls (call n) σ c vs))) as WL.
      { intros. apply wf_link; auto. }
      apply val_mutind; unfold Pa_shdw, Pa_nv, Pa_vl, Pa_vls.
      - (* Init *)
        intros σ σ' m r _ Wσ R D. simpl in D. rewrite ?L_Ret in D. simpl in D.
        rewrite (res_det _ _ _ _ Wσ R D). simpl.
        apply evc_const; simpl; auto. lia.
      - (* Read *)
        intros s x IH σ σ' m r Ws Wσ R D. simpl in D |- *.
        eapply step1; eauto using rd_comm.
      - (* Call *)
        intros s v IHs IHv σ σ' m r [Ws Wv] Wσ R D. simpl in D |- *.
        destruct (WL σ Wσ) as (WLs & _ & WLv & _).
        apply L_bind in D as (f & D1 & D2 & C1).
        apply L_bind in D2 as (a & D3 & D4 & C2).
        apply ap_comm in D4 as (f' & a' & c' & D5 & D6 & E & C3);
          [|eapply wf_Ltr; [|exact D1]; auto|eapply wf_Ltr; [|exact D3]; auto].
        destruct (L_join _ _ _ _ _ D1 D5) as [D7 C7].
        destruct (L_join _ _ _ _ _ D3 D6) as [D8 C8].
        specialize (IHs σ σ' m f' Ws Wσ R D7).
        specialize (IHv σ σ' m a' Wv Wσ R D8).
        eapply evc_weaken.
        + apply evc_bind with
            (K := fun m2 f0 => bind (fun a0 => ap (call m2) f0 a0)
                                 (link_vl (call m2) σ' v)) (w := f');
            [exact IHs|].
          apply evc_bind with (K := fun m2 a0 => ap (call m2) f' a0) (w := a');
            [exact IHv|exact E].
        + rewrite C1, C2, C7, C8. lia.
      - (* Dstr *)
        intros s c i IH σ σ' m r Ws Wσ R D. simpl in D |- *.
        eapply step1; eauto using ds_comm.
      - (* nv_mt *)
        intros σ σ' m r _ Wσ R D. simpl in D |- *. rewrite ?L_Ret in D |- *.
        simpl in D |- *. apply evc_const; simpl; auto.
      - (* nv_sh *)
        intros s IH σ σ' m r Ws Wσ R D. simpl in D |- *.
        eapply step1; eauto using mod_comm.
      - (* nv_bd *)
        intros x v σ1 IHv IHσ1 σ σ' m r [Wv Wσ1] Wσ R D. simpl in D |- *.
        apply L_bind in D as (v' & D1 & D2 & C1).
        apply L_bind in D2 as (w & D3 & D4 & C2).
        destruct w as [σ2|?|?|?]; simpl in D4, C2; try discriminate.
        rewrite ?L_Ret in D4, C2. simpl in D4, C2.
        apply inv_bind in D4 as (v'' & D5 & D6 & C3).
        apply inv_bind in D6 as (mσ & D7 & D8 & C4).
        destruct (link_nv_leaf _ _ _ _ D7) as (σ2' & ->). simpl in D8, C4.
        inversion D8; subst r; clear D8.
        destruct (L_join _ _ _ _ _ D1 D5) as [D9 C9].
        destruct (L_join _ _ _ _ _ D3 D7) as [D10 C10].
        specialize (IHv σ σ' m v'' Wv Wσ R D9).
        specialize (IHσ1 σ σ' m (vl_exp σ2') Wσ1 Wσ R D10).
        eapply evc_weaken.
        + apply evc_bind with
            (K := fun m2 v0 => bind (on_env (fun σ'' => Ret (vl_exp (nv_bd x v0 σ''))))
                                 (link_nv (call m2) σ' σ1)) (w := v'');
            [exact IHv|].
          apply evc_bind with
            (K := fun _ => on_env (fun σ'' => Ret (vl_exp (nv_bd x v'' σ''))))
            (w := vl_exp σ2'); [exact IHσ1|].
          apply evc_const; simpl; auto.
        + rewrite C1, C2, C3, C4, C9, C10. simpl. lia.
      - (* vl_exp *) intros σ1 IH. exact IH.
      - (* vl_sh *) intros s IH. exact IH.
      - (* vl_clos *)
        intros x b σ1 IH σ σ' m r [Wb Wσ1] Wσ R D. simpl in D |- *.
        eapply step1; eauto using clos_comm.
      - (* vl_cstr *) intros c vs IH σ σ' m r. apply IH.
      - (* vnil *)
        intros c σ σ' m r _ Wσ R D. simpl in D |- *. rewrite ?L_Ret in D |- *.
        simpl in D |- *. apply evc_const; simpl; auto.
      - (* vcons *)
        intros v vs IHv IHvs c σ σ' m r [Wv Wvs] Wσ R D. simpl in D |- *.
        apply L_bind in D as (v' & D1 & D2 & C1).
        apply L_bind in D2 as (w & D3 & D4 & C2).
        destruct w as [?|?|?|c1 vs1]; simpl in D4, C2; try discriminate.
        rewrite ?L_Ret in D4, C2. simpl in D4, C2.
        apply inv_bind in D4 as (v'' & D5 & D6 & C3).
        apply inv_bind in D6 as (mσ & D7 & D8 & C4).
        destruct (link_vls_leaf _ _ _ _ _ D7) as (vs1' & -> & _). simpl in D8, C4.
        inversion D8; subst r; clear D8.
        destruct (L_join _ _ _ _ _ D1 D5) as [D9 C9].
        destruct (L_join _ _ _ _ _ D3 D7) as [D10 C10].
        specialize (IHv σ σ' m v'' Wv Wσ R D9).
        specialize (IHvs c σ σ' m (vl_cstr c1 vs1') Wvs Wσ R D10).
        eapply evc_weaken.
        + apply evc_bind with
            (K := fun m2 v0 => bind (on_cstr (fun c' vs'' => Ret (vl_cstr c' (vcons v0 vs''))))
                                 (link_vls (call m2) σ' c vs)) (w := v'');
            [exact IHv|].
          apply evc_bind with
            (K := fun _ => on_cstr (fun c' vs'' => Ret (vl_cstr c' (vcons v'' vs''))))
            (w := vl_cstr c1 vs1'); [exact IHvs|].
          apply evc_const; simpl; auto.
        + rewrite C1, C2, C3, C4, C9, C10. simpl. lia.
    Qed.

    (** the spine of a trace *)
    Definition Pa_tr (t : trace) : Prop := ∀ σ σ' m w,
      wf_tr t → wf_nv σ → res σ σ' →
      dest (link_tr (call m) Σ0 (link_tr (call n) σ t)) = Some w →
      evc (fun m2 => link_tr (call m2) σ' t) w
          (cost (link_tr (call m) Σ0 (link_tr (call n) σ t))).
    Definition Pa_brs (bs : brs) : Prop := ∀ σ σ' m w c k,
      wf_brs bs → wf_nv σ → res σ σ' →
      (dest (link_sel (call m) Σ0 c k (link_brs (call n) σ bs)) = Some w →
       evc (fun m2 => link_sel (call m2) σ' c k bs) w
           (cost (link_sel (call m) Σ0 c k (link_brs (call n) σ bs)))) ∧
      (dest (link_tr (call m) Σ0 (link_sel (call n) σ c k bs)) = Some w →
       evc (fun m2 => link_sel (call m2) σ' c k bs) w
           (cost (link_tr (call m) Σ0 (link_sel (call n) σ c k bs)))).

    Lemma LLa_tr : (∀ t, Pa_tr t) ∧ (∀ bs, Pa_brs bs).
    Proof.
      destruct LLa_vals as (Vs & Vn & Vv & Vvs).
      apply tr_mutind; unfold Pa_tr, Pa_brs.
      - intros σ σ' m w _ Wσ R D. simpl in D. discriminate.
      - intros v σ σ' m w _ Wσ R D. simpl in D |- *.
        apply evc_const; simpl; auto.
      - (* Guard *)
        intros u t IH σ σ' m w [Wu Wt] Wσ R D. simpl in D |- *.
        rewrite link_tr_bind in D |- *.
        apply inv_bind in D as (u' & D1 & D2 & C1). simpl in D2, C1.
        apply inv_bind in D2 as (u'' & D3 & D4 & C2). simpl in D4, C2.
        destruct (L_join _ _ _ _ _ D1 D3) as [D5 C5].
        pose proof (Vv u σ σ' m u'' Wu Wσ R D5) as E1.
        pose proof (IH σ σ' m w Wt Wσ R D4) as E2.
        eapply evc_weaken.
        + apply evc_bind with
            (K := fun m2 u0 => Guard u0 (link_tr (call m2) σ' t)) (w := u'');
            [exact E1|]. apply evc_guard. exact E2.
        + simpl in *. lia.
      - (* Match *)
        intros s bs IH σ σ' m w [Ws Wb] Wσ R D. simpl in D |- *.
        rewrite link_tr_bind in D |- *.
        apply inv_bind in D as (mraw & D1 & D2 & C1).
        destruct mraw as [?|s1|?|c vs]; simpl in D2, C1; try discriminate.
        + (* still unknown after the inner link; the outer link decides *)
          apply inv_bind in D2 as (m'' & D3 & D4 & C2).
          destruct m'' as [?|?|?|c vs'']; simpl in D4, C2; try discriminate.
          destruct (L_join _ _ _ _ _ D1 D3) as [D5 C5].
          pose proof (Vs s σ σ' m _ Ws Wσ R D5) as E1.
          destruct (IH σ σ' m w c (vlen vs'') Wb Wσ R) as [IH1 _].
          specialize (IH1 D4).
          eapply evc_weaken.
          * apply evc_bind with
              (K := fun m2 m0 =>
                 match m0 with
                 | vl_sh s' => Match s' (link_brs (call m2) σ' bs)
                 | vl_cstr c vs => Guard m0 (link_sel (call m2) σ' c (vlen vs) bs)
                 | _ => Bot
                 end) (w := vl_cstr c vs''); [exact E1|].
            apply evc_guard. exact IH1.
          * simpl in *. lia.
        + (* decided by the inner link *)
          apply inv_bind in D2 as (m'' & D3 & D4 & C2).
          destruct (link_vls_leaf _ _ _ _ _ D3) as (vs'' & -> & Hlen).
          simpl in D4, C2.
          destruct (L_join _ _ _ _ _ D1 D3) as [D5 C5].
          pose proof (Vs s σ σ' m _ Ws Wσ R D5) as E1.
          destruct (IH σ σ' m w c (vlen vs) Wb Wσ R) as [_ IH2].
          specialize (IH2 D4).
          eapply evc_weaken.
          * apply evc_bind with
              (K := fun m2 m0 =>
                 match m0 with
                 | vl_sh s' => Match s' (link_brs (call m2) σ' bs)
                 | vl_cstr c vs => Guard m0 (link_sel (call m2) σ' c (vlen vs) bs)
                 | _ => Bot
                 end) (w := vl_cstr c vs''); [exact E1|].
            rewrite Hlen. apply evc_guard. exact IH2.
          * simpl in *. lia.
      - intros σ σ' m w c k _ Wσ R. split; simpl; intros D; discriminate.
      - intros c0 n0 t bs IHt IHb σ σ' m w c k [Wt Wb] Wσ R.
        destruct (IHb σ σ' m w c k Wb Wσ R) as [IH1 IH2].
        split; simpl; destruct (String.eqb c c0 && Nat.eqb k n0); intros D; auto.
    Qed.

    Lemma LLa_trace t σ σ' m r (Wt : wf_tr t) (Wσ : wf_nv σ) (R : res σ σ')
      (D : dest (L m (link_trace (call n) σ t)) = Some r) :
      evc (fun m2 => link_trace (call m2) σ' t) r
          (cost (L m (link_trace (call n) σ t))).
    Proof.
      destruct LLa_vals as (Vs & Vn & Vv & Vvs). destruct LLa_tr as [Vt _].
      unfold link_trace at 2 in D. unfold link_trace at 3.
      apply L_bind in D as (w & D1 & D2 & C).
      assert (wf_vl w) as Ww.
      { eapply wf_Ltr; [|exact D1]. apply wf_link_tr; auto. }
      pose proof (Vt t σ σ' m w Wt Wσ R D1) as E1.
      pose proof (Vv w σ σ' m r Ww Wσ R D2) as E2.
      eapply evc_weaken.
      - unfold link_trace.
        apply evc_bind with (K := fun m2 => link_vl (call m2) σ') (w := w);
          [exact E1|exact E2].
      - rewrite C. lia.
    Qed.
  End a.

  (** ** Direction (b): from one link to two *)

  Lemma Ltr_up m1 m (LE : m1 ≤ m) t t' w (W : wf_tr t) (LEt : le_tr t t')
    (D : dest (link_tr (call m1) Σ0 t) = Some w) :
    dest (link_tr (call m) Σ0 t') = Some w.
  Proof. rewrite (up_tr m1 m LE Σ0 HΣ0 t t' w W LEt D). exact D. Qed.

  Lemma L_up m1 m (LE : m1 ≤ m) t t' r (W : wf_tr t) (LEt : le_tr t t')
    (D : dest (L m1 t) = Some r) : dest (L m t') = Some r.
  Proof. rewrite (up_trace m1 m LE Σ0 HΣ0 t t' r W LEt D). exact D. Qed.

  (** the inner link is monotone in its fuel *)
  Lemma le_in n1 n (LE : n1 ≤ n) σ (Wσ : wf_nv σ) :
    (∀ s, wf_shdw s → le_tr (link_shdw (call n1) σ s) (link_shdw (call n) σ s)) ∧
    (∀ σ1, wf_nv σ1 → le_tr (link_nv (call n1) σ σ1) (link_nv (call n) σ σ1)) ∧
    (∀ v, wf_vl v → le_tr (link_vl (call n1) σ v) (link_vl (call n) σ v)) ∧
    (∀ vs, wf_vls vs → ∀ c,
       le_tr (link_vls (call n1) σ c vs) (link_vls (call n) σ c vs)).
  Proof. apply le_link; auto. intros. apply le_call; auto. Qed.

  Section b.
    Context (m' : nat).
    Context (Hcallb : ∀ σc b σc' r, wf_nv σc → wfb b → res σc σc' →
      dest (linkb m' σc' b) = Some r →
      ev2 (fun n m => L m (linkb n σc b)) r).

    Definition Pb_shdw (s : shdw) : Prop := ∀ σ σ' r,
      wf_shdw s → wf_nv σ → res σ σ' →
      dest (link_shdw (call m') σ' s) = Some r →
      ev2 (fun n m => L m (link_shdw (call n) σ s)) r.
    Definition Pb_nv (σ1 : nv) : Prop := ∀ σ σ' r,
      wf_nv σ1 → wf_nv σ → res σ σ' →
      dest (link_nv (call m') σ' σ1) = Some r →
      ev2 (fun n m => L m (link_nv (call n) σ σ1)) r.
    Definition Pb_vl (v : vl) : Prop := ∀ σ σ' r,
      wf_vl v → wf_nv σ → res σ σ' →
      dest (link_vl (call m') σ' v) = Some r →
      ev2 (fun n m => L m (link_vl (call n) σ v)) r.
    Definition Pb_vls (vs : vls) : Prop := ∀ c σ σ' r,
      wf_vls vs → wf_nv σ → res σ σ' →
      dest (link_vls (call m') σ' c vs) = Some r →
      ev2 (fun n m => L m (link_vls (call n) σ c vs)) r.

    Lemma step1_b P K (Tin : nat → trace) r' r
      (KC : ∀ m, Kcomm_b (call m) Σ0 P K)
      (SH : ∀ n, leaves P (Tin n))
      (IH : ev2 (fun n m => L m (Tin n)) r')
      (D : dest (K r') = Some r) :
      ev2 (fun n m => L m (bind K (Tin n))) r.
    Proof.
      destruct IH as (n0 & m0 & IH). exists n0, m0. intros n m Hn Hm.
      specialize (IH n m Hn Hm). apply L_split in IH as (w & D1 & D2 & _).
      eapply L_bind_intro; [exact D1|]. eapply KC; eauto.
      eapply sel_leaf; [apply (SH n)|exact D1].
    Qed.

    Lemma ap_comm_b f a f' a' r m1 (Wf : wf_vl f) (Wa : wf_vl a)
      (D1 : dest (link_vl (call m1) Σ0 f) = Some f')
      (D2 : dest (link_vl (call m1) Σ0 a) = Some a')
      (D : dest (ap (call m') f' a') = Some r) :
      ev2 (fun n m => L m (ap (call n) f a)) r.
    Proof.
      assert (wf_vl f') as Wf' by (eapply wf_Lvl; [exact Wf|exact D1]).
      assert (wf_vl a') as Wa' by (eapply wf_Lvl; [exact Wa|exact D2]).
      destruct f as [σ1|s1|x b σf|c vs].
      - simpl in D1. destruct (link_nv_leaf _ _ _ _ D1) as (σ1' & ->). discriminate.
      - simpl in D1. exists 0, (Nat.max m1 m'). intros n m _ Hm. simpl.
        rewrite ?L_Ret. simpl.
        rewrite (up_shdw m1 m ltac:(lia) Σ0 HΣ0 s1 f' Wf D1).
        rewrite (up_vl m1 m ltac:(lia) Σ0 HΣ0 a a' Wa D2).
        eapply dest_bind_intro; [exact D1|]. eapply dest_bind_intro; [exact D2|].
        rewrite (up_ap m' m ltac:(lia) f' a' r Wf' Wa' D). exact D.
      - destruct Wf as [Wb Wσf]. simpl in D1.
        apply dest_bind_inv in D1 as (mσ & D3 & D4).
        destruct (link_nv_leaf _ _ _ _ D3) as (σf' & ->). simpl in D4.
        inversion D4; subst f'; clear D4. simpl in D. rewrite call_eq in D.
        simpl in D.
        assert (dest (link_nv (call m1) Σ0 (nv_bd x a σf)) =
                Some (vl_exp (nv_bd x a' σf'))) as Dres.
        { simpl. eapply dest_bind_intro; eauto. eapply dest_bind_intro; eauto. }
        assert (wf_nv (nv_bd x a σf)) as Wc by (simpl; auto).
        destruct (Hcallb (nv_bd x a σf) b (nv_bd x a' σf') r Wc Wb
                    (ex_intro _ m1 Dres) D) as (n0 & m0 & H).
        exists n0, (Nat.max m0 m1). intros n m Hn Hm. simpl. rewrite call_eq.
        eapply L_guard_intro with (u' := vl_exp (nv_bd x a' σf'));
          [|apply H; lia].
        change (dest (link_nv (call m) Σ0 (nv_bd x a σf)) =
                Some (vl_exp (nv_bd x a' σf'))).
        rewrite (up_nv m1 m ltac:(lia) Σ0 HΣ0 _ _ Wc Dres). exact Dres.
      - simpl in D1. destruct (link_vls_leaf _ _ _ _ _ D1) as (vs' & -> & _).
        discriminate.
    Qed.

    Lemma LLb_vals :
      (∀ s, Pb_shdw s) ∧ (∀ σ1, Pb_nv σ1) ∧ (∀ v, Pb_vl v) ∧ (∀ vs, Pb_vls vs).
    Proof.
      assert (∀ n σ, wf_nv σ →
        (∀ s, wf_shdw s → wf_tr (link_shdw (call n) σ s)) ∧
        (∀ σ1, wf_nv σ1 → wf_tr (link_nv (call n) σ σ1)) ∧
        (∀ v, wf_vl v → wf_tr (link_vl (call n) σ v)) ∧
        (∀ vs, wf_vls vs → ∀ c, wf_tr (link_vls (call n) σ c vs))) as WL.
      { intros. apply wf_link; auto. }
      apply val_mutind; unfold Pb_shdw, Pb_nv, Pb_vl, Pb_vls.
      - (* Init *)
        intros σ σ' r _ Wσ R D. simpl in D. inversion D; subst.
        destruct R as (m0 & R). exists 0, m0. intros n m _ Hm. simpl.
        rewrite ?L_Ret. simpl. rewrite (up_nv m0 m Hm Σ0 HΣ0 σ _ Wσ R). exact R.
      - (* Read *)
        intros s x IH σ σ' r Ws Wσ R D. simpl in D |- *.
        apply dest_bind_inv in D as (r' & D1 & D2).
        eapply step1_b with (P := fun _ => True) (r' := r'); eauto.
        + intros; apply rd_comm_b.
        + intros; apply leaves_True.
      - (* Call *)
        intros s v IHs IHv σ σ' r [Ws Wv] Wσ R D. simpl in D |- *.
        apply dest_bind_inv in D as (f' & D1 & D2).
        apply dest_bind_inv in D2 as (a' & D3 & D4).
        destruct (IHs σ σ' f' Ws Wσ R D1) as (n1 & m1 & H1).
        destruct (IHv σ σ' a' Wv Wσ R D3) as (n2 & m2 & H2).
        set (N := Nat.max n1 n2). set (M := Nat.max m1 m2).
        pose proof (H1 N M ltac:(lia) ltac:(lia)) as E1.
        pose proof (H2 N M ltac:(lia) ltac:(lia)) as E2.
        apply L_split in E1 as (f & F1 & F2 & _).
        apply L_split in E2 as (a & A1 & A2 & _).
        destruct (WL N σ Wσ) as (WLs & _ & WLv & _).
        assert (wf_vl f) as Wf by (eapply wf_Ltr; [|exact F1]; auto).
        assert (wf_vl a) as Wa by (eapply wf_Ltr; [|exact A1]; auto).
        destruct (ap_comm_b f a f' a' r M Wf Wa F2 A2 D4) as (n3 & m3 & H3).
        exists (Nat.max N n3), (Nat.max M m3). intros n m Hn Hm.
        destruct (le_in N n ltac:(lia) σ Wσ) as (LEs & _ & LEv & _).
        eapply L_bind_intro.
        + eapply Ltr_up with (m1 := M); [lia| |apply LEs; auto|exact F1]. auto.
        + eapply L_bind_intro.
          * eapply Ltr_up with (m1 := M); [lia| |apply LEv; auto|exact A1]. auto.
          * apply H3; lia.
      - (* Dstr *)
        intros s c i IH σ σ' r Ws Wσ R D. simpl in D |- *.
        apply dest_bind_inv in D as (r' & D1 & D2).
        eapply step1_b with (P := fun _ => True) (r' := r'); eauto.
        + intros; apply ds_comm_b.
        + intros; apply leaves_True.
      - (* nv_mt *)
        intros σ σ' r _ _ _ D. simpl in D. inversion D; subst.
        exists 0, 0. intros. reflexivity.
      - (* nv_sh *)
        intros s IH σ σ' r Ws Wσ R D. simpl in D |- *.
        apply dest_bind_inv in D as (r' & D1 & D2).
        eapply step1_b with (P := fun _ => True) (r' := r'); eauto.
        + intros; apply mod_comm_b.
        + intros; apply leaves_True.
      - (* nv_bd *)
        intros x v σ1 IHv IHσ1 σ σ' r [Wv Wσ1] Wσ R D. simpl in D |- *.
        apply dest_bind_inv in D as (v'' & D1 & D2).
        apply dest_bind_inv in D2 as (mσ & D3 & D4).
        destruct (link_nv_leaf _ _ _ _ D3) as (σ1' & ->). simpl in D4.
        inversion D4; subst r; clear D4.
        destruct (IHv σ σ' v'' Wv Wσ R D1) as (n1 & m1 & H1).
        destruct (IHσ1 σ σ' _ Wσ1 Wσ R D3) as (n2 & m2 & H2).
        exists (Nat.max n1 n2), (Nat.max m1 m2). intros n m Hn Hm.
        pose proof (H1 n m ltac:(lia) ltac:(lia)) as E1.
        pose proof (H2 n m ltac:(lia) ltac:(lia)) as E2.
        apply L_split in E1 as (v' & F1 & F2 & _).
        apply L_split in E2 as (w & G1 & G2 & _).
        assert (is_exp w) as Hw
            by (eapply sel_leaf; [apply link_nv_leaves|exact G1]).
        destruct w as [σ2|?|?|?]; simpl in Hw; try tauto.
        eapply L_bind_intro; [exact F1|]. eapply L_bind_intro; [exact G1|].
        simpl. rewrite ?L_Ret. simpl.
        eapply dest_bind_intro; [exact F2|].
        eapply dest_bind_intro; [exact G2|]. reflexivity.
      - (* vl_exp *) intros σ1 IH. exact IH.
      - (* vl_sh *) intros s IH. exact IH.
      - (* vl_clos *)
        intros x b σ1 IH σ σ' r [Wb Wσ1] Wσ R D. simpl in D |- *.
        apply dest_bind_inv in D as (r' & D1 & D2).
        eapply step1_b with (P := is_exp) (r' := r'); eauto.
        + intros; apply clos_comm_b.
        + intros; apply link_nv_leaves.
      - (* vl_cstr *) intros c vs IH σ σ' r. apply IH.
      - (* vnil *)
        intros c σ σ' r _ _ _ D. simpl in D. inversion D; subst.
        exists 0, 0. intros. reflexivity.
      - (* vcons *)
        intros v vs IHv IHvs c σ σ' r [Wv Wvs] Wσ R D. simpl in D |- *.
        apply dest_bind_inv in D as (v'' & D1 & D2).
        apply dest_bind_inv in D2 as (mσ & D3 & D4).
        destruct (link_vls_leaf _ _ _ _ _ D3) as (vs' & -> & _). simpl in D4.
        inversion D4; subst r; clear D4.
        destruct (IHv σ σ' v'' Wv Wσ R D1) as (n1 & m1 & H1).
        destruct (IHvs c σ σ' _ Wvs Wσ R D3) as (n2 & m2 & H2).
        exists (Nat.max n1 n2), (Nat.max m1 m2). intros n m Hn Hm.
        pose proof (H1 n m ltac:(lia) ltac:(lia)) as E1.
        pose proof (H2 n m ltac:(lia) ltac:(lia)) as E2.
        apply L_split in E1 as (v' & F1 & F2 & _).
        apply L_split in E2 as (w & G1 & G2 & _).
        assert (is_cstr c w) as Hw
            by (eapply sel_leaf; [apply link_vls_leaves|exact G1]).
        destruct w as [?|?|?|c1 vs1]; simpl in Hw; try tauto. subst c1.
        eapply L_bind_intro; [exact F1|]. eapply L_bind_intro; [exact G1|].
        simpl. rewrite ?L_Ret. simpl.
        eapply dest_bind_intro; [exact F2|].
        eapply dest_bind_intro; [exact G2|]. reflexivity.
    Qed.

    Definition Pb_tr (t : trace) : Prop := ∀ σ σ' w,
      wf_tr t → wf_nv σ → res σ σ' →
      dest (link_tr (call m') σ' t) = Some w →
      ev2 (fun n m => link_tr (call m) Σ0 (link_tr (call n) σ t)) w.
    Definition Pb_brs (bs : brs) : Prop := ∀ σ σ' w c k,
      wf_brs bs → wf_nv σ → res σ σ' →
      dest (link_sel (call m') σ' c k bs) = Some w →
      ev2 (fun n m => link_sel (call m) Σ0 c k (link_brs (call n) σ bs)) w ∧
      ev2 (fun n m => link_tr (call m) Σ0 (link_sel (call n) σ c k bs)) w.

    Lemma LLb_tr : (∀ t, Pb_tr t) ∧ (∀ bs, Pb_brs bs).
    Proof.
      destruct LLb_vals as (Vs & Vn & Vv & Vvs).
      apply tr_mutind; unfold Pb_tr, Pb_brs.
      - intros σ σ' w _ Wσ R D. simpl in D. discriminate.
      - intros v σ σ' w _ Wσ R D. simpl in D. inversion D; subst.
        exists 0, 0. intros. reflexivity.
      - (* Guard *)
        intros u t IH σ σ' w [Wu Wt] Wσ R D. simpl in D |- *.
        apply dest_bind_inv in D as (u'' & D1 & D2). simpl in D2.
        destruct (Vv u σ σ' u'' Wu Wσ R D1) as (n1 & m1 & H1).
        destruct (IH σ σ' w Wt Wσ R D2) as (n2 & m2 & H2).
        exists (Nat.max n1 n2), (Nat.max m1 m2). intros n m Hn Hm.
        rewrite link_tr_bind.
        pose proof (H1 n m ltac:(lia) ltac:(lia)) as E1.
        apply L_split in E1 as (u' & F1 & F2 & _).
        eapply dest_bind_intro; [exact F1|]. simpl.
        eapply dest_bind_intro; [exact F2|]. simpl. apply H2; lia.
      - (* Match *)
        intros s bs IH σ σ' w [Ws Wb] Wσ R D. simpl in D |- *.
        apply dest_bind_inv in D as (m'' & D1 & D2).
        destruct m'' as [?|?|?|c vs'']; simpl in D2; try discriminate.
        destruct (Vs s σ σ' _ Ws Wσ R D1) as (n1 & m1 & H1).
        destruct (IH σ σ' w c (vlen vs'') Wb Wσ R D2)
          as [(n2 & m2 & H2) (n3 & m3 & H3)].
        exists (Nat.max n1 (Nat.max n2 n3)), (Nat.max m1 (Nat.max m2 m3)).
        intros n m Hn Hm. rewrite link_tr_bind.
        pose proof (H1 n m ltac:(lia) ltac:(lia)) as E1.
        apply L_split in E1 as (mraw & F1 & F2 & _).
        eapply dest_bind_intro; [exact F1|].
        destruct mraw as [σx|s1|?|c1 vs]; simpl in F2 |- *.
        + destruct (link_nv_leaf _ _ _ _ F2) as (? & E). discriminate.
        + eapply dest_bind_intro; [exact F2|]. simpl. apply H2; lia.
        + apply dest_bind_inv in F2 as (mσ & _ & F2).
          destruct mσ; simpl in F2; discriminate.
        + destruct (link_vls_leaf _ _ _ _ _ F2) as (vs1 & E & Hlen).
          inversion E; subst c1 vs1; clear E.
          eapply dest_bind_intro; [exact F2|]. simpl.
          rewrite <- Hlen. apply H3; lia.
      - intros σ σ' w c k _ Wσ R D. simpl in D. discriminate.
      - intros c0 n0 t bs IHt IHb σ σ' w c k [Wt Wb] Wσ R. simpl.
        destruct (String.eqb c c0 && Nat.eqb k n0); intros D.
        + pose proof (IHt σ σ' w Wt Wσ R D) as E. split; exact E.
        + exact (IHb σ σ' w c k Wb Wσ R D).
    Qed.

    Lemma LLb_trace t σ σ' r (Wt : wf_tr t) (Wσ : wf_nv σ) (R : res σ σ')
      (D : dest (link_trace (call m') σ' t) = Some r) :
      ev2 (fun n m => L m (link_trace (call n) σ t)) r.
    Proof.
      destruct LLb_vals as (Vs & Vn & Vv & Vvs). destruct LLb_tr as [Vt _].
      unfold link_trace in D. apply dest_bind_inv in D as (w & D1 & D2).
      assert (wf_vl w) as Ww.
      { eapply wf_dest; [|exact D1]. apply wf_link_tr; auto.
        eapply wf_res; eauto. }
      destruct (Vt t σ σ' w Wt Wσ R D1) as (n1 & m1 & H1).
      destruct (Vv w σ σ' r Ww Wσ R D2) as (n2 & m2 & H2).
      exists (Nat.max n1 n2), (Nat.max m1 m2). intros n m Hn Hm.
      unfold link_trace at 2.
      eapply L_bind_intro; [apply H1; lia|apply H2; lia].
    Qed.
  End b.

  Lemma LLb_call m' : ∀ σc b σc' r, wf_nv σc → wfb b → res σc σc' →
    dest (linkb m' σc' b) = Some r →
    ev2 (fun n m => L m (linkb n σc b)) r.
  Proof.
    induction m'; intros σc b σc' r Wσ Wb R D.
    - rewrite linkb_0 in D. discriminate.
    - destruct Wb as [e ->]. rewrite linkb_S in D.
      destruct (LLb_trace m' IHm' (den e m') σc σc' r (wf_den m' e) Wσ R D)
        as (n0 & m0 & H).
      exists (S (Nat.max n0 m')), m0. intros n m Hn Hm.
      destruct n as [|n]; [lia|]. rewrite linkb_S.
      eapply L_up with (m1 := m); [lia| | |apply (H n m); lia].
      + apply wf_link_trace; auto. apply wf_den.
      + apply le_link_trace; auto.
        * intros; apply le_refl.
        * apply wf_den.
        * apply le_den. lia.
  Qed.

  Lemma call_b n0 σ σ' b r (Wσ : wf_nv σ) (Wb : wfb b) (R : res σ σ')
    (D : dest (linkb n0 σ' b) = Some r) :
    ev2 (fun n m => L m (call n σ b)) r.
  Proof.
    destruct (LLb_call n0 σ b σ' r Wσ Wb R D) as (n1 & m1 & H).
    destruct R as (m2 & R). exists n1, (Nat.max m1 m2). intros n m Hn Hm.
    rewrite call_eq. eapply L_guard_intro; [|apply H; lia].
    simpl. rewrite (up_nv m2 m ltac:(lia) Σ0 HΣ0 σ _ Wσ R). exact R.
  Qed.

  Lemma LLa_call n : ∀ σc b σc' m r, wf_nv σc → wfb b → res σc σc' →
    dest (L m (linkb n σc b)) = Some r →
    evc (fun m2 => linkb m2 σc' b) r (cost (L m (linkb n σc b))).
  Proof.
    induction n; intros σc b σc' m r Wσ Wb R D.
    - rewrite linkb_0 in D. discriminate.
    - destruct Wb as [e ->]. rewrite linkb_S in D |- *.
      pose proof (LLa_trace n IHn (den e n) σc σc' m r (wf_den n e) Wσ R D) as E.
      destruct E as (m0 & E). exists (S (Nat.max m0 n)). intros m2 Hm2.
      destruct m2 as [|m2]; [lia|]. rewrite linkb_S.
      destruct (E (Nat.max m0 n) ltac:(lia)) as [D' C'].
      assert (link_trace (call m2) σc' (den e m2) =
              link_trace (call (Nat.max m0 n)) σc' (den e n)) as EQ.
      { eapply up_trace with (r := r); eauto; try lia.
        - eapply wf_res; eauto.
        - apply wf_den.
        - apply le_den. lia. }
      rewrite EQ. auto.
  Qed.

  (** Linking [Σ0] into a call that the inner link already made is the same
      as making the call in the resolved environment, and costs strictly
      more guards. *)
  Lemma call_a n σ b m r (Wσ : wf_nv σ) (Wb : wfb b)
    (D : dest (L m (call n σ b)) = Some r) :
    ∃ σ', dest (link_nv (call m) Σ0 σ) = Some (vl_exp σ') ∧
          evc (fun m2 => linkb m2 σ' b) r (cost (L m (linkb n σ b))) ∧
          cost (L m (call n σ b)) =
          cost (link_nv (call m) Σ0 σ) + S (cost (L m (linkb n σ b))).
  Proof.
    rewrite call_eq in *. apply L_guard in D as (u' & D1 & D2 & C).
    simpl in D1. destruct (link_nv_leaf _ _ _ _ D1) as (σ' & ->).
    assert (res σ σ') as R by (exists m; auto).
    exists σ'. repeat split; auto. apply LLa_call; auto.
  Qed.

  Lemma ap_a m n f a r (Wf : wf_vl f) (Wa : wf_vl a)
    (D : dest (L m (ap (call n) f a)) = Some r) :
    ∃ f' a' c',
      dest (link_vl (call m) Σ0 f) = Some f' ∧
      dest (link_vl (call m) Σ0 a) = Some a' ∧
      evc (fun m2 => ap (call m2) f' a') r c' ∧
      cost (link_vl (call m) Σ0 f) + cost (link_vl (call m) Σ0 a) + c'
        ≤ cost (L m (ap (call n) f a)).
  Proof. eapply ap_comm; eauto. apply LLa_call. Qed.

  Lemma ap_b m' f a f' a' r m1 (Wf : wf_vl f) (Wa : wf_vl a)
    (D1 : dest (link_vl (call m1) Σ0 f) = Some f')
    (D2 : dest (link_vl (call m1) Σ0 a) = Some a')
    (D : dest (ap (call m') f' a') = Some r) :
    ev2 (fun n m => L m (ap (call n) f a)) r.
  Proof. eapply ap_comm_b; eauto. apply LLb_call. Qed.

End LL.
