(** * Linking and the renaming of anchors

    This file proves that linking moves through a renaming of the free
    anchors, as an equation between traces. The renaming must keep the dead
    anchor. Thus the name that opens a recursive value, or that a binding
    runs with, can be each fresh name. [Subst.v], [LinkLink.v] and
    [Adequacy.v] use these equations to select one name that is fresh for
    each object of a proof.

    ** Main results

    - [kill_close_eq]: the names of 2 anchors that leave their scope do not
      matter.
    - [eq_link], [eq_link_tr], [eq_link_trace]: linking moves through a
      renaming.
    - [eq_linkb], [eq_linkv], [eq_call]: the same at each fuel.
    - [link_mu], [linkn_mu]: linking into a recursive value can open it with
      each fresh anchor.
    - [link_tr_killg], [linkn_tr_killg]: linking into a spine moves through
      the kill of an anchor that is fresh for the environment.
    - [denote_bind]: the trace of a binding can use each anchor but the dead
      anchor. *)
From Stdlib Require Import Utf8 String Bool Arith Lia List.
From Denot Require Import Syntax Anchor Domain Nominal Semantics Laws Wf Fresh.
Set Warnings "-notation-for-abbreviation".

(** ** Tools *)

(** [tall] moves through a universal quantifier. *)
Lemma tall_forall_mut {A} (Pg : A → vl → Prop) (Ps : A → shdw → Prop)
  (Pl : A → vl → Prop) :
  (∀ t, (∀ a, tall (Pg a) (Ps a) (Pl a) t) →
        tall (fun u => ∀ a, Pg a u) (fun s => ∀ a, Ps a s) (fun v => ∀ a, Pl a v) t) ∧
  (∀ bs, (∀ a, tall_brs (Pg a) (Ps a) (Pl a) bs) →
         tall_brs (fun u => ∀ a, Pg a u) (fun s => ∀ a, Ps a s)
           (fun v => ∀ a, Pl a v) bs).
Proof.
  apply tr_mutind; simpl; auto.
  - intros u t IH H. split; [intros a; apply (H a)|apply IH; intros a; apply (H a)].
  - intros s bs IH H. split; [intros a; apply (H a)|apply IH; intros a; apply (H a)].
  - intros c n t bs IHt IHb H.
    split; [apply IHt; intros a; apply (H a)|apply IHb; intros a; apply (H a)].
Qed.

(** [tall] moves through an implication. *)
Lemma tall_imp_mut (Q : Prop) (Pg : vl → Prop) (Ps : shdw → Prop) (Pl : vl → Prop) :
  (∀ t, (Q → tall Pg Ps Pl t) →
        tall (fun u => Q → Pg u) (fun s => Q → Ps s) (fun v => Q → Pl v) t) ∧
  (∀ bs, (Q → tall_brs Pg Ps Pl bs) →
         tall_brs (fun u => Q → Pg u) (fun s => Q → Ps s) (fun v => Q → Pl v) bs).
Proof.
  apply tr_mutind; simpl; auto.
  - intros u t IH H. split; [intros q; apply (H q)|apply IH; intros q; apply (H q)].
  - intros s bs IH H. split; [intros q; apply (H q)|apply IH; intros q; apply (H q)].
  - intros c n t bs IHt IHb H.
    split; [apply IHt; intros q; apply (H q)|apply IHb; intros q; apply (H q)].
Qed.

(** Assume that each anchor of [R] is fresh for the trace [t]. Then each
    anchor of [R] is fresh for each value of [t]. *)
Lemma nft_forall (R : loc → Prop) t (H : ∀ y, R y → nft y t) :
  tall (fun u => ∀ y, R y → nf_vl y u) (fun s => ∀ y, R y → nf_shdw y s)
       (fun v => ∀ y, R y → nf_vl y v) t.
Proof.
  apply (proj1 (tall_forall_mut
    (fun y u => R y → nf_vl y u) (fun y s => R y → nf_shdw y s)
    (fun y v => R y → nf_vl y v))).
  intros y. apply (proj1 (tall_imp_mut (R y) _ _ _)). auto.
Qed.

(** The mutual form of [bind_tmap_ext]. *)
Lemma bind_tmap_ext_mut k k' g gs h g' gs' h' :
  (∀ t, tall (fun u => g u = g' u) (fun s => gs s = gs' s)
          (fun v => k (h v) = k' (h' v)) t →
        bind k (tmap g gs h t) = bind k' (tmap g' gs' h' t)) ∧
  (∀ bs, tall_brs (fun u => g u = g' u) (fun s => gs s = gs' s)
           (fun v => k (h v) = k' (h' v)) bs →
         bind_brs k (tmap_brs g gs h bs) = bind_brs k' (tmap_brs g' gs' h' bs)).
Proof.
  apply tr_mutind; simpl; auto.
  - intros u t IH [-> H]. f_equal; auto.
  - intros s bs IH [-> H]. f_equal; auto.
  - intros c n t bs IHt IHb [Ht Hb]. f_equal; auto.
Qed.

(** [bind] after [tmap] gives the same trace for 2 maps and 2 continuations
    that agree on the values of the trace. *)
Lemma bind_tmap_ext k k' g gs h g' gs' h' t :
  tall (fun u => g u = g' u) (fun s => gs s = gs' s)
    (fun v => k (h v) = k' (h' v)) t →
  bind k (tmap g gs h t) = bind k' (tmap g' gs' h' t).
Proof. apply bind_tmap_ext_mut. Qed.

(** A renaming that keeps the dead anchor does not change a value whose only
    free anchor is the dead anchor. *)
Lemma ren_closed ξ v (Z : ξ 0 = 0) (H : ∀ y, y ≠ 0 → nf_vl y v) : ren_vl ξ v = v.
Proof.
  rewrite <- (ren_id v 0) at 2. apply ren_ext_nf.
  intros y NE. apply H. intros ->. congruence.
Qed.

(** A renaming that keeps the dead anchor does not change a trace whose only
    free anchor is the dead anchor. *)
Lemma ren_tr_closed ξ t (Z : ξ 0 = 0) (H : ∀ y, y ≠ 0 → nft y t) : ren_tr ξ t = t.
Proof.
  rewrite <- (tmap_id t) at 2. unfold ren_tr. apply tmap_ext.
  eapply tall_impl; [| | |apply (nft_forall (fun y => y ≠ 0) t H)]; simpl.
  - intros u Hu. apply ren_closed; auto.
  - intros s Hs. apply vl_sh_inj. apply (ren_closed ξ (vl_sh s)); auto.
  - intros v Hv. apply ren_closed; auto.
Qed.

(** The trivial predicates hold of each value of a trace. *)
Lemma tall_True_mut :
  (∀ t, tall (fun _ => True) (fun _ => True) (fun _ => True) t) ∧
  (∀ bs, tall_brs (fun _ => True) (fun _ => True) (fun _ => True) bs).
Proof. apply tr_mutind; simpl; auto. Qed.

(** The identity renaming does not change a trace. *)
Lemma ren_tr_id t : ren_tr (fun x => x) t = t.
Proof.
  rewrite <- (tmap_id t) at 2. unfold ren_tr. apply tmap_ext.
  eapply tall_impl; [| | |apply (proj1 tall_True_mut t)]; simpl.
  - intros u _. apply ren_id.
  - intros s _. apply vl_sh_inj. apply (ren_id (vl_sh s)).
  - intros v _. apply ren_id.
Qed.

(** A renaming moves through [bind], when the 2 continuations agree up to the
    renaming. *)
Lemma ren_tr_bind ξ k k' t (W : wf_tr t)
  (H : ∀ v, wf_vl v → k' (ren_vl ξ v) = ren_tr ξ (k v)) :
  bind k' (ren_tr ξ t) = ren_tr ξ (bind k t).
Proof.
  unfold ren_tr. rewrite tmap_bind, bind_tmap.
  eapply bind_ext_tall with (Pg := fun _ => True) (Ps := fun _ => True)
    (Pl := wfk_vl 0); [exact H|].
  apply tall_tmap. eapply tall_impl; [| | |apply wf_tall; exact W]; simpl; auto.
Qed.

(** ** An anchor that leaves its scope *)

(** The anchor [ℓ2] of the trace [T2] leaves its scope. That is, the spine
    kills it and the continuation closes it. Rename [T2] with [ξ] and with
    [ℓ2] to [ℓ1], then let [ℓ1] leave its scope. The result is the
    [ξ]-renaming of the first trace. The condition is that [ξ] takes no other
    anchor of [T2] to [ℓ1]. *)
Lemma kill_close_eq ξ ℓ1 ℓ2 T2 k1 k2
  (Z : ξ 0 = 0) (Z1 : ℓ1 ≠ 0) (W : wf_tr T2)
  (HN : ∀ y, ξ y = ℓ1 ∧ y ≠ ℓ2 → nft y T2)
  (Hk : ∀ w, wfk_vl 1 w → k1 (am_vl (fren ξ) 1 w) = ren_tr ξ (k2 w)) :
  bind (fun w' => k1 (close_vl 0 ℓ1 w'))
    (killg ℓ1 (ren_tr (fun y => if Nat.eqb y ℓ2 then ℓ1 else ξ y) T2)) =
  ren_tr ξ (bind (fun w' => k2 (close_vl 0 ℓ2 w')) (killg ℓ2 T2)).
Proof.
  set (ξ' := fun y => if Nat.eqb y ℓ2 then ℓ1 else ξ y).
  assert (ξ' ℓ2 = ℓ1) as E2 by (unfold ξ'; rewrite Nat.eqb_refl; reflexivity).
  assert (∀ y, y ≠ ℓ2 → ξ' y = ξ y) as Eo.
  { intros y NE. unfold ξ'. apply Nat.eqb_neq in NE. rewrite NE. reflexivity. }
  (* The guards and the scrutinees. *)
  assert (∀ u, (∀ y, ξ y = ℓ1 ∧ y ≠ ℓ2 → nf_vl y u) →
     am_vl (fren (kap ℓ1)) 0 (am_vl (fren ξ') 0 u) =
     am_vl (fren ξ) 0 (am_vl (fren (kap ℓ2)) 0 u)) as HG.
  { intros u Hu. rewrite !ren_ren. apply ren_ext_nf. intros y NE. apply Hu.
    destruct (Nat.eq_dec y ℓ2) as [->|NE2].
    - exfalso. apply NE. rewrite E2, !kap_self. auto.
    - split; auto. rewrite (Eo y NE2), (kap_fix ℓ2 y NE2) in NE.
      destruct (Nat.eq_dec (ξ y) ℓ1) as [E|NE1]; auto.
      exfalso. apply NE. apply kap_fix. auto. }
  (* The leaves. *)
  assert (∀ v, wf_vl v → (∀ y, ξ y = ℓ1 ∧ y ≠ ℓ2 → nf_vl y v) →
     close_vl 0 ℓ1 (am_vl (fren ξ') 0 v) = am_vl (fren ξ) 1 (close_vl 0 ℓ2 v)) as HL.
  { intros v Wv Hv.
    rewrite (ren_k ξ _ 1 0).
    rewrite <- (ren_ext_nf ξ' ξ (close_vl 0 ℓ2 v)).
    - rewrite ren_close, E2; auto.
      eapply aan_impl; [|apply (nf_all _ _ Hv)].
      intros a Ha y -> NE2 E. apply (Ha y eq_refl). split; auto.
      rewrite E2, (Eo y NE2) in E. exact E.
    - intros y NE. destruct (Nat.eq_dec y ℓ2) as [->|NE2].
      + apply nf_close_self.
      + exfalso. apply NE. apply Eo. auto. }
  unfold killg. unfold ren_tr at 1 2. rewrite tmap_tmap.
  rewrite tmap_bind, tmap_tmap.
  apply bind_tmap_ext.
  eapply tall_impl; [| | |apply tall_wf; [exact W|apply (nft_forall _ _ HN)]];
    simpl.
  - intros u [_ Hu]. apply HG; auto.
  - intros s [_ Hs]. apply vl_sh_inj. apply (HG (vl_sh s)); auto.
  - intros v [Wv Hv]. rewrite HL; auto. apply Hk. apply wf_close; auto.
Qed.

Section eq_link.
  Context (cl : nv → body → trace) (lk : nv → vl → trace).
  Context (Wcl : ∀ σ b, wf_nv σ → wfb b → wf_tr (cl σ b)).
  Context (Wlk : ∀ σ v, wf_nv σ → wf_vl v → wf_tr (lk σ v)).
  Context (Ecl : ∀ ξ σ b, ξ 0 = 0 → wf_nv σ → wfb b →
    cl (ren_nv ξ σ) b = ren_tr ξ (cl σ b)).
  Context (Elk : ∀ ξ σ v, ξ 0 = 0 → wf_nv σ → wf_vl v →
    lk (ren_nv ξ σ) (ren_vl ξ v) = ren_tr ξ (lk σ v)).
  Context (Nlk : ∀ x σ v, x ≠ 0 → wf_nv σ → wf_vl v → nf_nv x σ → nf_vl x v →
    nft x (lk σ v)).

  (** ** Linking moves through a renaming *)

  (** [ap] moves through a renaming. *)
  Lemma ap_ren ξ f a (Z : ξ 0 = 0) (Wf : wf_vl f) (Wa : wf_vl a) :
    ap cl (ren_vl ξ f) (ren_vl ξ a) = ren_tr ξ (ap cl f a).
  Proof.
    destruct f; simpl in *; auto. destruct Wf.
    apply (Ecl ξ (nv_bd x a σ) b); simpl; auto.
  Qed.

  (** A read moves through a renaming. *)
  Lemma rd_ren ξ x m : rd x (ren_vl ξ m) = ren_tr ξ (rd x m).
  Proof.
    unfold rd. destruct m; simpl; auto.
    change (am_nv (fren ξ) 0 σ) with (ren_nv ξ σ). rewrite read_ren.
    destruct (read x σ); simpl; auto.
  Qed.

  (** A field moves through a renaming. *)
  Lemma ds_ren ξ c i m : ds c i (ren_vl ξ m) = ren_tr ξ (ds c i m).
  Proof.
    unfold ds. destruct m; simpl; auto.
    destruct (String.eqb c c0); auto. rewrite vnth_am.
    destruct (vnth i vs); simpl; auto.
  Qed.

  (** The case of a recursive value in [eq_link]. The 2 sides can open the
      recursive value with different fresh anchors [ℓ1] and [ℓ2]. *)
  Lemma mu_eq ξ σ0 σ1 w w1 ℓ1 ℓ2 k1 k2 (Z : ξ 0 = 0) (Wσ0 : wf_nv σ0) (Ww : wfk_vl 1 w)
    (Eσ1 : σ1 = ren_nv ξ σ0) (Ew1 : w1 = am_vl (fren ξ) 1 w)
    (Z1 : ℓ1 ≠ 0) (N1σ : nf_nv ℓ1 σ1) (N1w : nf_vl ℓ1 w1)
    (Z2 : ℓ2 ≠ 0) (N2σ : nf_nv ℓ2 σ0) (N2w : nf_vl ℓ2 w)
    (Hk : ∀ u, wfk_vl 1 u → k1 (am_vl (fren ξ) 1 u) = ren_tr ξ (k2 u)) :
    bind (fun w' => k1 (close_vl 0 ℓ1 w')) (killg ℓ1 (lk σ1 (open_vl 0 ℓ1 w1))) =
    ren_tr ξ (bind (fun w' => k2 (close_vl 0 ℓ2 w'))
                (killg ℓ2 (lk σ0 (open_vl 0 ℓ2 w)))).
  Proof.
    subst σ1 w1.
    set (ξ' := fun y => if Nat.eqb y ℓ2 then ℓ1 else ξ y).
    assert (ξ' 0 = 0) as Z'.
    { unfold ξ'. destruct (Nat.eqb 0 ℓ2) eqn:E; auto.
      apply Nat.eqb_eq in E. congruence. }
    assert (ξ' ℓ2 = ℓ1) as E2 by (unfold ξ'; rewrite Nat.eqb_refl; reflexivity).
    assert (∀ y, ξ' y ≠ ξ y → y = ℓ2) as Eo.
    { intros y NE. unfold ξ' in NE. destruct (Nat.eqb y ℓ2) eqn:E.
      - apply Nat.eqb_eq in E. auto.
      - congruence. }
    assert (wf_vl (open_vl 0 ℓ2 w)) as Wo by (apply wf_open; auto).
    assert (ren_nv ξ σ0 = ren_nv ξ' σ0) as Eσ.
    { apply vl_exp_inj. symmetry. apply (ren_ext_nf ξ' ξ (vl_exp σ0)).
      intros y NE. rewrite (Eo y NE). exact N2σ. }
    assert (open_vl 0 ℓ1 (am_vl (fren ξ) 1 w) = ren_vl ξ' (open_vl 0 ℓ2 w)) as Ew.
    { rewrite ren_open, E2. f_equal. rewrite (ren_k ξ w 1 0). symmetry.
      apply ren_ext_nf. intros y NE. rewrite (Eo y NE). exact N2w. }
    rewrite Ew, Eσ, (Elk ξ' σ0 _ Z' Wσ0 Wo).
    apply kill_close_eq; auto.
    intros y [E NE]. apply Nlk; auto.
    - intros ->. congruence.
    - apply (nf_ren_inv ξ y (vl_exp σ0) 0). rewrite E. exact N1σ.
    - apply nf_open; auto. apply (nf_ren_inv ξ y w 1). rewrite E. exact N1w.
  Qed.

  Section fixed.
    Context (ξ : loc → loc) (Z : ξ 0 = 0) (σ0 : nv) (Wσ0 : wf_nv σ0).
    Local Notation σ1 := (ren_nv ξ σ0) (only parsing).

    (** Linking the renamed environment into the renamed value gives the
        renamed trace. *)
    Lemma eq_link :
      (∀ s, wf_shdw s →
         link_shdw cl lk σ1 (ren_shdw ξ s) = ren_tr ξ (link_shdw cl lk σ0 s)) ∧
      (∀ σ, wf_nv σ →
         link_nv cl lk σ1 (ren_nv ξ σ) = ren_tr ξ (link_nv cl lk σ0 σ)) ∧
      (∀ v, wf_vl v →
         link_vl cl lk σ1 (ren_vl ξ v) = ren_tr ξ (link_vl cl lk σ0 v)) ∧
      (∀ vs, wf_vls vs → ∀ c,
         link_vls cl lk σ1 c (ren_vls ξ vs) = ren_tr ξ (link_vls cl lk σ0 c vs)).
    Proof.
      destruct (wf_link cl lk Wcl Wlk σ0 Wσ0) as (Ws & Wn & Wv & Wvs).
      apply val_mutind; simpl.
      - auto.
      - intros s x IH W. rewrite IH; auto. apply ren_tr_bind; auto.
        intros; apply rd_ren.
      - intros s v IHs IHv [W1 W2]. rewrite IHs, IHv; auto.
        apply ren_tr_bind; auto. intros f Wf. apply ren_tr_bind; auto.
        intros a Wa. apply ap_ren; auto.
      - intros s c i IH W. rewrite IH; auto. apply ren_tr_bind; auto.
        intros; apply ds_ren.
      - auto.
      - intros s IH W. rewrite IH; auto. apply ren_tr_bind; auto.
        intros m Wm. destruct m; reflexivity.
      - intros x v σ IHv IHσ [W1 W2]. rewrite IHv, IHσ; auto.
        apply ren_tr_bind; auto. intros v' Wv'. apply ren_tr_bind; auto.
        intros m Wm. destruct m; reflexivity.
      - (* The case of a recursive value. *)
        intros x w σ _ IHσ [W1 W2]. rewrite IHσ; auto.
        apply (mu_eq ξ σ0 _ w _ _ _
          (fun u => bind (on_env (fun σ'' => Ret (vl_exp (nv_bd x (wvl_mu u) σ''))))
                      (ren_tr ξ (link_nv cl lk σ0 σ)))
          (fun u => bind (on_env (fun σ'' => Ret (vl_exp (nv_bd x (wvl_mu u) σ''))))
                      (link_nv cl lk σ0 σ))); auto.
        + apply fresh_pos.
        + apply fresh_nv.
        + apply fresh_vl.
        + apply fresh_pos.
        + apply fresh_nv.
        + apply fresh_vl.
        + intros u Wu. apply ren_tr_bind; auto.
          intros m Wm. destruct m; reflexivity.
      - intros x a σ IH [W1 W2]. rewrite IH; auto. apply ren_tr_bind; auto.
        intros m Wm. destruct m; reflexivity.
      - auto.
      - auto.
      - intros x b σ IH [W1 W2]. rewrite IH; auto. apply ren_tr_bind; auto.
        intros m Wm. destruct m; reflexivity.
      - auto.
      - auto.
      - intros v vs IHv IHvs [W1 W2] c. rewrite IHv, IHvs; auto.
        apply ren_tr_bind; auto. intros v' Wv'. apply ren_tr_bind; auto.
        intros m Wm. destruct m; reflexivity.
    Qed.

    (** Linking the renamed environment into the spine of the renamed trace
        gives the renamed trace. *)
    Lemma eq_link_tr :
      (∀ t, wf_tr t →
         link_tr cl lk σ1 (ren_tr ξ t) = ren_tr ξ (link_tr cl lk σ0 t)) ∧
      (∀ bs, wf_brs bs →
         link_brs cl lk σ1 (tmap_brs (ren_vl ξ) (ren_shdw ξ) (ren_vl ξ) bs) =
         tmap_brs (ren_vl ξ) (ren_shdw ξ) (ren_vl ξ) (link_brs cl lk σ0 bs) ∧
         ∀ c n, link_sel cl lk σ1 c n
                  (tmap_brs (ren_vl ξ) (ren_shdw ξ) (ren_vl ξ) bs) =
                ren_tr ξ (link_sel cl lk σ0 c n bs)).
    Proof.
      destruct (wf_link cl lk Wcl Wlk σ0 Wσ0) as (Ws & Wn & Wv & Wvs).
      destruct eq_link as (Es & En & Ev & Evs).
      apply tr_mutind; simpl.
      - auto.
      - auto.
      - intros u t IH [W1 W2]. rewrite Ev; auto. apply ren_tr_bind; auto.
        intros u' Wu'. simpl. unfold ren_tr in IH. rewrite IH; auto.
      - intros s bs IH [W1 W2]. destruct (IH W2) as [IH1 IH2].
        rewrite Es; auto. apply ren_tr_bind; auto.
        intros m Wm. destruct m; simpl; auto.
        + rewrite IH1. reflexivity.
        + rewrite vlen_am, IH2. reflexivity.
      - auto.
      - intros c n t bs IHt IHb [W1 W2]. destruct (IHb W2) as [IH1 IH2].
        unfold ren_tr in IHt. split.
        + rewrite IHt, IH1; auto.
        + intros c' n'. destruct (_ && _); auto.
    Qed.

    (** Linking the renamed environment into the renamed trace gives the
        renamed trace. *)
    Lemma eq_link_trace t (W : wf_tr t) :
      link_trace cl lk σ1 (ren_tr ξ t) = ren_tr ξ (link_trace cl lk σ0 t).
    Proof.
      unfold link_trace. rewrite (proj1 eq_link_tr); auto.
      apply ren_tr_bind.
      - apply wf_link_tr; auto.
      - intros. apply eq_link; auto.
    Qed.
  End fixed.

  (** Linking into a recursive value can open it with each fresh anchor. The
      anchor must be fresh for the environment and for the value, and it must
      not be the dead anchor. *)
  Lemma link_mu σ0 x w σ ℓ (Wσ0 : wf_nv σ0) (Ww : wfk_vl 1 w)
    (NZ : ℓ ≠ 0) (Nσ : nf_nv ℓ σ0) (Nw : nf_vl ℓ w) :
    link_nv cl lk σ0 (nv_bd x (wvl_mu w) σ) =
    bind (fun w' =>
      bind (on_env (fun σ'' => Ret (vl_exp (nv_bd x (wvl_mu (close_vl 0 ℓ w')) σ''))))
        (link_nv cl lk σ0 σ))
      (killg ℓ (lk σ0 (open_vl 0 ℓ w))).
  Proof.
    simpl.
    rewrite <- (ren_tr_id (bind _ (killg (fresh σ0 w) _))). symmetry.
    apply (mu_eq (fun y => y) σ0 σ0 w w ℓ (fresh σ0 w)
      (fun u => bind (on_env (fun σ'' => Ret (vl_exp (nv_bd x (wvl_mu u) σ''))))
                  (link_nv cl lk σ0 σ))
      (fun u => bind (on_env (fun σ'' => Ret (vl_exp (nv_bd x (wvl_mu u) σ''))))
                  (link_nv cl lk σ0 σ))); auto.
    - symmetry. apply vl_exp_inj. apply (ren_id (vl_exp σ0)).
    - symmetry. apply ren_id.
    - apply fresh_pos.
    - apply fresh_nv.
    - apply fresh_vl.
    - intros u Wu. rewrite ren_tr_id, ren_id. reflexivity.
  Qed.

  (** Linking into a spine moves through the kill of an anchor that is fresh
      for the environment. *)
  Lemma link_tr_killg σ0 ℓ (Wσ0 : wf_nv σ0) (Nσ : nf_nv ℓ σ0) :
    (∀ t, wf_tr t → link_tr cl lk σ0 (killg ℓ t) = killg ℓ (link_tr cl lk σ0 t)) ∧
    (∀ bs, wf_brs bs →
       link_brs cl lk σ0 (tmap_brs (ren_vl (kap ℓ)) (ren_shdw (kap ℓ)) (fun v => v) bs) =
       tmap_brs (ren_vl (kap ℓ)) (ren_shdw (kap ℓ)) (fun v => v) (link_brs cl lk σ0 bs) ∧
       ∀ c n, link_sel cl lk σ0 c n
                (tmap_brs (ren_vl (kap ℓ)) (ren_shdw (kap ℓ)) (fun v => v) bs) =
              killg ℓ (link_sel cl lk σ0 c n bs)).
  Proof.
    destruct (wf_link cl lk Wcl Wlk σ0 Wσ0) as (Ws & Wn & Wv & Wvs).
    assert (ren_nv (kap ℓ) σ0 = σ0) as E.
    { apply vl_exp_inj.
      transitivity (am_vl (fren (fun x => x)) 0 (vl_exp σ0)); [|apply ren_id].
      apply (ren_ext_nf (kap ℓ) (fun x => x) (vl_exp σ0)).
      intros y NE. destruct (Nat.eq_dec y ℓ) as [->|NE'].
      - exact Nσ.
      - exfalso. apply NE. apply kap_fix; auto. }
    destruct (eq_link (kap ℓ) (kap_0 ℓ) σ0 Wσ0) as (Es & En & Ev & Evs).
    rewrite E in Es, Ev.
    unfold killg. apply tr_mutind; simpl.
    - auto.
    - auto.
    - intros u t IH [W1 W2]. rewrite Ev; auto.
      unfold ren_tr. rewrite bind_tmap, tmap_bind. simpl.
      apply bind_ext. intros u'. rewrite IH; auto.
    - intros s bs IH [W1 W2]. destruct (IH W2) as [IH1 IH2]. rewrite Es; auto.
      unfold ren_tr. rewrite bind_tmap, tmap_bind.
      apply bind_ext. intros m. destruct m; simpl; auto.
      + rewrite IH1. reflexivity.
      + rewrite vlen_am, IH2. reflexivity.
    - auto.
    - intros c n t bs IHt IHb [W1 W2]. destruct (IHb W2) as [IH1 IH2]. split.
      + rewrite IHt, IH1; auto.
      + intros c' n'. destruct (_ && _); auto.
  Qed.
End eq_link.

(** ** At each fuel *)

(** [linkb n] and [linkv n] move through a renaming, by induction on the
    fuel. *)
Lemma eq_linkbv n :
  (∀ ξ σ b, ξ 0 = 0 → wf_nv σ → wfb b →
     linkb n (ren_nv ξ σ) b = ren_tr ξ (linkb n σ b)) ∧
  (∀ ξ σ v, ξ 0 = 0 → wf_nv σ → wf_vl v →
     linkv n (ren_nv ξ σ) (ren_vl ξ v) = ren_tr ξ (linkv n σ v)).
Proof.
  induction n as [|n [IHb IHv]].
  - split; intros; rewrite ?linkb_0, ?linkv_0; reflexivity.
  - assert (∀ σ b, wf_nv σ → wfb b → wf_tr (call n σ b)) as Wcl
        by (intros; apply wf_call; auto).
    assert (∀ σ v, wf_nv σ → wf_vl v → wf_tr (linkv n σ v)) as Wlk
        by (intros; apply wf_linkv; auto).
    assert (∀ ξ σ b, ξ 0 = 0 → wf_nv σ → wfb b →
              call n (ren_nv ξ σ) b = ren_tr ξ (call n σ b)) as Ecl.
    { intros. rewrite !call_eq. simpl. rewrite IHb; auto. }
    assert (∀ x σ v, x ≠ 0 → wf_nv σ → wf_vl v → nf_nv x σ → nf_vl x v →
              nft x (linkv n σ v)) as Nlk
        by (intros; apply nf_linkv; auto).
    split.
    + intros ξ σ b Z Wσ [e ->]. rewrite !linkb_S.
      rewrite <- (ren_tr_closed ξ (den e n) Z) at 1.
      * apply eq_link_trace; auto. apply wf_den.
      * intros y NZ. apply nf_den; auto.
    + intros ξ σ v Z Wσ Wv. rewrite !linkv_S. apply eq_link; auto.
Qed.

(** [linkb] moves through a renaming of the environment. *)
Lemma eq_linkb n ξ σ b : ξ 0 = 0 → wf_nv σ → wfb b →
  linkb n (ren_nv ξ σ) b = ren_tr ξ (linkb n σ b).
Proof. apply eq_linkbv. Qed.

(** [linkv] moves through a renaming of the environment and the value. *)
Lemma eq_linkv n ξ σ v : ξ 0 = 0 → wf_nv σ → wf_vl v →
  linkv n (ren_nv ξ σ) (ren_vl ξ v) = ren_tr ξ (linkv n σ v).
Proof. apply eq_linkbv. Qed.

(** [call] moves through a renaming of the environment. *)
Lemma eq_call n ξ σ b : ξ 0 = 0 → wf_nv σ → wfb b →
  call n (ren_nv ξ σ) b = ren_tr ξ (call n σ b).
Proof. intros. rewrite !call_eq. simpl. rewrite eq_linkb; auto. Qed.

(** [link_mu] at the fuel [n]. *)
Lemma linkn_mu n σ0 x w σ ℓ (Wσ0 : wf_nv σ0) (Ww : wfk_vl 1 w)
  (NZ : ℓ ≠ 0) (Nσ : nf_nv ℓ σ0) (Nw : nf_vl ℓ w) :
  link_nv (call n) (linkv n) σ0 (nv_bd x (wvl_mu w) σ) =
  bind (fun w' =>
    bind (on_env (fun σ'' => Ret (vl_exp (nv_bd x (wvl_mu (close_vl 0 ℓ w')) σ''))))
      (link_nv (call n) (linkv n) σ0 σ))
    (killg ℓ (linkv n σ0 (open_vl 0 ℓ w))).
Proof.
  apply link_mu; auto.
  - intros; apply wf_linkv; auto.
  - intros; apply eq_linkv; auto.
  - intros; apply nf_linkv; auto.
Qed.

(** [link_tr_killg] at the fuel [n]. *)
Lemma linkn_tr_killg n σ0 ℓ t (Wσ0 : wf_nv σ0) (Nσ : nf_nv ℓ σ0) (W : wf_tr t) :
  link_tr (call n) (linkv n) σ0 (killg ℓ t) =
  killg ℓ (link_tr (call n) (linkv n) σ0 t).
Proof.
  apply link_tr_killg; auto.
  - intros; apply wf_call; auto.
  - intros; apply wf_linkv; auto.
  - intros; apply eq_call; auto.
  - intros; apply eq_linkv; auto.
  - intros; apply nf_linkv; auto.
Qed.

(** The trace of a binding is the same for each anchor [ℓ] but the dead
    anchor. *)
Lemma denote_bind n x e1 e2 ℓ (NZ : ℓ ≠ 0) :
  denote n (Bind x e1 e2) =
  bind (fun v =>
    bind (on_mod (fun σ2 => Ret (vl_exp (nv_bd x (wvl_mu (close_vl 0 ℓ v)) σ2))))
      (call n (nv_bd x (wvl_mu (close_vl 0 ℓ v)) (nv_sh Init)) (den e2)))
    (killg ℓ (call n (nv_bd x (wvl_an (F ℓ)) (nv_sh Init)) (den e1))).
Proof.
  simpl. symmetry.
  assert (wf_nv (nv_bd x (wvl_an (F 1)) (nv_sh Init))) as W1 by (simpl; auto).
  pose proof (kill_close_eq (fun y => y) ℓ 1
    (call n (nv_bd x (wvl_an (F 1)) (nv_sh Init)) (den e1))
    (fun u => bind (on_mod (fun σ2 => Ret (vl_exp (nv_bd x (wvl_mu u) σ2))))
                (call n (nv_bd x (wvl_mu u) (nv_sh Init)) (den e2)))
    (fun u => bind (on_mod (fun σ2 => Ret (vl_exp (nv_bd x (wvl_mu u) σ2))))
                (call n (nv_bd x (wvl_mu u) (nv_sh Init)) (den e2)))
    eq_refl NZ (wf_call n _ _ W1 (wfb_den e1))) as H.
  rewrite ren_tr_id in H.
  rewrite <- (eq_call n _ _ (den e1)) in H; auto.
  - simpl in H. apply H.
    + intros y [-> NE]. apply nf_call; auto. apply wfb_den. simpl. split; auto.
      congruence.
    + intros u Wu. rewrite ren_tr_id, ren_id. reflexivity.
  - apply wfb_den.
Qed.
