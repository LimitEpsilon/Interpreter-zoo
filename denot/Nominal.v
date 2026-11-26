(** * Facts about anchors

    This file proves how open, close, rename and unroll act on each other and
    on the free anchors of a value. It states each fact once, for values.
    [vl_sh], [vl_exp] and [vl_cstr c] make a shadow, an environment or a list
    of values into a value, so each fact also holds for them.

    ** Main definitions

    - [vl_ind1]: induction on the 4 mutual types of values with one
      predicate.
    - [aan_vl]: a property of each anchor of a value.
    - [nf_vl x]: the anchor [x] is fresh for a value.
    - [tall]: a property of each guard, each scrutinee and each leaf of a
      trace.
    - [nft x]: the anchor [x] is fresh for each value of a trace.

    ** Main results

    - [sup_nf], [fresh_nv], [fresh_vl]: a name above each free anchor is
      fresh.
    - [ren_ext_nf]: two renamings that differ only on fresh anchors give the
      same value.
    - [ren_open], [ren_close]: rename moves through open and close.
    - [close_open]: close after open of a fresh anchor gives the value back.
    - [ren_unroll], [read_ren]: rename moves through unroll and through a
      read.
    - [tmap_bind], [bind_tmap], [tmap_tmap], [tmap_ext]: the equations of
      [tmap].

    ** Tactics

    - [veq]: prove an equation between values from the induction hypotheses.
    - [dconj]: split each conjunction of the context. *)
From Stdlib Require Import Utf8 String Bool Arith Lia List.
From Denot Require Import Syntax Anchor Domain.
Set Warnings "-notation-for-abbreviation".

(** ** One induction principle for values *)

(** Induction on values with one predicate. A shadow, an environment and a
    list of values are values through [vl_sh], [vl_exp] and [vl_cstr c]. *)
Lemma vl_ind1 (P : vl → Prop)
  (HInit : P (vl_sh Init))
  (HRead : ∀ s x, P (vl_sh s) → P (vl_sh (Read s x)))
  (HCall : ∀ s v, P (vl_sh s) → P v → P (vl_sh (Call s v)))
  (HDstr : ∀ s c i, P (vl_sh s) → P (vl_sh (Dstr s c i)))
  (Hmt : P (vl_exp nv_mt))
  (Hsh : ∀ s, P (vl_sh s) → P (vl_exp (nv_sh s)))
  (Hbd : ∀ x v σ, P v → P (vl_exp σ) → P (vl_exp (nv_bd x v σ)))
  (Hmu : ∀ x v σ, P v → P (vl_exp σ) → P (vl_exp (nv_mu x v σ)))
  (Han : ∀ x a σ, P (vl_exp σ) → P (vl_exp (nv_an x a σ)))
  (Hclos : ∀ x b σ, P (vl_exp σ) → P (vl_clos x b σ))
  (Hnil : ∀ c, P (vl_cstr c vnil))
  (Hcons : ∀ c v vs, P v → P (vl_cstr c vs) → P (vl_cstr c (vcons v vs))) :
  ∀ v, P v.
Proof.
  apply (val_mutind (fun s => P (vl_sh s)) (fun σ => P (vl_exp σ)) P
           (fun vs => ∀ c, P (vl_cstr c vs))); auto.
Qed.

(** [vl_sh] is injective. *)
Lemma vl_sh_inj s s' : vl_sh s = vl_sh s' → s = s'.
Proof. congruence. Qed.

(** [vl_exp] is injective. *)
Lemma vl_exp_inj σ σ' : vl_exp σ = vl_exp σ' → σ = σ'.
Proof. congruence. Qed.

(** [vl_cstr c] is injective. *)
Lemma vl_cstr_inj c vs vs' : vl_cstr c vs = vl_cstr c vs' → vs = vs'.
Proof. congruence. Qed.

(** Prove an equation of two parts of a value from an induction hypothesis of
    [vl_ind1]. *)
Ltac inj_ih :=
  solve [ auto
        | apply vl_sh_inj; auto
        | apply vl_exp_inj; auto
        | eapply vl_cstr_inj; eauto ].

(** Remove the same constructor from the 2 sides of an equation between
    values. *)
Ltac veq1 :=
  match goal with
  | |- vl_sh _ = vl_sh _ => f_equal
  | |- vl_exp _ = vl_exp _ => f_equal
  | |- vl_clos _ _ _ = vl_clos _ _ _ => f_equal
  | |- vl_cstr _ _ = vl_cstr _ _ => f_equal
  | |- Read _ _ = Read _ _ => f_equal
  | |- Call _ _ = Call _ _ => f_equal
  | |- Dstr _ _ _ = Dstr _ _ _ => f_equal
  | |- nv_sh _ = nv_sh _ => f_equal
  | |- nv_bd _ _ _ = nv_bd _ _ _ => f_equal
  | |- nv_mu _ _ _ = nv_mu _ _ _ => f_equal
  | |- nv_an _ _ _ = nv_an _ _ _ => f_equal
  | |- vcons _ _ = vcons _ _ => f_equal
  end.

(** Prove an equation between values. The tactic goes into the constructors
    and uses the induction hypotheses. *)
Ltac veq := simpl in *; repeat first [inj_ih | veq1]; try reflexivity.

(** Split each conjunction of the context. *)
Ltac dconj := repeat match goal with H : _ ∧ _ |- _ => destruct H end.

(** Apply the induction hypothesis whose conclusion is the goal, then run
    [tac]. *)
Ltac by_ih tac :=
  match goal with IH : _ → ?G |- ?G => apply IH; tac end.

(** ** A property of each anchor *)

(** [P] holds of each anchor. *)
Fixpoint aan_shdw (P : anc → Prop) (s : shdw) : Prop :=
  match s with
  | Init => True
  | Read s' _ => aan_shdw P s'
  | Call s' v => aan_shdw P s' ∧ aan_vl P v
  | Dstr s' _ _ => aan_shdw P s'
  end
with aan_nv (P : anc → Prop) (σ : nv) : Prop :=
  match σ with
  | nv_mt => True
  | nv_sh s => aan_shdw P s
  | nv_bd _ v σ' => aan_vl P v ∧ aan_nv P σ'
  | nv_mu _ v σ' => aan_vl P v ∧ aan_nv P σ'
  | nv_an _ a σ' => P a ∧ aan_nv P σ'
  end
with aan_vl (P : anc → Prop) (v : vl) : Prop :=
  match v with
  | vl_exp σ => aan_nv P σ
  | vl_sh s => aan_shdw P s
  | vl_clos _ _ σ => aan_nv P σ
  | vl_cstr _ vs => aan_vls P vs
  end
with aan_vls (P : anc → Prop) (vs : vls) : Prop :=
  match vs with
  | vnil => True
  | vcons v vs' => aan_vl P v ∧ aan_vls P vs'
  end.

(** The anchor [x] is fresh, that is no entry holds the name [x]. *)
Notation nf_shdw x := (aan_shdw (fun a => a ≠ F x)) (only parsing).
Notation nf_nv x := (aan_nv (fun a => a ≠ F x)) (only parsing).
Notation nf_vl x := (aan_vl (fun a => a ≠ F x)) (only parsing).
Notation nf_vls x := (aan_vls (fun a => a ≠ F x)) (only parsing).

(** A property of each anchor implies each weaker property. *)
Lemma aan_impl (P Q : anc → Prop) (H : ∀ a, P a → Q a) v : aan_vl P v → aan_vl Q v.
Proof. induction v using vl_ind1; simpl in *; intuition auto. Qed.

(** 2 properties of each anchor give their conjunction. *)
Lemma aan_and (P Q : anc → Prop) v :
  aan_vl P v → aan_vl Q v → aan_vl (fun a => P a ∧ Q a) v.
Proof. induction v using vl_ind1; simpl in *; intuition auto. Qed.

(** [P] holds of each anchor after [am_vl f] when [P] holds of [f k a] for
    each anchor [a]. *)
Lemma aan_am (P : anc → Prop) f v : ∀ k,
  aan_vl (fun a => ∀ k, P (f k a)) v → aan_vl P (am_vl f k v).
Proof. induction v using vl_ind1; simpl in *; intuition auto. Qed.

(** Assume that each anchor of [R] is fresh for [v]. Then no anchor of [v] is
    in [R]. *)
Lemma nf_all (R : loc → Prop) v :
  (∀ x, R x → nf_vl x v) → aan_vl (fun a => ∀ y, a = F y → ¬ R y) v.
Proof.
  induction v using vl_ind1; simpl in *; intros H; auto;
    try solve [intuition auto].
  all: split; try (by_ih ltac:(intros y Hy; apply (H y Hy))).
  intros y -> Hy. destruct (H y Hy) as [N _]. congruence.
Qed.

(** ** Fresh anchors *)

(** Open with [ℓ] keeps each other anchor fresh. *)
Lemma nf_open y ℓ v (NE : y ≠ ℓ) : ∀ i, nf_vl y v → nf_vl y (open_vl i ℓ v).
Proof.
  intros i H. apply aan_am. eapply aan_impl; [|exact H].
  intros [j|z] Ha k; simpl; [destruct (Nat.eqb j k)|]; congruence.
Qed.

(** Close keeps a fresh anchor fresh. *)
Lemma nf_close y ℓ v : ∀ i, nf_vl y v → nf_vl y (close_vl i ℓ v).
Proof.
  intros i H. apply aan_am. eapply aan_impl; [|exact H].
  intros [j|z] Ha k; simpl; [|destruct (Nat.eqb z ℓ)]; congruence.
Qed.

(** After close of [ℓ], the anchor [ℓ] is fresh. *)
Lemma nf_close_self ℓ v : ∀ i, nf_vl ℓ (close_vl i ℓ v).
Proof.
  intros i. apply aan_am. apply aan_impl with (P := fun _ => True).
  - intros [j|z] _ k; simpl; [congruence|].
    destruct (Nat.eqb z ℓ) eqn:E; [congruence|].
    apply Nat.eqb_neq in E. congruence.
  - clear. induction v using vl_ind1; simpl; auto.
Qed.

(** The anchor [y] is fresh after a renaming that takes no anchor of the
    value to [y]. *)
Lemma nf_ren y ξ v :
  aan_vl (fun a => ∀ z, a = F z → ξ z ≠ y) v → ∀ k, nf_vl y (am_vl (fren ξ) k v).
Proof.
  intros H k. apply aan_am. eapply aan_impl; [|exact H].
  intros [j|z] Ha k'; simpl; [congruence|].
  specialize (Ha z eq_refl). congruence.
Qed.

(** When [ξ x] is fresh after the renaming [ξ], then [x] is fresh before it. *)
Lemma nf_ren_inv ξ x v : ∀ k, nf_vl (ξ x) (am_vl (fren ξ) k v) → nf_vl x v.
Proof.
  induction v using vl_ind1; simpl in *; intros k0 H; intuition eauto.
  destruct a; simpl in *; congruence.
Qed.

(** A name above the largest free anchor is fresh. *)
Lemma sup_nf x v : sup_vl v < x → nf_vl x v.
Proof.
  induction v using vl_ind1; simpl in *; intros H; auto;
    try solve [intuition auto].
  all: split; try (by_ih lia).
  destruct a; [congruence|]. intros E. inversion E. lia.
Qed.

(** [sup_nf] for an environment. *)
Lemma sup_nf_nv x σ : sup_nv σ < x → nf_nv x σ.
Proof. exact (sup_nf x (vl_exp σ)). Qed.

(** [fresh σ v] is fresh for [σ]. *)
Lemma fresh_nv σ v : nf_nv (fresh σ v) σ.
Proof. apply sup_nf_nv. unfold fresh. lia. Qed.

(** [fresh σ v] is fresh for [v]. *)
Lemma fresh_vl σ v : nf_vl (fresh σ v) v.
Proof. apply sup_nf. unfold fresh. lia. Qed.

(** [fresh σ v] is not the dead anchor. *)
Lemma fresh_pos σ v : fresh σ v ≠ 0.
Proof. unfold fresh. lia. Qed.

(** ** Rename *)

(** Rename does not depend on the number of recursive values around. *)
Lemma ren_k ξ v : ∀ k k', am_vl (fren ξ) k v = am_vl (fren ξ) k' v.
Proof. induction v using vl_ind1; intros; veq. Qed.

(** 2 renamings that agree on each anchor of a value give the same value. *)
Lemma ren_ext ξ ξ' v :
  aan_vl (fun a => ∀ y, a = F y → ξ y = ξ' y) v →
  ∀ k, am_vl (fren ξ) k v = am_vl (fren ξ') k v.
Proof.
  induction v using vl_ind1; simpl; intros H k; dconj; veq.
  destruct a; simpl; auto.
Qed.

(** 2 renamings that differ only on fresh anchors give the same value. *)
Lemma ren_ext_nf ξ ξ' v (H : ∀ y, ξ y ≠ ξ' y → nf_vl y v) :
  ∀ k, am_vl (fren ξ) k v = am_vl (fren ξ') k v.
Proof.
  apply ren_ext. eapply aan_impl; [|apply (nf_all _ _ H)].
  intros a Ha y ->. destruct (Nat.eq_dec (ξ y) (ξ' y)); auto.
  exfalso. apply (Ha y eq_refl). auto.
Qed.

(** The identity renaming changes nothing. *)
Lemma ren_id v : ∀ k, am_vl (fren (fun x => x)) k v = v.
Proof.
  induction v using vl_ind1; intros; veq.
  destruct a; reflexivity.
Qed.

(** 2 renamings compose. *)
Lemma ren_ren ξ ζ v : ∀ k,
  am_vl (fren ξ) k (am_vl (fren ζ) k v) = am_vl (fren (fun x => ξ (ζ x))) k v.
Proof.
  induction v using vl_ind1; intros; veq.
  destruct a; reflexivity.
Qed.

(** Rename after open is open after rename, with the renamed anchor. *)
Lemma ren_open ξ ℓ v : ∀ k i,
  am_vl (fren ξ) k (open_vl i ℓ v) = open_vl i (ξ ℓ) (am_vl (fren ξ) k v).
Proof.
  induction v using vl_ind1; intros; veq.
  destruct a as [j|z]; simpl; auto. destruct (Nat.eqb j i); reflexivity.
Qed.

(** Rename after close is close after rename, when the renaming takes no
    other anchor of the value to [ξ ℓ]. *)
Lemma ren_close ξ ℓ v :
  aan_vl (fun a => ∀ y, a = F y → y ≠ ℓ → ξ y ≠ ξ ℓ) v →
  ∀ k i, am_vl (fren ξ) k (close_vl i ℓ v) = close_vl i (ξ ℓ) (am_vl (fren ξ) k v).
Proof.
  induction v using vl_ind1; simpl; intros H k d; dconj; veq.
  destruct a as [j|z]; simpl; auto.
  match goal with H : ∀ y, _ = F y → _ |- _ => rename H into Hz end.
  destruct (Nat.eqb z ℓ) eqn:E; simpl.
  - apply Nat.eqb_eq in E. subst z. rewrite Nat.eqb_refl. reflexivity.
  - apply Nat.eqb_neq in E. specialize (Hz z eq_refl E).
    apply Nat.eqb_neq in Hz. rewrite Hz. reflexivity.
Qed.

(** Close after open of a fresh anchor gives the value back. The inverse
    order needs a locally closed value ([open_close] in [Wf.v]). *)
Lemma close_open ℓ v : nf_vl ℓ v → ∀ i, close_vl i ℓ (open_vl i ℓ v) = v.
Proof.
  induction v using vl_ind1; simpl; intros H d; dconj; veq.
  destruct a as [j|z]; simpl.
  - destruct (Nat.eqb j d) eqn:E; simpl.
    + rewrite Nat.eqb_refl. apply Nat.eqb_eq in E. congruence.
    + reflexivity.
  - destruct (Nat.eqb z ℓ) eqn:E; auto.
    apply Nat.eqb_eq in E. congruence.
Qed.

(** Close of a fresh anchor changes nothing. *)
Lemma close_nf ℓ v : nf_vl ℓ v → ∀ i, close_vl i ℓ v = v.
Proof.
  induction v using vl_ind1; simpl; intros H d; dconj; veq.
  destruct a as [j|z]; simpl; auto.
  destruct (Nat.eqb z ℓ) eqn:E; auto. apply Nat.eqb_eq in E. congruence.
Qed.

(** ** Unroll *)

(** Rename moves through the replacement of an index by a recursive value. *)
Lemma ren_su ξ u v : ∀ k k' d,
  am_vl (fren ξ) k (su_vl (funr u) d v) =
  su_vl (funr (am_vl (fren ξ) k' u)) d (am_vl (fren ξ) k v).
Proof.
  induction v using vl_ind1; intros k0 k' d; veq.
  destruct a as [j|z]; simpl; [|veq].
  destruct (Nat.eqb j d); simpl; veq. apply ren_k.
Qed.

(** Rename moves through unroll. *)
Lemma ren_unroll ξ v k : am_vl (fren ξ) 0 (unroll v) = unroll (am_vl (fren ξ) k v).
Proof.
  unfold unroll. rewrite (ren_su ξ v v 0 k 0). f_equal. apply ren_k.
Qed.

(** A property of each anchor of [u] and of [v] holds after the replacement
    of an index of [v] by the recursive value of [u]. *)
Lemma aan_su (P : anc → Prop) u v : ∀ d,
  aan_vl P u → aan_vl P v → aan_vl P (su_vl (funr u) d v).
Proof.
  induction v using vl_ind1; simpl in *; intros d Hu Hv; try solve [intuition auto].
  destruct a as [j|z]; simpl.
  - destruct (Nat.eqb j d); simpl; intuition auto.
  - intuition auto.
Qed.

(** ** Reads and fields *)

(** A read in a renamed environment gives the renamed value. *)
Lemma read_ren ξ x σ :
  read x (ren_nv ξ σ) = option_map (ren_vl ξ) (read x σ).
Proof.
  induction σ as [|s|y v σ IH|y v σ IH|y a σ IH]; simpl; auto.
  - destruct (String.eqb x y); auto.
  - destruct (String.eqb x y); auto. simpl. f_equal. symmetry. apply ren_unroll.
  - destruct (String.eqb x y); auto.
Qed.

(** A property of each anchor of an environment holds of each value that a
    read gives. *)
Lemma read_aan (P : anc → Prop) x σ v :
  aan_nv P σ → read x σ = Some v → aan_vl P v.
Proof.
  induction σ as [|s|y u σ IH|y u σ IH|y a σ IH]; simpl; intros H R;
    try discriminate.
  - inversion R; subst. simpl. auto.
  - destruct (String.eqb x y); [inversion R; subst|]; intuition auto.
  - destruct (String.eqb x y); [inversion R; subst|]; intuition auto.
    apply aan_su; auto.
  - destruct (String.eqb x y); [discriminate|]. intuition auto.
Qed.

(** A field of a list after [am_vls] is the field after [am_vl]. *)
Lemma vnth_am f k vs : ∀ i,
  vnth i (am_vls f k vs) = option_map (am_vl f k) (vnth i vs).
Proof. induction vs as [|v vs IH]; simpl; intros [|i]; auto. Qed.

(** [am_vls] keeps the length. *)
Lemma vlen_am f k vs : vlen (am_vls f k vs) = vlen vs.
Proof. induction vs; simpl; auto. Qed.

(** A property of each anchor of a list of values holds of each of its
    values. *)
Lemma vnth_aan (P : anc → Prop) vs : ∀ i v,
  aan_vls P vs → vnth i vs = Some v → aan_vl P v.
Proof.
  induction vs as [|u vs IH]; simpl; intros i v H N; try discriminate.
  destruct i; [inversion N; subst; tauto|]. eapply IH; eauto. tauto.
Qed.

(** ** Traces *)

(** [Pg] holds of each guard, [Ps] of each scrutinee and [Pl] of each leaf. *)
Fixpoint tall (Pg : vl → Prop) (Ps : shdw → Prop) (Pl : vl → Prop) (t : trace) : Prop :=
  match t with
  | Bot => True
  | Ret v => Pl v
  | Guard u t' => Pg u ∧ tall Pg Ps Pl t'
  | Match s bs => Ps s ∧ tall_brs Pg Ps Pl bs
  end
with tall_brs (Pg : vl → Prop) (Ps : shdw → Prop) (Pl : vl → Prop) (bs : brs) : Prop :=
  match bs with
  | bnil => True
  | bcons _ _ t bs' => tall Pg Ps Pl t ∧ tall_brs Pg Ps Pl bs'
  end.

(** The anchor [x] is fresh for each value of a trace. *)
Notation nft x := (tall (aan_vl (fun a => a ≠ F x)) (aan_shdw (fun a => a ≠ F x))
                     (aan_vl (fun a => a ≠ F x))) (only parsing).

(** The mutual form of [tall_impl]. *)
Lemma tall_impl_mut (Pg Pg' : vl → Prop) (Ps Ps' : shdw → Prop) (Pl Pl' : vl → Prop)
  (Hg : ∀ u, Pg u → Pg' u) (Hs : ∀ s, Ps s → Ps' s) (Hl : ∀ v, Pl v → Pl' v) :
  (∀ t, tall Pg Ps Pl t → tall Pg' Ps' Pl' t) ∧
  (∀ bs, tall_brs Pg Ps Pl bs → tall_brs Pg' Ps' Pl' bs).
Proof. apply tr_mutind; simpl; intuition auto. Qed.

(** [tall] is monotone in its 3 predicates. *)
Lemma tall_impl (Pg Pg' : vl → Prop) (Ps Ps' : shdw → Prop) (Pl Pl' : vl → Prop) t
  (Hg : ∀ u, Pg u → Pg' u) (Hs : ∀ s, Ps s → Ps' s) (Hl : ∀ v, Pl v → Pl' v) :
  tall Pg Ps Pl t → tall Pg' Ps' Pl' t.
Proof. apply tall_impl_mut; auto. Qed.

(** The mutual form of [tall_bind]. *)
Lemma tall_bind_mut (Pg : vl → Prop) (Ps : shdw → Prop) (Q Pl : vl → Prop) k
  (Hk : ∀ v, Q v → tall Pg Ps Pl (k v)) :
  (∀ t, tall Pg Ps Q t → tall Pg Ps Pl (bind k t)) ∧
  (∀ bs, tall_brs Pg Ps Q bs → tall_brs Pg Ps Pl (bind_brs k bs)).
Proof. apply tr_mutind; simpl; intuition auto. Qed.

(** [tall] holds of [bind k t] when it holds of [t] and of [k v] for each
    leaf [v] of [t]. *)
Lemma tall_bind (Pg : vl → Prop) (Ps : shdw → Prop) (Q Pl : vl → Prop) k t
  (Hk : ∀ v, Q v → tall Pg Ps Pl (k v)) (Ht : tall Pg Ps Q t) :
  tall Pg Ps Pl (bind k t).
Proof. eapply tall_bind_mut; eauto. Qed.

(** The mutual form of [tall_tmap]. *)
Lemma tall_tmap_mut (Pg : vl → Prop) (Ps : shdw → Prop) (Pl : vl → Prop) g gs h :
  (∀ t, tall (fun u => Pg (g u)) (fun s => Ps (gs s)) (fun v => Pl (h v)) t →
        tall Pg Ps Pl (tmap g gs h t)) ∧
  (∀ bs, tall_brs (fun u => Pg (g u)) (fun s => Ps (gs s)) (fun v => Pl (h v)) bs →
         tall_brs Pg Ps Pl (tmap_brs g gs h bs)).
Proof. apply tr_mutind; simpl; intuition auto. Qed.

(** [tall] holds of [tmap g gs h t] when it holds of [t] for the predicates
    after [g], [gs] and [h]. *)
Lemma tall_tmap (Pg : vl → Prop) (Ps : shdw → Prop) (Pl : vl → Prop) g gs h t :
  tall (fun u => Pg (g u)) (fun s => Ps (gs s)) (fun v => Pl (h v)) t →
  tall Pg Ps Pl (tmap g gs h t).
Proof. apply tall_tmap_mut. Qed.

(** The result of a finished trace satisfies the predicate of the leaves. *)
Lemma tall_dest (Pg : vl → Prop) (Ps : shdw → Prop) (Pl : vl → Prop) t v :
  tall Pg Ps Pl t → dest t = Some v → Pl v.
Proof.
  induction t; simpl; intros H D; try discriminate.
  - inversion D; subst; auto.
  - apply IHt; tauto.
Qed.

(** The mutual form of [tmap_ext]. *)
Lemma tmap_ext_mut g gs h g' gs' h' :
  (∀ t, tall (fun u => g u = g' u) (fun s => gs s = gs' s) (fun v => h v = h' v) t →
        tmap g gs h t = tmap g' gs' h' t) ∧
  (∀ bs, tall_brs (fun u => g u = g' u) (fun s => gs s = gs' s)
           (fun v => h v = h' v) bs →
         tmap_brs g gs h bs = tmap_brs g' gs' h' bs).
Proof.
  apply tr_mutind; simpl; auto.
  - intros v ->. reflexivity.
  - intros u t IH [-> H]. f_equal; auto.
  - intros s bs IH [-> H]. f_equal; auto.
  - intros c n t bs IHt IHb [Ht Hb]. f_equal; auto.
Qed.

(** 2 maps that agree on each value of a trace give the same trace. *)
Lemma tmap_ext g gs h g' gs' h' t :
  tall (fun u => g u = g' u) (fun s => gs s = gs' s) (fun v => h v = h' v) t →
  tmap g gs h t = tmap g' gs' h' t.
Proof. apply tmap_ext_mut. Qed.

(** The mutual form of [tmap_id]. *)
Lemma tmap_id_mut :
  (∀ t, tmap (fun v => v) (fun s => s) (fun v => v) t = t) ∧
  (∀ bs, tmap_brs (fun v => v) (fun s => s) (fun v => v) bs = bs).
Proof. apply tr_mutind; simpl; intros; f_equal; auto. Qed.

(** [tmap] with 3 identities changes nothing. *)
Lemma tmap_id t : tmap (fun v => v) (fun s => s) (fun v => v) t = t.
Proof. apply tmap_id_mut. Qed.

(** The mutual form of [tmap_tmap]. *)
Lemma tmap_tmap_mut g2 gs2 h2 g1 gs1 h1 :
  (∀ t, tmap g2 gs2 h2 (tmap g1 gs1 h1 t) =
        tmap (fun u => g2 (g1 u)) (fun s => gs2 (gs1 s)) (fun v => h2 (h1 v)) t) ∧
  (∀ bs, tmap_brs g2 gs2 h2 (tmap_brs g1 gs1 h1 bs) =
         tmap_brs (fun u => g2 (g1 u)) (fun s => gs2 (gs1 s)) (fun v => h2 (h1 v)) bs).
Proof. apply tr_mutind; simpl; intros; f_equal; auto. Qed.

(** 2 maps compose. *)
Lemma tmap_tmap g2 gs2 h2 g1 gs1 h1 t :
  tmap g2 gs2 h2 (tmap g1 gs1 h1 t) =
  tmap (fun u => g2 (g1 u)) (fun s => gs2 (gs1 s)) (fun v => h2 (h1 v)) t.
Proof. apply tmap_tmap_mut. Qed.

(** The mutual form of [tmap_bind]. *)
Lemma tmap_bind_mut g gs h k :
  (∀ t, tmap g gs h (bind k t) =
        bind (fun v => tmap g gs h (k v)) (tmap g gs (fun v => v) t)) ∧
  (∀ bs, tmap_brs g gs h (bind_brs k bs) =
         bind_brs (fun v => tmap g gs h (k v)) (tmap_brs g gs (fun v => v) bs)).
Proof. apply tr_mutind; simpl; intros; f_equal; auto. Qed.

(** A map of [bind k t] maps the spine of [t] and each [k v]. *)
Lemma tmap_bind g gs h k t :
  tmap g gs h (bind k t) =
  bind (fun v => tmap g gs h (k v)) (tmap g gs (fun v => v) t).
Proof. apply tmap_bind_mut. Qed.

(** The mutual form of [bind_tmap]. *)
Lemma bind_tmap_mut g gs h k :
  (∀ t, bind k (tmap g gs h t) =
        bind (fun v => k (h v)) (tmap g gs (fun v => v) t)) ∧
  (∀ bs, bind_brs k (tmap_brs g gs h bs) =
         bind_brs (fun v => k (h v)) (tmap_brs g gs (fun v => v) bs)).
Proof. apply tr_mutind; simpl; intros; f_equal; auto. Qed.

(** [bind] after a map applies the map of the leaves first. *)
Lemma bind_tmap g gs h k t :
  bind k (tmap g gs h t) = bind (fun v => k (h v)) (tmap g gs (fun v => v) t).
Proof. apply bind_tmap_mut. Qed.

(** The mutual form of [bind_ext_tall]. *)
Lemma bind_ext_tall_mut (Pg : vl → Prop) (Ps : shdw → Prop) (Pl : vl → Prop) k k'
  (H : ∀ v, Pl v → k v = k' v) :
  (∀ t, tall Pg Ps Pl t → bind k t = bind k' t) ∧
  (∀ bs, tall_brs Pg Ps Pl bs → bind_brs k bs = bind_brs k' bs).
Proof. apply tr_mutind; simpl; intros; f_equal; intuition auto. Qed.

(** 2 continuations that agree on each leaf of a trace give the same trace. *)
Lemma bind_ext_tall (Pg : vl → Prop) (Ps : shdw → Prop) (Pl : vl → Prop) k k' t
  (H : ∀ v, Pl v → k v = k' v) (Ht : tall Pg Ps Pl t) : bind k t = bind k' t.
Proof. eapply bind_ext_tall_mut; eauto. Qed.

(** The result after a map is the map of the result. *)
Lemma dest_tmap g gs h t : dest (tmap g gs h t) = option_map h (dest t).
Proof. induction t; simpl; auto. Qed.

(** [killg] keeps the result. *)
Lemma dest_killg ℓ t : dest (killg ℓ t) = dest t.
Proof. unfold killg. rewrite dest_tmap. destruct (dest t); reflexivity. Qed.
