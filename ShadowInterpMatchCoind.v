From Stdlib Require Import Utf8.
From Stdlib Require Import PArith Lia.
From Stdlib Require Import String List.
From Paco Require Import paco.
Import ListNotations.

Local Open Scope string_scope.
Local Unset Elimination Schemes.
Local Set Primitive Projections.

Module StreamTest.
  Variant streamF {T stream : Type} :=
  | snil
  | scons (hd : T) (tl : stream)
  .

  Arguments streamF : clear implicits.

  Inductive streamA {T : Type} := Str (k : streamF T streamA).
  Arguments streamA : clear implicits.

  Definition streamA_ind T P (Psnil : P (Str snil))
    (Pscons : ∀ (hd : T) (tl : streamA T), P tl → P (Str (scons hd tl)))
  : ∀ s, P s :=
    fix go s :=
      match s with
      | Str snil => Psnil
  | Str (scons hd tl) => Pscons hd tl (go tl)
      end.

  CoInductive stream {T : Type} := mkStream { obs_st : streamF T stream }.
  Arguments stream : clear implicits.
  Arguments mkStream {_} _.

  (* define approximation order *)
  Definition le_streamF {T st} (le_st : st → st → Prop) :=
    fun (sF sF' : streamF T st) =>
    match sF with
    | snil => True
    | scons hd tl =>
      match sF' with
      | scons hd' tl' => hd = hd' ∧ le_st tl tl'
      | _ => False
      end
    end.

  Definition lt_streamF {T st} (lt_st : st → st → Prop) :=
    fun (sF sF' : streamF T st) =>
    match sF with
    | snil =>
      match sF' with
      | snil => False
      | scons _ _ => True
      end
    | scons hd tl =>
      match sF' with
      | scons hd' tl' => hd = hd' ∧ lt_st tl tl'
      | _ => False
      end
    end.

  Fixpoint le_streamA {T} (s s' : streamA T) :=
    match s with
    | Str k =>
      match s' with
      | Str k' => le_streamF le_streamA k k'
      end
    end.

  Fixpoint lt_streamA {T} (s s' : streamA T) :=
    match s with
    | Str k =>
      match s' with
      | Str k' => lt_streamF lt_streamA k k'
      end
    end.

  Fixpoint nth_approxA {T} (s : streamA T) (n : nat) : streamA T :=
    Str match n with
    | 0 => snil
    | S n' =>
      match s with
      | Str snil => snil
      | Str (scons hd tl) => scons hd (nth_approxA tl n')
      end
    end.

  Fixpoint nth_approx {T} (s : stream T) (n : nat) : streamA T :=
    Str match n with
    | 0 => snil
    | S n' =>
      match obs_st s with
      | snil => snil
      | scons hd tl => scons hd (nth_approx tl n')
      end
    end.

  Definition eq_streamF T eq_st (s s' : stream T) :=
    match obs_st s with
    | snil =>
      match obs_st s' with
      | snil => True
      | _ => False
      end
    | scons hd tl =>
      match obs_st s' with
      | scons hd' tl' => hd = hd' ∧ eq_st tl tl'
      | snil => False
      end
    end.
 
  Lemma eq_streamF_monotone {T} : monotone2 (eq_streamF T).
  Proof.
    repeat intro. unfold eq_streamF in *.
    destruct (obs_st _); auto.
    destruct (obs_st _); intuition auto.
  Qed.

  Hint Resolve eq_streamF_monotone : paco.

  Definition eq_stream {T} := paco2 (eq_streamF T) bot2.

  (* eq_stream is an equivalence relation *)
  Lemma eq_stream_refl {T} (s : stream T)
  : eq_stream s s.
  Proof.
    revert s. pcofix CIH.
    intros. pfold. unfold eq_streamF.
    destruct (obs_st s); auto.
  Qed.

  Lemma eq_stream_sym {T} (s s' : stream T) (EQ : eq_stream s s')
  : eq_stream s' s.
  Proof.
    revert s s' EQ. pcofix CIH.
    intros. pfold. unfold eq_streamF.
    destruct (obs_st _) eqn:OBS'.
    - punfold EQ.
      unfold eq_streamF in EQ.
      rewrite OBS' in *. auto.
    - punfold EQ. unfold eq_streamF in EQ.
      rewrite OBS' in *.
      destruct (obs_st s) eqn:OBS; auto.
      destruct EQ as (? & EQ); subst.
      split; auto.
      destruct EQ as [?|?]; try contradiction.
      right. auto.
  Qed.

  Lemma eq_stream_trans {T} (s s' s'' : stream T)
    (EQ : eq_stream s s') (EQ' : eq_stream s' s'')
  : eq_stream s s''.
  Proof.
    revert s s' s'' EQ EQ'. pcofix CIH.
    intros. punfold EQ. punfold EQ'. pfold.
    unfold eq_streamF in *.
    destruct (obs_st s) eqn:OBS.
    { destruct (obs_st s') eqn:OBS'; try contradiction. auto. }
    destruct (obs_st s') eqn:OBS'; try contradiction.
    destruct EQ as (? & EQ); subst.
    destruct (obs_st s'') eqn:OBS''; try contradiction.
    destruct EQ' as (? & EQ'); subst.
    pclearbot.
    split; auto. right. eauto.
  Qed.

  Lemma eq_streamA_eq_stream {T} (s s' : stream T)
    (LE : ∀ n, ∃ m, le_streamA (nth_approx s n) (nth_approx s' m))
    (LE' : ∀ n, ∃ m, le_streamA (nth_approx s' n) (nth_approx s m))
  : eq_stream s s'.
  Proof.
    revert s s' LE LE'. pcofix CIH.
    intros. pfold. unfold eq_streamF.
    destruct (obs_st _) eqn:OBS.
    - destruct (LE' 1) as (m & LE'').
      destruct m; simpl in *; destruct (obs_st s') eqn:OBS'; auto.
      rewrite OBS in *. cbn in LE''. auto.
    - destruct (obs_st s') eqn:OBS'.
      { specialize (LE 1) as (m & LE'').
        destruct m; simpl in *. rewrite OBS in *. simpl in *. auto.
        rewrite OBS, OBS' in *. simpl in *. auto. }
      destruct (LE 1) as (m & LE''). destruct m; simpl in *.
      { rewrite OBS in *. simpl in *. contradiction. }
      rewrite OBS, OBS' in *. simpl in *. destruct LE'' as (? & _); subst.
      split; auto. clear m.
      right. apply CIH; intros.
      { destruct (LE (S n)) as (m & LE'').
        destruct m; simpl in *. rewrite OBS in *. destruct LE''.
        rewrite OBS, OBS' in *.
        exists m. eapply LE''. }
      { destruct (LE' (S n)) as (m & LE'').
        destruct m; simpl in *. rewrite OBS' in *. destruct LE''.
        rewrite OBS, OBS' in *.
        exists m. eapply LE''. }
  Qed.

  Lemma le_streamA_refl {T} (s : streamA T) :
    le_streamA s s.
  Proof. induction s; simpl; auto. Qed.

  Lemma le_streamA_trans {T} :
    (∀ s' : streamA T,
      ∀ s s'', le_streamA s s' → le_streamA s' s'' → le_streamA s s'').
  Proof.
    induction s'; destruct s; destruct k; simpl.
    - destruct s''; auto.
    - intuition auto.
    - destruct s''. destruct k; intuition auto.
    - intros ? (? & LE); subst.
      destruct s''; intuition auto.
      destruct k; intuition auto.
  Qed.

  Lemma lt_streamA_trans {T} :
    (∀ s' : streamA T,
      ∀ s s'', lt_streamA s s' → lt_streamA s' s'' → lt_streamA s s'').
  Proof.
    induction s'; destruct s; destruct k; simpl.
    - destruct s''; auto.
    - intuition auto.
    - destruct s''. destruct k; intuition auto.
    - intros ? (? & LE); subst.
      destruct s''; intuition auto.
      destruct k; intuition auto.
  Qed.

  Lemma le_lt_eq {T} (s s' : streamA T) :
    le_streamA s s' ↔
    s = s' ∨ lt_streamA s s'.
  Proof.
    revert s'. induction s; simpl.
    { destruct s'; destruct k; simpl; intuition auto. }
    destruct s'; destruct k; simpl; intuition auto; subst; try congruence;
    try rewrite IHs in *; intuition auto; subst; eauto.
    match goal with H : _ |- _ => inversion H; subst; eauto end.
  Qed.

  Lemma eq_stream_le_streamA {T} (s s' : stream T) (EQ : eq_stream s s')
  : ∀ n, ∃ m,
      le_streamA (nth_approx s n) (nth_approx s' m).
  Proof.
    intros; revert s s' EQ; induction n; simpl; intros.
    - exists 0; simpl; eauto.
    - punfold EQ.
      unfold eq_streamF in EQ.
      destruct (obs_st s) eqn:OBS.
      { exists 0; simpl; auto. }
      { destruct (obs_st s') eqn:OBS'; [contradiction|].
        destruct EQ as (? & EQ); subst.
        destruct EQ as [EQ|?]; [|contradiction].
        destruct (IHn _ _ EQ) as (m & LE).
        exists (S m).
        simpl. rewrite OBS'. eauto. }
  Qed.

  (* s = s' ↔ ⌊ s ⌋ ≈ ⌊ s' ⌋ *)
  Lemma eq_stream_iff_eq_streamA {T} (s s' : stream T) :
    eq_stream s s' ↔
    (∀ n, ∃ m, le_streamA (nth_approx s n) (nth_approx s' m)) ∧
    (∀ n, ∃ m, le_streamA (nth_approx s' n) (nth_approx s m)).
  Proof.
    split; [|intro; apply eq_streamA_eq_stream; intuition auto].
    intro EQ. apply eq_stream_sym in EQ as EQ'.
    split; apply eq_stream_le_streamA; auto.
  Qed.

  Definition stable {T} (s : nat → streamA T) :=
    ∀ n, lt_streamA (s n) (s (S n)) ∨ ∀ m (LE : n ≤ m), s n = s m
  .

  Definition stable_le {T} (s : nat → streamA T) (ST : stable s)
  : ∀ n m (LE : n ≤ m), le_streamA (s n) (s m).
  Proof.
    intro. revert s ST. induction n; simpl.
    { intros. revert s ST. clear LE.
      induction m; simpl; [intros; apply le_streamA_refl|].
      intros. eapply le_streamA_trans; [apply IHm|]; auto.
      rewrite le_lt_eq. destruct (ST m); eauto. }
    intros. destruct m; simpl in *; [lia|].
    apply IHn with (s := fun n => s (S n)); try lia.
    intro n'. destruct (ST (S n')) as [?|EQ]; eauto.
    right. intros m' LE'.
    assert (n' = m' ∨ S n' ≤ m') as [?|?] by lia; eauto.
  Qed.

  Lemma nth_approx_stable {T} (s : stream T) :
    stable (nth_approx s).
  Proof.
    intro. revert s. induction n; intros; simpl.
    { destruct (obs_st s) eqn:OBS; intuition auto. right.
      induction m; simpl; eauto; rewrite OBS; auto. }
    destruct (obs_st s) eqn:OBS; simpl.
    { right. induction m; simpl; eauto; rewrite OBS; auto. }
    destruct (obs_st tl) eqn:OBS'.
    - right. induction m; [lia|].
      intros. simpl. rewrite OBS. do 2 f_equal.
      destruct (IHn tl).
      { simpl in *; rewrite OBS' in *.
        destruct (nth_approx tl n); destruct k; simpl in *; intuition. }
      assert (n ≤ m) by lia; eauto.
    - destruct (IHn tl).
      { simpl in *; rewrite OBS' in *. eauto. }
      right. intros. destruct m; [lia|].
      simpl in *; rewrite OBS. do 2 f_equal.
      assert (n ≤ m) by lia; eauto.
  Qed.

  CoFixpoint mkStream' {T} (s : nat → streamA T) : stream T :=
    match s 1 with
    | Str snil => {| obs_st := snil |} (* s 0 must be nil *)
    | Str (scons hd _) => {|
      obs_st := scons hd (mkStream' (fun n =>
        match s (S n) with
        | Str snil => Str snil
        | Str (scons _ tl) => tl
        end))
      |}
    end.

  Lemma mkStream'_ext {T} (s s' : nat → streamA T) (EXT : ∀ n, s n = s' n) :
    ∀ d, nth_approx (mkStream' s) d = nth_approx (mkStream' s') d.
  Proof.
    intros. revert s s' EXT. induction d; intros; simpl; eauto.
    rewrite <- EXT. destruct (s 1); destruct k; simpl; eauto.
    erewrite IHd; eauto; simpl.
    intros. rewrite EXT. eauto.
  Qed.

  Fixpoint depth {T} (s : streamA T) :=
    match s with
    | Str snil => 0
    | Str (scons _ tl) => S (depth tl)
    end.

  Lemma stable_tl {T} (s : nat → streamA T) (INC : stable s)
    (NONNIL : s 1 ≠ Str snil)
  : stable (fun n =>
      match s (S n) with
      | Str snil => Str snil
      | Str (scons _ tl) => tl
      end).
  Proof.
    destruct (s 1) eqn:EQ; destruct k. congruence.
    intro n'.
    specialize (stable_le s INC 1 (S n') ltac:(lia)).
    specialize (stable_le s INC 1 (S (S n')) ltac:(lia)).
    rewrite EQ.
    destruct (s (S n')) eqn:OBS; destruct k; simpl.
    destruct 2.
    destruct (s (S (S n'))) eqn:OBS'; destruct k; simpl.
    destruct 1.
    intuition auto; subst.
    destruct (INC (S n')) as [LT|EQ''].
    rewrite OBS, OBS' in LT. simpl in LT. left; apply LT.
    right. intros.
    rewrite <- EQ'' by lia.
    rewrite OBS. auto.
  Qed.

  Lemma le_streamA_nth_approxA {T} (s s' : streamA T) (LE : le_streamA s s')
  : ∀ d (LEd : d ≤ depth s), nth_approxA s d = nth_approxA s' d.
  Proof.
    intros. revert s' LE d LEd.
    induction s; simpl.
    { destruct s'; destruct d; simpl; intros; auto; lia. }
    destruct s'; destruct d; simpl; intros; auto.
    destruct k; destruct LE; subst.
    erewrite IHs; eauto. lia.
  Qed.

  Lemma le_streamA_depth {T} (s s' : streamA T) (LE : le_streamA s s')
  : depth s ≤ depth s'.
  Proof.
    revert s' LE. induction s; simpl; [lia|].
    destruct s'; destruct k; intros; destruct LE; subst.
    simpl. assert (depth s ≤ depth tl) by auto.
    lia.
  Qed.

  Lemma nth_approxA_depth {T} (s : streamA T)
  : ∀ d (LE : depth s ≤ d), nth_approxA s d = s.
  Proof.
    induction s; simpl; destruct d; simpl; auto.
    - lia.
    - intros. repeat f_equal. apply IHs. lia.
  Qed.

  Lemma stable_approx_mkStream' {T} (s : nat → streamA T) (INC : stable s)
  : ∀ d n (DEPTH : d ≤ depth (s n)),
      nth_approxA (s n) d = nth_approx (mkStream' s) d.
  Proof.
    intro. revert s INC. induction d; simpl.
    - intros. destruct (s n); destruct k; simpl in *; congruence.
    - intros. destruct (s n) eqn:EQ; destruct k; simpl in *. lia.
      destruct (s 1) eqn:EQ'; destruct k; simpl.
      { assert (∀ n, s n = Str snil) as RR.
        { specialize (INC 0). destruct INC as [LT|STABLE].
          rewrite EQ' in LT. destruct (s 0); destruct k; destruct LT.
          rewrite <- STABLE in EQ' by lia. intros. rewrite <- STABLE by lia. auto. }
        rewrite RR in EQ. congruence. }
      set (s' m :=
        match s (S m) with
        | Str snil => Str snil
        | Str (scons _ tl') => tl'
        end).
      assert (stable s') as ST' by (apply stable_tl; auto; congruence).
      specialize (IHd s' ST') as IHd'.
      destruct n.
      { specialize (stable_le s INC 0 1 ltac:(lia)).
        rewrite EQ, EQ'; simpl; intros (? & LE); subst.
        do 2 f_equal; auto.
        rewrite <- (IHd' 0); subst s'; simpl; rewrite EQ'.
        apply le_streamA_nth_approxA; auto. lia.
        transitivity (depth tl). lia. apply le_streamA_depth; auto. }
      specialize (stable_le s INC 1 (S n) ltac:(lia)).
      rewrite EQ, EQ'; simpl; intros (? & _); subst.
      do 2 f_equal; auto.
      rewrite <- (IHd' n); subst s'; simpl; rewrite EQ; auto. lia.
  Qed.

  Lemma stable_mkStream' {T} (s : nat → streamA T) (INC : stable s)
  : ∀ n, s n = nth_approx (mkStream' s) (depth (s n)).
  Proof.
    intros. erewrite <- stable_approx_mkStream'; auto.
    symmetry. apply nth_approxA_depth. auto.
  Qed.
End StreamTest.

Definition var := string.

Module simple.

Inductive shdw {vl} :=
  | Rd (x : var)
  | Ap (s : shdw) (v : vl)
.

Arguments shdw : clear implicits.

Inductive nv {vl} :=
  | Init
  | nv_bd (x : var) (v : vl) (σ : nv)
.

Arguments nv : clear implicits.

Inductive vl {tr} :=
  | vl_sh (s : shdw vl) (* s *)
  | vl_clos (x : var) (t : tr) (σ : nv vl) (* ⟨ λx.t, σ ⟩ *)
.

Arguments vl : clear implicits.

Definition shadow trace := shdw (vl trace).
Definition env trace := nv (vl trace).

Section ind.
  Context {T : Type}.
  Let Value := vl T.
  Let Env := env T.
  Let Shadow := shadow T.
  Context (Ptr : T → Prop) (tr_ind : ∀ t, Ptr t)
          (Pshdw : Shadow → Prop)
          (Pnv : Env → Prop)
          (Pvl : Value → Prop).
  Context (PRd : ∀ x, Pshdw (Rd x))
          (PAp : ∀ s v, Pshdw s → Pvl v → Pshdw (Ap s v)).
  Context (PInit : Pnv Init)
          (Pnv_bd : ∀ x v σ, Pvl v → Pnv σ → Pnv (nv_bd x v σ)).
  Context (Pvl_sh : ∀ s, Pshdw s → Pvl (vl_sh s))
          (Pvl_clos : ∀ x k σ, Ptr k → Pnv σ → Pvl (vl_clos x k σ)).

  Definition shdw_ind vl_ind :=
    fix go s : Pshdw s :=
      match s as s' return Pshdw s' with
      | Rd x => PRd x
      | Ap f v => PAp f v (go f) (vl_ind v)
      end.

  Definition nv_ind vl_ind :=
    fix go σ : Pnv σ :=
      match σ as σ' return Pnv σ' with
      | Init => PInit
      | nv_bd x v σ' => Pnv_bd x v σ' (vl_ind v) (go σ')
      end.

  Fixpoint vl_ind v : Pvl v :=
    match v as v' return Pvl v' with
    | vl_sh s => Pvl_sh s (shdw_ind vl_ind s)
    | vl_clos x t σ => Pvl_clos x t σ (tr_ind t) (nv_ind vl_ind σ)
    end.

  Lemma pre_val_ind :
    (∀ s, Pshdw s) ∧ (∀ σ, Pnv σ) ∧ (∀ v, Pvl v).
  Proof.
    pose proof (nv_ind vl_ind).
    pose proof (shdw_ind vl_ind).
    eauto using vl_ind.
  Qed.
End ind.

Inductive term :=
  | Var (x : var)
  | Lam (x : var) (t : term)
  | App (fn arg : term)
.

Definition term_ind P
  (PVar : ∀ x, P (Var x))
  (PLam : ∀ x e (IHbody : P e), P (Lam x e))
  (PApp : ∀ fn arg (IHfn : P fn) (IHarg : P arg), P (App fn arg)) :=
  fix go t :=
    match t as t' return P t' with
    | Var x => PVar x
    | Lam x e => PLam x e (go e)
    | App fn arg => PApp fn arg (go fn) (go arg)
    end.

Definition ω := Lam "x" (App (Var "x") (Var "x")).
Definition ι := Lam "x" (Var "x").
Definition fst' := Lam "x" (Lam "y" (Var "x")).

Inductive traceF {trace} :=
  | Stuck
  | Ret (v : vl trace)
  | Step (s : env trace) (k : traceF)
.

Arguments traceF : clear implicits.

(* Finite approximation, annotated with source term *)
Inductive trace := Tr (e : term) (k : nat → traceF trace).

Section trace_ind.
  Let Value := vl trace.
  Let Env := env trace.
  Let Shadow := shadow trace.
  Context (Pshdw : Shadow → Prop)
          (Pnv : Env → Prop)
          (Pvl : Value → Prop)
          (PtrF : traceF trace → Prop)
          (Ptr : trace → Prop).
  Context (PRd : ∀ x, Pshdw (Rd x))
          (PAp : ∀ s v (IHs : Pshdw s) (IHv : Pvl v), Pshdw (Ap s v)).
  Context (PInit : Pnv Init)
          (Pnv_bd : ∀ x v σ (IHv : Pvl v) (IHσ : Pnv σ), Pnv (nv_bd x v σ)).
  Context (Pvl_sh : ∀ s (IHs : Pshdw s), Pvl (vl_sh s))
          (Pvl_clos : ∀ x k σ (IHk : Ptr k) (IHσ : Pnv σ), Pvl (vl_clos x k σ)).
  Context (PStuck : PtrF Stuck)
          (PRet : ∀ v (IHv : Pvl v), PtrF (Ret v))
          (PStep : ∀ σ t (IHσ : Pnv σ) (IHt : PtrF t), PtrF (Step σ t)).
  Context (PTr : ∀ e t (IHt : ∀ n, PtrF (t n)), Ptr (Tr e t)).

  Definition traceF_ind (trace_ind : ∀ t, Ptr t) :=
    let vl_ind' := vl_ind _ trace_ind _ _ _
      PRd PAp
      PInit Pnv_bd
      Pvl_sh Pvl_clos in
    let nv_ind' := nv_ind _ _ PInit Pnv_bd vl_ind' in
    fix go (t : traceF trace) :=
    match t as k return PtrF k with
    | Stuck => PStuck
    | Ret v => PRet v (vl_ind' v)
    | Step σ t => PStep σ t (nv_ind' σ) (go t)
    end.

  Fixpoint trace_ind (t : trace) :=
    match t with
    | Tr e t => PTr e t (fun n => traceF_ind trace_ind (t n))
    end.

  Lemma val_ind :
    (∀ s, Pshdw s) ∧ (∀ σ, Pnv σ) ∧ (∀ v, Pvl v) ∧ (∀ tF, PtrF tF) ∧ (∀ t, Ptr t).
  Proof.
    pose proof
      (pre_val_ind _ trace_ind Pshdw Pnv Pvl
        PRd PAp
        PInit Pnv_bd
        Pvl_sh Pvl_clos).
    intuition auto.
    all: auto using traceF_ind, trace_ind.
  Qed.
End trace_ind.

Section rel.
  Definition rel_shdw {vl vl'}
    (rel_vl : vl → vl' → Prop) :=
    fix rel_s (s : shdw vl) (s' : shdw vl') : Prop :=
      match s with
      | Rd x =>
        match s' with
        | Rd x' => x = x'
        | _ => False
        end
      | Ap f v =>
        match s' with
        | Ap f' v' => rel_s f f' ∧ rel_vl v v'
        | _ => False
        end
      end.

  Definition rel_nv {vl vl'}
    (rel_vl : vl → vl' → Prop) :=
    fix rel_nv (σ : nv vl) (σ' : nv vl') : Prop :=
      match σ with
      | Init =>
        match σ' with
        | Init => True
        | _ => False
        end
      | nv_bd x v σ =>
        match σ' with
        | nv_bd x' v' σ' => x = x' ∧ rel_vl v v' ∧ rel_nv σ σ'
        | _ => False
        end
      end.

  Definition rel_vl {tr tr'}
    (rel_tr : tr → tr' → Prop) :=
    fix rel_v (v : vl tr) (v' : vl tr') :=
      match v with
      | vl_sh s =>
        match v' with
        | vl_sh s' => rel_shdw rel_v s s'
        | _ => False
        end
      | vl_clos x t σ =>
        match v' with
        | vl_clos x' t' σ' => x = x' ∧ rel_tr t t' ∧ rel_nv rel_v σ σ'
        | _ => False
        end
      end.

  Context {tr tr' : Type}
    (r r' : tr → tr' → Prop)
    (LEt : ∀ t t', r t t' → r' t t').

  Definition rel_shdw_monotone (s : shdw (vl tr)) :=
    ∀ s', rel_shdw (rel_vl r) s s' →
          rel_shdw (rel_vl r') s s'
  .
  Definition rel_nv_monotone (σ : nv (vl tr)) :=
    ∀ σ', rel_nv (rel_vl r) σ σ' → rel_nv (rel_vl r') σ σ'
  .
  Definition rel_vl_monotone (v : vl tr) :=
    ∀ v', rel_vl r v v' → rel_vl r' v v'
  .

  Lemma rel_monotone :
    (∀ s, rel_shdw_monotone s) ∧
    (∀ σ, rel_nv_monotone σ) ∧
    (∀ v, rel_vl_monotone v).
  Proof.
    apply (pre_val_ind _ (fun _ => I));
    cbv [rel_shdw_monotone rel_nv_monotone rel_vl_monotone];
    simpl; intros;
    match goal with
    | _ : match ?x with _ => _ end |- _ =>
      destruct x; intuition auto
    end.
  Qed.
End rel.

(* partial order between finite approximations *)
Definition le_traceF {tr}
  (le_tr : tr → tr → Prop) :=
  fix le_tF (t t' : traceF tr) :=
    let le_vl := rel_vl le_tr in
    match t with
    | Stuck => True
    | Ret v =>
      match t' with
      | Ret v' => le_vl v v'
      | _ => False
      end
    | Step σ k =>
      match t' with
      | Step σ' k' => rel_nv le_vl σ σ' ∧ le_tF k k'
      | _ => False
      end
    end.

Fixpoint le_trace (t t' : trace) :=
  match t with
  | Tr e k =>
    match t' with
    | Tr e' k' => e = e' ∧ ∀ n, ∃ m, le_traceF le_trace (k n) (k' m)
    end
  end.

Lemma le_trace_refl :
  let le_trF := le_traceF le_trace in
  let le_vl := rel_vl le_trace in
  let le_nv := rel_nv le_vl in
  let le_shdw := rel_shdw le_vl in
  (∀ s, le_shdw s s) ∧
  (∀ σ, le_nv σ σ) ∧
  (∀ v, le_vl v v) ∧
  (∀ t, le_trF t t) ∧
  (∀ t : trace, le_trace t t).
Proof. cbn zeta. apply val_ind; simpl; eauto. Qed.

Lemma le_trace_trans :
  let le_trF := le_traceF le_trace in
  let le_vl := rel_vl le_trace in
  let le_nv := rel_nv le_vl in
  let le_shdw := rel_shdw le_vl in
  (∀ s',
    ∀ s s'', le_shdw s s' → le_shdw s' s'' → le_shdw s s'') ∧
  (∀ σ',
    ∀ σ σ'', le_nv σ σ' → le_nv σ' σ'' → le_nv σ σ'') ∧
  (∀ v',
    ∀ v v'', le_vl v v' → le_vl v' v'' → le_vl v v'') ∧
  (∀ tF',
    ∀ tF tF'', le_trF tF tF' → le_trF tF' tF'' → le_trF tF tF'') ∧
  (∀ t',
    ∀ t t'', le_trace t t' → le_trace t' t'' → le_trace t t'').
Proof.
  cbn zeta. apply val_ind; simpl; intros;
  match goal with
  | |- rel_shdw _ ?s ?s'' =>
    destruct s; simpl in *; intuition eauto;
    subst; destruct s''; intuition eauto
  | |- rel_nv _ ?σ ?σ'' =>
    destruct σ; simpl in *; intuition eauto;
    subst; destruct σ''; intuition eauto
  | |- rel_vl _ ?v ?v'' =>
    destruct v; simpl in *; intuition eauto;
    subst; destruct v''; intuition eauto
  | |- le_traceF _ ?tF ?tF'' =>
    destruct tF; simpl in *; intuition eauto;
    subst; destruct tF''; intuition eauto
  | |- le_trace ?t ?t'' =>
    destruct t; simpl in *; intuition eauto;
    subst; destruct t''; intuition eauto
  end.
  match reverse goal with
  | H : _ |- _ => destruct (H n) as (m & ?)
  end.
  match goal with
  | H : _ |- _ => destruct (H m) as (? & ?)
  end.
  eauto.
Qed.

Section link.
  Context {trace : Type}.
  Context {T : Type}.
  Context (link_trace : env trace → trace → (vl trace → T) → T).

  Definition rd x :=
    fix rd (σ : env trace) :=
      match σ with
      | Init => vl_sh (Rd x)
      | nv_bd x' v σ' =>
        if x =? x' then v else rd σ'
      end.

  Lemma rd_monotone {r} x σ σ' (REL : rel_nv (rel_vl r) σ σ') :
    rel_vl r (rd x σ) (rd x σ').
  Proof.
    revert σ σ' REL.
    refine (fix go σ :=
      match σ with
      | Init => fun σ' =>
        match σ' with
        | Init => _
        | _ => _
        end
      | nv_bd x v σ => fun σ' =>
        match σ' with
        | nv_bd x' v' σ' => _
        | _ => _
        end
      end); simpl; try solve [destruct 1]; auto.
    intros (? & RELv & RELσ); subst.
    destruct (_ =? _); auto.
  Qed.

  Definition link_shdw link_value σ0 :=
    fix link (s : shadow trace) k : T :=
      match s with
      | Rd x => k (rd x σ0)
      | Ap s' v =>
        let k_s f :=
          let k_v a :=
            match f with
            | vl_sh f' => k (vl_sh (Ap f' a))
            | vl_clos x k' σ => link_trace (nv_bd x a σ) k' k
            end
          in link_value v k_v
        in link s' k_s
      end.

  Definition link_nv link_value (σ0 : env trace) :=
    fix link (σ : env trace) k : T :=
      match σ with
      | Init => k σ0
      | nv_bd x v σ' =>
        let k_v v' :=
          let k_σ σ'' := k (nv_bd x v' σ'')
          in link σ' k_σ
        in link_value v k_v
      end.

  Definition link_vl σ0 :=
    fix link (v : vl trace) k : T :=
      match v with
      | vl_sh s => link_shdw link σ0 s k
      | vl_clos x t σ =>
        let k_σ σ' := k (vl_clos x t σ')
        in link_nv link σ0 σ k_σ
      end.
End link.

Definition link_tr link σ0 :=
  fix go (t : traceF trace) k {struct t} :=
    let link_value := link_vl link in
    match t with
    | Stuck => Stuck
    | Ret v => link_value σ0 v k
    | Step σ t' =>
      let k_σ σ' := Step σ' (go t' k) in
      link_nv (link_value σ0) σ0 σ k_σ
    end.

Fixpoint link_trace n :=
  match n with
  | 0 => fun _ _ _ => Stuck
  | S n' =>
    link_tr (fun σ0 '(Tr _ t') => link_trace n' σ0 (t' n'))
  end.

Definition link_value n :=
  link_vl (fun σ0 '(Tr _ t') => link_trace n σ0 (t' n))
.

Definition link_env n :=
  fun σ0 => link_nv (link_value n σ0) σ0
.

Definition link_shadow n :=
  fun σ0 => link_shdw
    (fun σ0 '(Tr _ t') => link_trace n σ0 (t' n))
    (link_value n σ0)
    σ0
.

Fixpoint denote (t : term) k {struct t} : nat → traceF trace :=
  match t with
  | Var x => fun _ =>
    let r := vl_sh (Rd x) in
    Step Init (k r)
  | Lam x e => fun n =>
    let E := Tr e (denote e Ret) in
    let r := vl_clos x E Init in
    Step Init (k r)
  | App fn arg => fun n =>
    let k_fn f :=
      let k_arg a :=
        match f with
        | vl_sh f' => k (vl_sh (Ap f' a))
        | vl_clos x (Tr _ t') σ =>
          link_trace n (nv_bd x a σ) (t' n) k
        end in
      denote arg k_arg n in
    Step Init (denote fn k_fn n)
  end.

(* traditional *)
Inductive value :=
  | value_clos (x : var) (e : term) (σ : list (var * value))
.

Definition rd' x :=
  fix read (σ : list (var * value)) :=
  match σ with
  | [] => None
  | (x', v) :: σ' =>
    if x =? x' then Some v else read σ'
  end.

Definition ev ev :=
  fix go t (k : _ → option value) :=
  match t with
  | Var x => fun σ =>
    match rd' x σ with
    | None => None
    | Some r => k r
    end
  | Lam x e => fun σ => k (value_clos x e σ)
  | App fn arg => fun σ =>
    let k_fn f :=
      let k_arg a :=
        match f with
        | value_clos x e σ' =>
          ev e k ((x, a) :: σ')
        end in
      go arg k_arg σ in
    go fn k_fn σ
  end.

Fixpoint eval n :=
  match n with
  | 0 => fun _ _ _ => None
  | S n' => ev (eval n')
  end.

Definition lift_shdw lift_vl n :=
  fix go (s : shadow trace) :=
    match s with
    | Rd x => fun σ0 => rd' x σ0
    | Ap s v => fun σ0 =>
      match lift_vl v σ0 with
      | Some a =>
        match go s σ0 with
        | Some (value_clos x e σ) =>
          eval n e Some ((x, a) :: σ)
        | None => None
        end
      | None => None
      end
    end.

Definition lift_nv lift_vl :=
  fix go (σ : env trace) :=
    match σ with
    | Init => @Some (list (var * value))
    | nv_bd x v σ' => fun σ0 =>
      match lift_vl v σ0 with
      | Some v' =>
        match go σ' σ0 with
        | Some σ'' => Some ((x, v') :: σ'')
        | None => None
        end
      | None => None
      end
    end.

Definition lift_vl n :=
  fix go (v : vl trace) :=
    match v with
    | vl_sh s => lift_shdw go n s
    | vl_clos x (Tr e _) σ => fun σ0 =>
      match lift_nv go σ σ0 with
      | Some σ' => Some (value_clos x e σ')
      | None => None
      end
    end.

Definition lift_shadow n := lift_shdw (lift_vl n) n.
Definition lift_env n := lift_nv (lift_vl n).

Definition lift_trace n :=
  fix go (t : traceF trace) :=
    match t with
    | Stuck => fun _ => None
    | Ret v => lift_vl n v
    | Step σ t' => fun σ0 =>
      match lift_env n σ σ0 with
      | Some _ => go t' σ0
      | None => None
      end
    end.

Lemma ev_monotonicity : ∀ e k k' σ v f f'
  (K_MONO : ∀ v w, k v = Some w → k' v = Some w)
  (EVAL_MONO : ∀ e k k' σ v,
    (∀ v w, k v = Some w → k' v = Some w) →
    f e k σ = Some v → f' e k' σ = Some v)
  (EVAL : ev f e k σ = Some v),
  ev f' e k' σ = Some v.
Proof.
  induction e; simpl; auto.
  { intros. destruct (rd' x σ); auto. }
  intros.
  eapply IHe1; eauto. simpl.
  intros u w EVAL'.
  eapply IHe2; eauto. simpl.
  intros v' w'. destruct u. eauto.
Qed.

Lemma eval_monotonicity : ∀ m n (GE : m ≤ n) e k k' σ v
  (K_MONO : ∀ v w, k v = Some w → k' v = Some w)
  (EVAL : eval m e k σ = Some v),
  eval n e k' σ = Some v.
Proof.
  induction m; simpl; [congruence|].
  intros [|n]. lia.
  intros.
  eapply ev_monotonicity with (f := eval m) (f' := eval n); eauto.
  intros. eapply IHm; eauto. lia.
Qed.

Definition bind_link_shdw n s :=
  ∀ σ0 Σ0 σ1 Σ1 k k'
    (WF : ∀ v0' v1'
      (LIFT : lift_vl v0' Σ0 = lift_vl v1' Σ1)
      (VALID : lift_vl v0' Σ0 ≠ None),
      lift_trace (k v0') Σ0 = lift_trace (k' v1') Σ1)
    (LIFTΣ : lift_env σ0 Σ0 = lift_env σ1 Σ1)
    (VALIDΣ : lift_env σ0 Σ0 ≠ None),
    lift_trace (link_shadow n σ0 s k) Σ0 =
    lift_trace (link_shadow n σ1 s k') Σ1
  .

Definition bind_link_nv n σ :=
  ∀ σ0 Σ0 σ1 Σ1 k k'
    (WF : ∀ σ0' σ1'
      (LIFT : lift_env σ0' Σ0 = lift_env σ1' Σ1)
      (VALID : lift_env σ0' Σ0 ≠ None),
      lift_trace (k σ0') Σ0 = lift_trace (k' σ1') Σ1)
    (LIFTΣ : lift_env σ0 Σ0 = lift_env σ1 Σ1)
    (VALIDΣ : lift_env σ0 Σ0 ≠ None),
    lift_trace (link_env n σ0 σ k) Σ0 =
    lift_trace (link_env n σ1 σ k') Σ1
  .

Definition bind_link_vl n v :=
  ∀ σ0 Σ0 σ1 Σ1 k k'
    (WF : ∀ v0' v1'
      (LIFT : lift_vl v0' Σ0 = lift_vl v1' Σ1)
      (VALID : lift_vl v0' Σ0 ≠ None),
      lift_trace (k v0') Σ0 = lift_trace (k' v1') Σ1)
    (LIFTΣ : lift_env σ0 Σ0 = lift_env σ1 Σ1)
    (VALIDΣ : lift_env σ0 Σ0 ≠ None),
    lift_trace (link_value n σ0 v k) Σ0 =
    lift_trace (link_value n σ1 v k') Σ1
  .

Definition bind_link_tr n t :=
  ∀ σ0 Σ0 σ1 Σ1 k k'
    (WF : ∀ v0' v1'
      (LIFT : lift_vl v0' Σ0 = lift_vl v1' Σ1)
      (VALID : lift_vl v0' Σ0 ≠ None),
      lift_trace (k v0') Σ0 = lift_trace (k' v1') Σ1)
    (LIFTΣ : lift_env σ0 Σ0 = lift_env σ1 Σ1)
    (VALIDΣ : lift_env σ0 Σ0 ≠ None),
    lift_trace (link_trace n σ0 t k) Σ0 =
    lift_trace (link_trace n σ1 t k') Σ1
  .

Lemma bind_link m : ∀ n (LE : n ≤ m),
  (∀ s, bind_link_shdw n s) ∧
  (∀ σ, bind_link_nv n σ) ∧
  (∀ v, bind_link_vl n v) ∧
  (∀ t, bind_link_tr n t) ∧
  (∀ t, match t with Tr _ t' => bind_link_tr n t' end).
Proof.
  induction m.
  { intros. assert (n = 0) by lia. subst.
    cbv [bind_link_shdw bind_link_nv bind_link_vl bind_link_tr].
    simpl. intuition auto. destruct t; auto. }
  intro. destruct n.
  { cbv [bind_link_shdw bind_link_nv bind_link_vl bind_link_tr].
    simpl. intuition auto. destruct t; auto. }
  intro. apply PeanoNat.Nat.succ_le_mono in LE.
  specialize (IHm _ LE).
  destruct IHm as (IHms & IHmσ & IHmv & IHmtF & IHmt).
  apply val_ind; intros;
  cbv [bind_link_shdw bind_link_nv bind_link_vl bind_link_tr] in *;
  simpl; intros; auto.
  - apply WF. all: admit.
  - apply IHs; auto. intros.
    apply IHmv; auto. intros.
    destruct v0'. { simpl in VALID. congruence. }
    destruct v1'. { rewrite LIFT in VALID. simpl in *; congruence. }
    destruct t, t0.
    apply IHmtF.
    { destruct v1'; simpl in LIFT. apply WF; auto.
      destruct t. simpl in 
      change (lift_nv lift_vl σ Σ1) with (lift_env σ Σ1) in LIFT.
      destruct (lift_env σ Σ1) eqn:LIFTΣ'. congruence.
      simpl in VALID. congruence.
      
      destruct (lift_nv σ Σ1) in LIFT. }
  apply IHv; auto. intros.
    apply LIFT.
  - apply IHv; auto. intros. apply IHσ; auto.
    intros. apply WF; auto. simpl.
    rewrite LIFT, LIFT0. auto.
  - `:with`
Abort.

Lemma test' : ∀ n t k k' σ v
  (EVAL : eval n t k' σ = Some v),
  lift_trace (denote t k n) σ = Some v.
Proof.
  induction n. simpl. congruence.
  induction t; simpl.
Abort.
Module judg.
(* Judgment *)
Variant judgF {judg} :=
  | Stuck
  | Ret (v : value judg)
  | AppJ (fn arg body : judg)
.

Arguments judgF : clear implicits.

Inductive judg := mkJudg (j : judgF judg).

Definition on_ret k :=
  fix go (j : judg) {struct j} :=
    let '(mkJudg j') := j in
    match j' with
    | Stuck => mkJudg Stuck
    | Ret v => k v
    | AppJ _ _ body => go body
    end.

Definition link_j link σ0 :=
  let stuck := mkJudg Stuck in
  let ret v := mkJudg (Ret v) in
  let appj f a b := mkJudg (AppJ f a b) in
  fix go (j : judg) k {struct j} :=
    let '(mkJudg j') := j in
    match j' with
    | Stuck => stuck
    | Ret v => link_vl stuck link σ0 v k
    | AppJ fn arg _ =>
      let fn' := go fn ret in
      let arg' := go arg ret in
      let k_fn f :=
        let k_arg a :=
          match f with
          | vl_sh s => k (vl_sh (Ap s a))
          | vl_clos x k' σ => link (nv_bd x a σ) k' k
          end
        in on_ret k_arg arg'
      in appj fn' arg' (on_ret k_fn fn')
    end.

Definition link_judg :=
  let stuck := mkJudg Stuck in
  fix go n :=
    match n with
    | 0 => fun _ _ _ => stuck
    | S n' => link_j (go n')
    end.

Definition denote_judg :=
  let stuck := mkJudg Stuck in
  let ret v := mkJudg (Ret v) in
  let appj f a b := mkJudg (AppJ f a b) in
  fix go (t : term) k : nat → judg :=
    match t with
    | Var x => fun _ =>
      let r := vl_sh (Rd x)
      in k r
    | Lam x e => fun n =>
      let r := vl_clos x (go e ret n) Init
      in k r
    | App fn arg => fun n =>
      let fn' := go fn ret n in
      let arg' := go arg ret n in
      let k_fn f :=
        let k_arg a :=
          match f with
          | vl_sh f' => k (vl_sh (Ap f' a))
          | vl_clos x k' σ => link_judg n (nv_bd x a σ) k' k
          end
        in on_ret k_arg arg'
      in appj fn' arg' (on_ret k_fn fn')
    end.

(* Compute denote_judg (App (App fst' (App ω ω)) ι) (fun r => mkJudg (Ret r)) 2. *)
End judg.

(* Prove that there exists a unique coinductive tree for every ω chain *)
End simple.

Definition loc := positive.

Inductive shdw {nv wvl} :=
  | Init
  | Rd (s : shdw) (σ : nv) (x : var)
  | Ap (s : shdw) (w : wvl)
.

Arguments shdw : clear implicits.

Inductive nv {wvl} :=
  | nv_sh (s : shdw nv wvl) (* [s] *)
  | nv_one (x : var) (w : wvl) (* x ↦ w *)
  | nv_mrg (σ σ' : nv) (* σ ;; σ' *)
.

Arguments nv : clear implicits.

Variant vl {P wvl tr} :=
  | vl_prim (p : P) (* primitive Value *)
  | vl_nv (σ : nv wvl)
  | vl_sh (s : shdw (nv wvl) wvl) (* s *)
  | vl_clos (x : var) (t : tr) (σ : nv wvl) (* ⟨ λx.t, σ ⟩ *)
.

Arguments vl : clear implicits.

Inductive wvl {P tr} :=
  | wvl_v (v : vl P wvl tr) (* v *)
  | wvl_recv (v : vl P wvl tr) (* μℓ.v *)
  | wvl_floc (ℓ : loc) (* free location *)
  | wvl_bloc (n : nat) (* bound location *)
.

Arguments wvl : clear implicits.

Variant traceF {P trace} :=
  | Stuck
  | Ret (w : wvl P trace)
  | Step (σ : nv (wvl P trace)) (t : trace)
.

Arguments traceF : clear implicits.

(* Finite approximation *)
Inductive trace' {P} := mkTrace' (k : traceF P trace').
Definition obs_tr' {P} (t : @trace' P) :=
  match t with
  | mkTrace' k => k
  end.

(* Infinite tree *)
CoInductive trace {P} := mkTrace { obs_tr : traceF P trace }.

Arguments trace' : clear implicits.
Arguments trace : clear implicits.
Arguments mkTrace {_} _.

Definition walue := wvl.
Definition env P trace := nv (walue P trace).
Definition shadow P trace := shdw (env P trace) (walue P trace).
Definition value P trace := vl P (walue P trace) trace.

Definition Walue' P := walue P (trace' P).
Definition Walue P := walue P (trace P).
Definition Env' P := env P (trace' P).
Definition Env P := env P (trace P).
Definition Shadow' P := shadow P (trace' P).
Definition Shadow P := shadow P (trace P).
Definition Value' P := value P (trace' P).
Definition Value P := value P (trace P).

Notation stuck' := (mkTrace' Stuck) (only parsing).
Notation stuck := (mkTrace Stuck) (only parsing).
Notation ret' w := (mkTrace' (Ret w)) (only parsing).
Notation ret w := (mkTrace (Ret w)) (only parsing).
Notation step' σ t := (mkTrace' (Step σ t)) (only parsing).
Notation step σ t := (mkTrace (Step σ t)) (only parsing).

Section ind.
  Context {P tr : Type}.
  Let Walue := walue P tr.
  Let Value := value P tr.
  Let Env := env P tr.
  Let Shadow := shadow P tr.
  Context (Ptr : tr → Prop) (tr_ind : ∀ k, Ptr k)
          (Pshdw : Shadow → Prop)
          (Pnv : Env → Prop)
          (Pvl : Value → Prop)
          (Pwvl : Walue → Prop).
  Context (PInit : Pshdw Init)
          (PRd : ∀ s σ x, Pshdw s → Pnv σ → Pshdw (Rd s σ x))
          (PAp : ∀ s w, Pshdw s → Pwvl w → Pshdw (Ap s w)).
  Context (Pnv_sh : ∀ s, Pshdw s → Pnv (nv_sh s))
          (Pnv_one : ∀ x w, Pwvl w → Pnv (nv_one x w))
          (Pnv_mrg : ∀ σ σ', Pnv σ → Pnv σ' -> Pnv (nv_mrg σ σ')).
  Context (Pvl_prim : ∀ p, Pvl (vl_prim p))
          (Pvl_nv : ∀ σ, Pnv σ → Pvl (vl_nv σ))
          (Pvl_sh : ∀ s, Pshdw s → Pvl (vl_sh s))
          (Pvl_clos : ∀ x k σ, Ptr k → Pnv σ → Pvl (vl_clos x k σ)).
  Context (Pwvl_v : ∀ v, Pvl v → Pwvl (wvl_v v))
          (Pwvl_recv : ∀ v, Pvl v → Pwvl (wvl_recv v))
          (Pwvl_floc : ∀ ℓ, Pwvl (wvl_floc ℓ))
          (Pwvl_bloc : ∀ n, Pwvl (wvl_bloc n)).

  Definition shdw_ind nv_ind wvl_ind :=
    fix go s : Pshdw s :=
      match s as s' return Pshdw s' with
      | Init => PInit
      | Rd s σ x => PRd s σ x (go s) (nv_ind σ)
      | Ap f w => PAp f w (go f) (wvl_ind w)
      end.

  Definition nv_ind wvl_ind :=
    fix go σ : Pnv σ :=
      match σ as σ' return Pnv σ' with
      | nv_sh s => Pnv_sh s (shdw_ind go wvl_ind s)
      | nv_one x w => Pnv_one x w (wvl_ind w)
      | nv_mrg σ1 σ2 => Pnv_mrg σ1 σ2 (go σ1) (go σ2)
      end.

  Definition vl_ind wvl_ind v : Pvl v :=
    match v as v' return Pvl v' with
    | vl_prim p => Pvl_prim p
    | vl_nv σ => Pvl_nv σ (nv_ind wvl_ind σ)
    | vl_sh s => Pvl_sh s (shdw_ind (nv_ind wvl_ind) wvl_ind s)
    | vl_clos x t σ => Pvl_clos x t σ (tr_ind t) (nv_ind wvl_ind σ)
    end.

  Fixpoint wvl_ind w : Pwvl w :=
    match w with
    | wvl_v v => Pwvl_v v (vl_ind wvl_ind v)
    | wvl_recv v => Pwvl_recv v (vl_ind wvl_ind v)
    | wvl_floc ℓ => Pwvl_floc ℓ
    | wvl_bloc n => Pwvl_bloc n
    end.

  Lemma pre_val_ind :
    (∀ s, Pshdw s) ∧ (∀ σ, Pnv σ) ∧ (∀ v, Pvl v) ∧ (∀ w, Pwvl w).
  Proof.
    pose proof (nv_ind wvl_ind).
    pose proof (vl_ind wvl_ind).
    pose proof (shdw_ind (nv_ind wvl_ind) wvl_ind).
    eauto using wvl_ind.
  Qed.
End ind.

Section trace'_ind.
  Context {P : Type}.
  Let tr := trace' P.
  Let Walue := walue P tr.
  Let Value := value P tr.
  Let Env := env P tr.
  Let Shadow := shadow P tr.
  Context (Ptr : tr → Prop)
          (Pshdw : Shadow → Prop)
          (Pnv : Env → Prop)
          (Pvl : Value → Prop)
          (Pwvl : Walue → Prop).
  Context (PInit : Pshdw Init)
          (PRd : ∀ s σ x, Pshdw s → Pnv σ → Pshdw (Rd s σ x))
          (PAp : ∀ s w, Pshdw s → Pwvl w → Pshdw (Ap s w)).
  Context (Pnv_sh : ∀ s, Pshdw s → Pnv (nv_sh s))
          (Pnv_one : ∀ x w, Pwvl w → Pnv (nv_one x w))
          (Pnv_mrg : ∀ σ σ', Pnv σ → Pnv σ' -> Pnv (nv_mrg σ σ')).
  Context (Pvl_prim : ∀ p, Pvl (vl_prim p))
          (Pvl_nv : ∀ σ, Pnv σ → Pvl (vl_nv σ))
          (Pvl_sh : ∀ s, Pshdw s → Pvl (vl_sh s))
          (Pvl_clos : ∀ x k σ, Ptr k → Pnv σ → Pvl (vl_clos x k σ)).
  Context (Pwvl_v : ∀ v, Pvl v → Pwvl (wvl_v v))
          (Pwvl_recv : ∀ v, Pvl v → Pwvl (wvl_recv v))
          (Pwvl_floc : ∀ ℓ, Pwvl (wvl_floc ℓ))
          (Pwvl_bloc : ∀ n, Pwvl (wvl_bloc n)).
  Context (Pstuck : Ptr stuck')
          (Pret : ∀ w, Pwvl w → Ptr (ret' w))
          (Pstep : ∀ σ t, Pnv σ → Ptr t → Ptr (step' σ t)).

  Fixpoint trace'_ind (t : tr) : Ptr t :=
    let wvl_ind' := wvl_ind _ trace'_ind _ _ _ _
      PInit PRd PAp
      Pnv_sh Pnv_one Pnv_mrg
      Pvl_prim Pvl_nv Pvl_sh Pvl_clos
      Pwvl_v Pwvl_recv Pwvl_floc Pwvl_bloc in
    let nv_ind' := nv_ind _ _ _
      PInit PRd PAp
      Pnv_sh Pnv_one Pnv_mrg wvl_ind' in
    match t with
    | mkTrace' k =>
      match k as k' return Ptr (mkTrace' k') with
      | Stuck => Pstuck
      | Ret w => Pret w (wvl_ind' w)
      | Step σ t => Pstep σ t (nv_ind' σ) (trace'_ind t)
      end
    end.

  Lemma val'_ind :
    (∀ s, Pshdw s) ∧ (∀ σ, Pnv σ) ∧ (∀ v, Pvl v) ∧ (∀ w, Pwvl w) ∧ (∀ t, Ptr t).
  Proof.
    pose proof
      (pre_val_ind (tr := tr) Ptr trace'_ind Pshdw Pnv Pvl Pwvl
        PInit PRd PAp
        Pnv_sh Pnv_one Pnv_mrg
        Pvl_prim Pvl_nv Pvl_sh Pvl_clos
        Pwvl_v Pwvl_recv Pwvl_floc Pwvl_bloc).
    intuition auto.
    apply trace'_ind.
  Qed.
End trace'_ind.

Section map.
  Definition map_shdw {wvl wvl'}
    (map_wvl : wvl → wvl')
    (map_nv : nv wvl → nv wvl') :=
    fix map_s (s : shdw (nv wvl) wvl) : shdw (nv wvl') wvl' :=
      match s with
      | Init => Init
      | Rd s' σ x => Rd (map_s s') (map_nv σ) x
      | Ap f w => Ap (map_s f) (map_wvl w)
      end.

  Definition map_nv {wvl wvl'}
    (map_wvl : wvl → wvl') :=
    fix map_nv (σ : nv wvl) : nv wvl' :=
      match σ with
      | nv_sh s => nv_sh (map_shdw map_wvl map_nv s)
      | nv_one x w => nv_one x (map_wvl w)
      | nv_mrg σ1 σ2 => nv_mrg (map_nv σ1) (map_nv σ2)
      end.

  Definition map_vl {P wvl wvl' tr tr'}
    (map_wvl : wvl → wvl')
    (map_tr : tr → tr')
    (v : vl P wvl tr) : vl P wvl' tr' :=
    match v with
    | vl_prim p => vl_prim p
    | vl_nv σ => vl_nv (map_nv map_wvl σ)
    | vl_sh s => vl_sh (map_shdw map_wvl (map_nv map_wvl) s)
    | vl_clos x t σ => vl_clos x (map_tr t) (map_nv map_wvl σ)
    end.

  Definition map_wvl {P tr tr'}
    (map_tr : tr → tr') :=
    fix map_w (w : wvl P tr) : wvl P tr' :=
      match w with
      | wvl_v v => wvl_v (map_vl map_w map_tr v)
      | wvl_recv v => wvl_recv (map_vl map_w map_tr v)
      | wvl_floc ℓ => wvl_floc ℓ
      | wvl_bloc ℓ => wvl_bloc ℓ
      end.
End map.

Section rel.
  Definition rel_shdw {wvl wvl'}
    (rel_wvl : wvl → wvl' → Prop)
    (rel_nv : nv wvl → nv wvl' → Prop) :=
    fix rel_s (s : shdw (nv wvl) wvl) (s' : shdw (nv wvl') wvl') : Prop :=
      match s with
      | Init => match s' with Init => True | _ => False end
      | Rd s σ x =>
        match s' with
        | Rd s' σ' x' => rel_s s s' ∧ rel_nv σ σ' ∧ x = x'
        | _ => False
        end
      | Ap f w =>
        match s' with
        | Ap f' w' => rel_s f f' ∧ rel_wvl w w'
        | _ => False
        end
      end.

  Definition rel_nv {wvl wvl'}
    (rel_wvl : wvl → wvl' → Prop) :=
    fix rel_nv (σ : nv wvl) (σ' : nv wvl') : Prop :=
      match σ with
      | nv_sh s =>
        match σ' with
        | nv_sh s' => rel_shdw rel_wvl rel_nv s s'
        | _ => False
        end
      | nv_one x w =>
        match σ' with
        | nv_one x' w' => x = x' ∧ rel_wvl w w'
        | _ => False
        end
      | nv_mrg σ1 σ2 =>
        match σ' with
        | nv_mrg σ1' σ2' => rel_nv σ1 σ1' ∧ rel_nv σ2 σ2'
        | _ => False
        end
      end.

  Definition rel_vl {P wvl wvl' tr tr'}
    (rel_wvl : wvl → wvl' → Prop)
    (rel_tr : tr → tr' → Prop)
    (v : vl P wvl tr) (v' : vl P wvl' tr') :=
    match v with
    | vl_prim p =>
      match v' with
      | vl_prim p' => p = p'
      | _ => False
      end
    | vl_nv σ =>
      match v' with
      | vl_nv σ' => rel_nv rel_wvl σ σ'
      | _ => False
      end
    | vl_sh s =>
      match v' with
      | vl_sh s' => rel_shdw rel_wvl (rel_nv rel_wvl) s s'
      | _ => False
      end
    | vl_clos x t σ =>
      match v' with
      | vl_clos x' t' σ' =>
        x = x' ∧ rel_tr t t' ∧ rel_nv rel_wvl σ σ'
      | _ => False
      end
    end.

  Definition rel_wvl {P tr tr'}
    (rel_tr : tr → tr' → Prop) :=
    fix rel_w (w : wvl P tr) (w' : wvl P tr') :=
      match w with
      | wvl_v v =>
        match w' with
        | wvl_v v' => rel_vl rel_w rel_tr v v'
        | _ => False
        end
      | wvl_recv v =>
        match w' with
        | wvl_recv v' => rel_vl rel_w rel_tr v v'
        | _ => False
        end
      (* Assume a fixed allocation function *)
      | wvl_floc ℓ => match w' with wvl_floc ℓ' => ℓ = ℓ' | _ => False end
      | wvl_bloc n => match w' with wvl_bloc n' => n = n' | _ => False end
      end.

  Context {P tr tr' : Type}
    (r r' : tr → tr' → Prop)
    (LEt : ∀ t t', r t t' → r' t t').

  Definition rel_shdw_monotone (s : shdw (nv (wvl P tr)) (wvl P tr)) :=
    ∀ s', rel_shdw (rel_wvl r) (rel_nv (rel_wvl r)) s s' →
          rel_shdw (rel_wvl r') (rel_nv (rel_wvl r')) s s'
  .
  Definition rel_nv_monotone (σ : nv (wvl P tr)) :=
    ∀ σ', rel_nv (rel_wvl r) σ σ' → rel_nv (rel_wvl r') σ σ'
  .
  Definition rel_vl_monotone (v : vl P (wvl P tr) tr) :=
    ∀ v', rel_vl (rel_wvl r) r v v' → rel_vl (rel_wvl r') r' v v'
  .
  Definition rel_wvl_monotone (w : wvl P tr) :=
    ∀ w', rel_wvl r w w' → rel_wvl r' w w'
  .

  Lemma rel_monotone :
    (∀ s, rel_shdw_monotone s) ∧
    (∀ σ, rel_nv_monotone σ) ∧
    (∀ v, rel_vl_monotone v) ∧
    (∀ w, rel_wvl_monotone w).
  Proof.
    apply (pre_val_ind _ (fun _ => I));
    cbv [rel_shdw_monotone rel_nv_monotone rel_vl_monotone rel_wvl_monotone];
    simpl; intros;
    match goal with
    | _ : match ?x with _ => _ end |- _ =>
      destruct x; intuition auto
    end.
  Qed.
End rel.

(* partial order between finite approximations *)
Definition le_trace' {P} :=
  fix le_t (t t' : trace' P) :=
    let le_wvl := rel_wvl le_t in
    match obs_tr' t with
    | Stuck => True
    | Ret w =>
      match obs_tr' t' with
      | Ret w' => le_wvl w w'
      | _ => False
      end
    | Step σ k =>
      match obs_tr' t' with
      | Step σ' k' => rel_nv le_wvl σ σ' ∧ le_t k k'
      | _ => False
      end
    end.

Lemma le_trace'_refl {P} :
  let le_wvl (w : Walue' P) := rel_wvl le_trace' w in
  let le_vl (v : Value' P) := rel_vl le_wvl le_trace' v in
  let le_nv (σ : Env' P) := rel_nv le_wvl σ in
  let le_shdw (s : Shadow' P) := rel_shdw le_wvl le_nv s in
  (∀ s, le_shdw s s) ∧
  (∀ σ, le_nv σ σ) ∧
  (∀ v, le_vl v v) ∧
  (∀ w, le_wvl w w) ∧
  (∀ t : trace' P, le_trace' t t).
Proof. cbn zeta. apply val'_ind; simpl; auto. Qed.

Lemma le_trace'_trans {P} :
  let le_wvl (w : Walue' P) := rel_wvl le_trace' w in
  let le_vl (v : Value' P) := rel_vl le_wvl le_trace' v in
  let le_nv (σ : Env' P) := rel_nv le_wvl σ in
  let le_shdw (s : Shadow' P) := rel_shdw le_wvl le_nv s in
  (∀ s' : Shadow' P,
    ∀ s s'', le_shdw s s' → le_shdw s' s'' → le_shdw s s'') ∧
  (∀ σ' : Env' P,
    ∀ σ σ'', le_nv σ σ' → le_nv σ' σ'' → le_nv σ σ'') ∧
  (∀ v' : Value' P,
    ∀ v v'', le_vl v v' → le_vl v' v'' → le_vl v v'') ∧
  (∀ w' : Walue' P,
    ∀ w w'', le_wvl w w' → le_wvl w' w'' → le_wvl w w'') ∧
  (∀ t' : trace' P,
    ∀ t t'', le_trace' t t' → le_trace' t' t'' → le_trace' t t'').
Proof.
  cbn zeta. apply val'_ind; simpl; intros;
  match goal with
  | |- rel_shdw _ _ ?s ?s'' =>
    destruct s; simpl in *; intuition eauto;
    on_ret; destruct s''; intuition eauto
  | |- rel_nv _ ?σ ?σ'' =>
    destruct σ; simpl in *; intuition eauto;
    on_ret; destruct σ''; intuition eauto
  | |- rel_vl _ _ ?v ?v'' =>
    destruct v; simpl in *; intuition eauto;
    on_ret; destruct v''; intuition eauto
  | |- rel_wvl _ ?w ?w'' =>
    destruct w; simpl in *; intuition eauto;
    on_ret; destruct w''; intuition eauto
  | |- le_trace' ?t ?t'' =>
    destruct t; simpl in *; intuition eauto;
    on_ret; destruct t''; intuition eauto
  end.
  - destruct k; simpl in *; intuition eauto.
  - destruct k; simpl in *; intuition eauto.
    destruct k0; simpl in *; intuition eauto.
  - destruct k; simpl in *; intuition eauto.
    destruct k0; simpl in *; intuition eauto.
Qed.

(* approx t' t : t' is a finite approximation of t *)
Definition approx {P} :=
  fix approx (t' : trace' P) (t : trace P) :=
    let approx_w := rel_wvl approx in
    match obs_tr' t' with
    | Stuck => True
    | Ret w' =>
      match obs_tr t with
      | Ret w => approx_w w' w
      | _ => False
      end
    | Step σ' k' =>
      match obs_tr t with
      | Step σ k => rel_nv approx_w σ' σ ∧ approx k' k
      | _ => False
      end
    end.

Variant eq_traceF {P} eq : trace P → trace P → Prop :=
  | eq_stuck : eq_traceF eq stuck stuck
  | eq_ret w w'
    (EQw : rel_wvl eq w w')
  : eq_traceF eq (ret w) (ret w')
  | eq_step σ σ' k k'
    (EQσ : rel_nv (rel_wvl eq) σ σ')
    (EQk : eq k k')
  : eq_traceF eq (step σ k) (step σ' k')
.

Arguments eq_traceF : clear implicits.

Lemma eq_traceF_monotone {P} : monotone2 (eq_traceF P).
Proof.
  repeat intro. inversion IN; try constructor; on_ret; auto.
  all: eapply rel_monotone; eauto.
Qed.

Hint Resolve eq_traceF_monotone : paco.
Definition eq_trace P := paco2 (eq_traceF P) bot2.

Fixpoint nth_trace {P} (n : nat) (t : trace P) : trace' P :=
  match n with
  | 0 => stuck'
  | S n' =>
    match obs_tr t with
    | Stuck => stuck'
    | Ret w =>
      let w' := map_wvl (nth_trace n') w in
      ret' w'
    | Step σ k =>
      let σ' := map_nv (map_wvl (nth_trace n')) σ in
      step' σ' (nth_trace n' k)
    end
  end.

Section subst.
  Context {P trace : Type}.
  Let Walue := walue P trace.
  Let Env := env P trace.
  Let Value := value P trace.
  Let Shadow := shadow P trace.

  (** Operations for on_retitution *)
  (* open the bound location i with ℓ *)
  Definition open_loc_shdw fw fn (i : nat) (ℓ : loc) :=
    fix open (s : shadow P trace) : Shadow :=
    match s with
    | Init => Init
    | Rd s σ x => Rd (open s) (fn σ) x
    | Ap s w => Ap (open s) (fw w)
    end.

  Definition open_loc_nv fw (i : nat) (ℓ : loc) :=
    fix open (σ : Env) :=
    match σ with
    | nv_sh s => nv_sh (open_loc_shdw fw open i ℓ s)
    | nv_one x w => nv_one x (fw w)
    | nv_mrg σ σ' => nv_mrg (open σ) (open σ') 
    end.

  Definition open_loc_vl fw (i : nat) (ℓ : loc) :=
    let open (v : Value) :=
      match v with
      | vl_prim p => vl_prim p
      | vl_nv σ => vl_nv (open_loc_nv fw i ℓ σ)
      | vl_sh s => vl_sh (open_loc_shdw fw (open_loc_nv fw i ℓ) i ℓ s)
      | vl_clos x k σ => vl_clos x k (open_loc_nv fw i ℓ σ)
      end in
    open.

  Fixpoint open_loc_walue (i : nat) (ℓ : loc) (w : Walue) : Walue :=
    match w with
    | wvl_v v => wvl_v (open_loc_vl (open_loc_walue i ℓ) i ℓ v)
    | wvl_recv v => wvl_recv (open_loc_vl (open_loc_walue (S i) ℓ) (S i) ℓ v)
    | wvl_bloc n => if Nat.eqb i n then wvl_floc ℓ else wvl_bloc n
    | wvl_floc ℓ => wvl_floc ℓ
    end.

  Definition open_loc_value i ℓ := open_loc_vl (open_loc_walue i ℓ) i ℓ.
  Definition open_loc_env i ℓ := open_loc_nv (open_loc_walue i ℓ) i ℓ.
  Definition open_loc_shadow i ℓ := open_loc_shdw (open_loc_walue i ℓ) (open_loc_env i ℓ).

  (* close the free location ℓ with the binding depth i *)
  Definition close_loc_shdw fw fn (i : nat) (ℓ : loc) :=
    fix close (s : shadow P trace) : Shadow :=
    match s with
    | Init => Init
    | Rd s σ x => Rd (close s) (fn σ) x
    | Ap s w => Ap (close s) (fw w)
    end.

  Definition close_loc_nv fw (i : nat) (ℓ : loc) :=
    fix close (σ : Env) :=
    match σ with
    | nv_sh s => nv_sh (close_loc_shdw fw close i ℓ s)
    | nv_one x w => nv_one x (fw w)
    | nv_mrg σ σ' => nv_mrg (close σ) (close σ') 
    end.

  Definition close_loc_vl fw (i : nat) (ℓ : loc) :=
    let close (v : Value) :=
      match v with
      | vl_prim p => vl_prim p
      | vl_nv σ => vl_nv (close_loc_nv fw i ℓ σ)
      | vl_sh s => vl_sh (close_loc_shdw fw (close_loc_nv fw i ℓ) i ℓ s)
      | vl_clos x k σ => vl_clos x k (close_loc_nv fw i ℓ σ)
      end in
    close.

  Fixpoint close_loc_walue (i : nat) (ℓ : loc) (w : Walue) : Walue :=
    match w with
    | wvl_v v => wvl_v (close_loc_vl (close_loc_walue i ℓ) i ℓ v)
    | wvl_recv v => wvl_recv (close_loc_vl (close_loc_walue (S i) ℓ) (S i) ℓ v)
    | wvl_bloc n => wvl_bloc n
    | wvl_floc ℓ' => if Pos.eqb ℓ ℓ' then wvl_bloc i else wvl_floc ℓ'
    end.

  Definition close_loc_value i ℓ := close_loc_vl (close_loc_walue i ℓ) i ℓ.
  Definition close_loc_env i ℓ := close_loc_nv (close_loc_walue i ℓ) i ℓ.
  Definition close_loc_shadow i ℓ := close_loc_shdw (close_loc_walue i ℓ) (close_loc_env i ℓ).

  (* open the bound location i with u *)
  Definition open_wvl_shdw fw fn (i : nat) (u : Walue) :=
    fix open (s : shadow P trace) : Shadow :=
    match s with
    | Init => Init
    | Rd s σ x => Rd (open s) (fn σ) x
    | Ap s w => Ap (open s) (fw w)
    end.

  Definition open_wvl_nv fw (i : nat) (u : Walue) :=
    fix open (σ : Env) :=
    match σ with
    | nv_sh s => nv_sh (open_wvl_shdw fw open i u s)
    | nv_one x w => nv_one x (fw w)
    | nv_mrg σ σ' => nv_mrg (open σ) (open σ') 
    end.

  Definition open_wvl_vl fw (i : nat) (u : Walue) :=
    let open (v : Value) :=
      match v with
      | vl_prim p => vl_prim p
      | vl_nv σ => vl_nv (open_wvl_nv fw i u σ)
      | vl_sh s => vl_sh (open_wvl_shdw fw (open_wvl_nv fw i u) i u s)
      | vl_clos x k σ => vl_clos x k (open_wvl_nv fw i u σ)
      end in
    open.

  Fixpoint open_wvl_walue (i : nat) (u : Walue) (w : Walue) : Walue :=
    match w with
    | wvl_v v => wvl_v (open_wvl_vl (open_wvl_walue i u) i u v)
    | wvl_recv v => wvl_recv (open_wvl_vl (open_wvl_walue (S i) u) (S i) u v)
    | wvl_bloc n => if Nat.eqb i n then u else wvl_bloc n
    | wvl_floc ℓ => wvl_floc ℓ
    end.

  Definition open_wvl_value i ℓ := open_wvl_vl (open_wvl_walue i ℓ) i ℓ.
  Definition open_wvl_env i ℓ := open_wvl_nv (open_wvl_walue i ℓ) i ℓ.
  Definition open_wvl_shadow i ℓ := open_wvl_shdw (open_wvl_walue i ℓ) (open_wvl_env i ℓ).
End subst.

(* Define : coinductive version of traces *)
(* Define : strong bisimilarity between traces *)
(* Define : depth-n approximation between traces *)
(* Prove : strong bisimilarity ↔ equality of approximation for all n *)
(* Conclusion : represent coinductive trace with a stream of "increasing" approximations *)
