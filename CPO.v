From Stdlib Require Import Utf8.
From Paco Require Import paco.

Set Primitive Projections.

Variant StreamF {T Stream} :=
| snil
| scons (hd : T) (tl : Stream)
| stau (tl : Stream)
.

Arguments StreamF : clear implicits.

CoInductive Stream {T} := mkStream { obs_st : StreamF T Stream }.

Arguments Stream : clear implicits.

Notation Snil := {| obs_st := snil |}.
Notation Scons hd tl := {| obs_st := scons hd tl |}.
Notation Stau tl := {| obs_st := stau tl |}.

(* define approximation order *)
Inductive le_StreamF {T le_Stream} (s s' : Stream T) : Prop :=
| le_snil
  (NIL : obs_st s = snil)
| le_scons_scons hd tl tl'
  (CONS : obs_st s = scons hd tl)
  (CONS' : obs_st s' = scons hd tl')
  (LE : le_Stream tl tl')
| le_stauL tl
  (TAU : obs_st s = stau tl)
  (LE : le_StreamF tl s')
| le_stauR tl'
  (TAU' : obs_st s' = stau tl')
  (LE : le_StreamF s tl')
| le_stauB tl tl'
  (TAU : obs_st s = stau tl)
  (TAU' : obs_st s' = stau tl')
  (LE : le_Stream tl tl')
.

Arguments le_StreamF {_} _ _ _.

Lemma le_StreamF_monotone T : monotone2 (@le_StreamF T).
Proof.
  repeat intro. induction IN.
  - econstructor 1; eauto.
  - econstructor 2; eauto.
  - econstructor 3; eauto.
  - econstructor 4; eauto.
  - econstructor 5; eauto.
Qed.

Hint Resolve le_StreamF_monotone : paco.

Definition le_Stream {T} := paco2 (@le_StreamF T) bot2.

Lemma le_Stream_refl {T} : ∀ s, le_Stream (T := T) s s.
Proof.
  pcofix CIH.
  intros. pfold. destruct (obs_st s) eqn:EQ.
  - econstructor 1; eauto.
  - econstructor 2; eauto.
  - econstructor 5; eauto.
Qed.

Lemma inv_tauL {T} :
  ∀ s s' (LE : le_Stream (T := T) s s') tl (TAUL : obs_st s = stau tl),
    le_Stream tl s'.
Proof.
  do 3 intro. punfold LE. induction LE.
  - intros. congruence.
  - intros. congruence.
  - intros. rewrite TAUL in *. inversion TAU; subst; clear TAU.
    pfold; auto.
  - intros. pfold. econstructor 4; eauto.
    specialize (IHLE _ TAUL). punfold IHLE.
  - intros. rewrite TAUL in *. inversion TAU; subst; clear TAU.
    pclearbot. pfold. econstructor 4; eauto. punfold LE.
Qed.

Lemma inv_tauR {T} :
  ∀ s s' (LE : le_Stream (T := T) s s') tl' (TAUR : obs_st s' = stau tl'),
    le_Stream s tl'.
Proof.
  do 3 intro. punfold LE. induction LE.
  - intros. pfold. econstructor 1; eauto.
  - intros. congruence.
  - intros. pfold. econstructor 3; eauto.
    specialize (IHLE _ TAUR). punfold IHLE.
  - intros. rewrite TAUR in *. inversion TAU'; subst; clear TAU'.
    pfold; auto.
  - intros. rewrite TAUR in *. inversion TAU'; subst; clear TAU'.
    pclearbot. pfold. econstructor 3; eauto. punfold LE.
Qed.

Lemma inv_nilR {T} :
  ∀ s s' s''
    (LE' : le_Stream (T := T) s' s'')
    (LE : le_Stream s s')
    (OBS : obs_st s'' = snil),
    le_Stream s s''.
Proof.
  pcofix CIH.
  do 4 intro. revert s. punfold LE'. induction LE'.
  - intros. pfold. clear CIH. revert s' OBS. rename s0 into s''.
    punfold LE. induction LE.
    + intros. econstructor 1; eauto.
    + congruence.
    + specialize (IHLE NIL). intros. econstructor 3; eauto.
    + congruence.
    + congruence.
  - intros. congruence.
  - intros. eapply IHLE'; eauto. eapply inv_tauR; eauto.
  - intros. congruence.
  - intros. congruence.
Qed.

Lemma inv_nil_all {T} :
  ∀ s s'
    (LE : le_Stream (T := T) s s')
    (OBS : obs_st s' = snil)
    s'',
    le_Stream s s''.
Proof.
  pcofix CIH.
  do 3 intro. punfold LE. induction LE.
  - intros. pfold. econstructor 1; eauto.
  - intros; congruence.
  - intros. pfold. econstructor 3; eauto. specialize (IHLE OBS s''). punfold IHLE.
  - intros. congruence.
  - intros; congruence.
Qed.

Lemma le_Stream_trans {T} :
  ∀ s s' s'',
    le_Stream (T := T) s s' → le_Stream s' s'' → le_Stream s s''.
Proof.
  pcofix CIH.
  do 3 intro. intros LE LE'. revert s'' LE'.
  punfold LE.
  induction LE.
  - intros. pfold. econstructor 1; eauto.
  - intros. pclearbot. punfold LE'. induction LE'; rewrite CONS' in *.
    + congruence.
    + inversion CONS0; subst; clear CONS0.
      pclearbot. pfold. econstructor 2; eauto.
    + congruence.
    + pfold. econstructor 4; eauto.
      specialize (IHLE' eq_refl).
      punfold IHLE'.
    + congruence.
  - intros. specialize (IHLE _ LE'). pfold. econstructor 3; eauto.
    punfold IHLE.
  - intros. eapply IHLE. eapply inv_tauL; eauto.
  - intros. pclearbot.
    assert (le_Stream s s') as LE'' by (pfold; econstructor 5; eauto).
    destruct (obs_st s'') as [|hd'' tl''|tl''] eqn:OBS.
    { specialize (inv_nilR s s' s'' LE' LE'' OBS).
      intros. eapply paco2_mon; eauto. destruct 1. }
    punfold LE'. revert hd'' tl'' OBS.
    clear tl tl' TAU TAU' LE.
    rename LE'' into LE.
    revert s LE.
    induction LE'; intros.
    + specialize (inv_nil_all _ _ LE NIL s').
      intros. eapply paco2_mon; eauto. destruct 1.
    + rewrite OBS in *. inversion CONS'; subst; clear CONS'.
      pclearbot. punfold LE0. revert LE0.
      induction 1.
      * pfold. econstructor 1; eauto.
      * rewrite CONS in *. inversion CONS'; subst; clear CONS'.
        pclearbot. pfold. econstructor 2; eauto.
      * pfold. econstructor 3; eauto. specialize (IHLE0 CONS). punfold IHLE0.
      * rewrite CONS in *. congruence.
      * rewrite CONS in *. congruence.
    + eapply IHLE'; eauto. clear IHLE' hd'' tl'' OBS LE' s'.
      revert tl TAU. punfold LE. induction LE; intros; try rewrite TAU in *.
      * pfold. econstructor 1; eauto.
      * congruence.
      * pfold. econstructor 3; eauto.
        specialize (IHLE _ TAU0). punfold IHLE.
      * inversion TAU'; subst; clear TAU'. pfold. auto.
      * rewrite TAU0 in *. inversion TAU'; subst; clear TAU'.
        pclearbot. pfold. econstructor 3; eauto. punfold LE.
    + congruence.
    + congruence.
    + pfold. econstructor 5; eauto. right. eapply CIH; eauto.
      eapply inv_tauL; eauto. eapply inv_tauR; eauto.
Qed.

