From iris.prelude Require Import options.
From iris.proofmode Require Import proofmode.
From stdpp Require Import gmap.

From Vellvm Require Import
  Syntax.DynamicTypes Handlers Utils.Util.

(* Util lemmas about uvalues and dvalues *)
Lemma uvalue_to_dvalue_list :
  forall fields,
    (forall u : uvalue,
        List.In u fields ->
        is_concrete u ->
        exists dv : dvalue, uvalue_to_dvalue u = inr dv /\
            concretize_uvalue u = Monad.ret dv) ->
    forallb is_concrete fields = true ->
    exists dfields, Util.map_monad uvalue_to_dvalue fields = inr dfields /\
                  Util.map_monad concretize_uvalue fields = Monad.ret dfields.
Proof.
  induction fields; intros H' ALL.
  - exists nil. split; reflexivity.
  - assert (List.In a (a :: fields)) as IN.
    { constructor; auto. }

    change (a :: fields) with ([a] ++ fields)%list in ALL.
    rewrite forallb_app in ALL.
    apply andb_prop in ALL as (CONC_A & CONC_FIELDS).

    cbn in CONC_A.
    rewrite Bool.andb_true_r in CONC_A.
    apply Is_true_true_2 in CONC_A.
    pose proof (H' a IN CONC_A) as (dv & CONV_A&?).

    assert
      (∀ u : uvalue,
        In u fields
        → is_concrete u
          → ∃ dv : dvalue, uvalue_to_dvalue u = inr dv ∧
                            concretize_uvalue u = Monad.ret dv) as HCONV.
    { intros u INFS CONCU.
      apply H'; auto.
      apply in_cons; auto. }

    pose proof (IHfields HCONV CONC_FIELDS) as (dfields & CONV_DFIELDS & CONV_DFIELDS').
    exists (dv :: dfields).

    change (a :: fields) with ([a] ++ fields)%list.
    rewrite map_monad_app.
    cbn.
    rewrite CONV_A CONV_DFIELDS CONV_DFIELDS' H.
    split; reflexivity.
Qed.

Lemma is_concrete_uvalue_to_dvalue :
  forall uv,
    is_concrete uv ->
    exists dv, uvalue_to_dvalue uv = inr dv /\
          concretize_uvalue uv = Monad.ret dv.
Proof.
  intros uv CONC.
  induction uv;
    try inversion CONC; try (eexists; split; reflexivity).
  - cbn in CONC. cbn.
    pose proof uvalue_to_dvalue_list _ H as (dv & MAP & MAP').
    { by apply Is_true_true_1. }
    exists (DVALUE_Struct dv). rewrite MAP MAP'. split; eauto.
  - cbn.
    pose proof uvalue_to_dvalue_list _ H as (dv & MAP & MAP').
    { by apply Is_true_true_1. }
    exists (DVALUE_Array dv). rewrite MAP MAP'; split; eauto.
Qed.

Lemma uvalue_to_dvalue_inv u dv:
  uvalue_to_dvalue u = inr dv ->
  u = dvalue_to_uvalue dv.
Proof.
  intros H. revert dv H.
  induction u; intros; try solve [inversion H; eauto].
  { cbn in H0.
    destruct (map_monad uvalue_to_dvalue fields) eqn : Hfields; inversion H0; subst.
    clear H0. cbn. f_equiv.
    revert l Hfields H.
    induction fields; intros; cbn in *; [ inversion Hfields; eauto | ].
    destruct (uvalue_to_dvalue a) eqn: Ha; [ inversion Hfields | ].
    destruct (map_monad uvalue_to_dvalue fields) eqn : Hfields'; inversion Hfields; subst.
    cbn. erewrite <-H; eauto.
    rewrite <-IHfields; eauto. }
  { cbn in H0.
    destruct (map_monad uvalue_to_dvalue elts) eqn : Hfields; inversion H0; subst.
    clear H0. cbn. f_equiv.
    revert l Hfields H.
    induction elts; intros; cbn in *; [ inversion Hfields; eauto | ].
    destruct (uvalue_to_dvalue a) eqn: Ha; [ inversion Hfields | ].
    destruct (map_monad uvalue_to_dvalue elts) eqn : Hfields'; inversion Hfields; subst.
    cbn. erewrite <-H; eauto.
    rewrite <-IHelts; eauto. }
  { cbn in *; inversion H0. }
Qed.

Lemma concretize_uvalue_dvalue_to_uvalue u:
  concretize_uvalue (dvalue_to_uvalue u) = Monad.ret u.
Proof.
  induction u; intros; eauto.
  { induction fields; cbn in *; eauto.
    assert (Ha : a = a ∨ In a fields) by eauto.
    pose proof (H a Ha) as H'.
    rewrite H'; cbn.
    assert
      (IHp :
        (∀ u : dvalue, In u fields →
          concretize_uvalue (dvalue_to_uvalue u) =
                {| EitherMonad.unEitherT := inr (inr u) |})).
    { intros; eauto. }
    specialize (IHfields IHp).
    inversion IHfields.
    destruct (EitherMonad.unEitherT
      (Util.map_monad concretize_uvalue (map dvalue_to_uvalue fields)));
      inversion H1.
    destruct s; inversion H1; subst; cbn. eauto. }

  { induction elts; cbn in *; eauto.
    assert (Ha : a = a ∨ In a elts) by eauto.
    pose proof (H a Ha) as H'. rewrite H'; cbn.
    assert
      (IHp :
        (∀ u : dvalue, In u elts →
            concretize_uvalue (dvalue_to_uvalue u) =
                {| EitherMonad.unEitherT := inr (inr u) |})).
    { intros; eauto. }
    specialize (IHelts IHp); inversion IHelts.
    destruct (EitherMonad.unEitherT
      (Util.map_monad concretize_uvalue (map dvalue_to_uvalue elts)));
      inversion H1.
    destruct s; inversion H1; subst; cbn. eauto. }
Qed.

Lemma concretize_uvalue_dvalue_to_uvalue_map l :
  Util.map_monad concretize_uvalue (map dvalue_to_uvalue l) = Monad.ret l.
Proof.
  induction l; eauto.
  cbn. rewrite concretize_uvalue_dvalue_to_uvalue; cbn.
  cbn in IHl.
  destruct (map_monad concretize_uvalue (map dvalue_to_uvalue l)), unEitherT, s;
    inversion IHl; subst; cbn; eauto.
Qed.

Lemma is_concrete_dvalue_to_uvalue v :
  is_concrete (dvalue_to_uvalue v) = true.
Proof.
  induction v; eauto; cbn.
  { induction fields; cbn; auto.
    rewrite H; [ | by constructor].
    rewrite andb_true_l.
    apply IHfields; intros; eauto.
    eapply H; by apply in_cons. }
  { induction elts; cbn; auto.
    rewrite H; [ | by constructor].
    rewrite andb_true_l.
    apply IHelts; intros; eauto.
    eapply H; by apply in_cons. }
Qed.

Lemma is_concrete_imples_uvalue_to_dvalue uv:
  is_concrete uv ->
  exists v, uvalue_to_dvalue uv = inr v.
Proof.
  induction uv; intros; try inversion H; eauto.
  { induction fields; eauto.
    cbn in H0. apply andb_True in H0.
    destruct H0.
    pose proof (H _ (in_eq _ _) H0) as Heq.
    cbn. destruct Heq. rewrite H2.
    assert
      (Hin:
        ∀ u : uvalue,
          In u fields →
          is_concrete u →
          ∃ v : dvalue, uvalue_to_dvalue u = inr v).
    { intros; eapply H; eauto; by apply in_cons. }
    specialize (IHfields Hin H1).
    destruct IHfields.
    cbn in H3.
    destruct (Util.map_monad uvalue_to_dvalue fields);
      subst; inversion H3; eauto. }
  { induction elts; eauto.
    cbn in H0. apply andb_True in H0.
    destruct H0.
    pose proof (H _ (in_eq _ _) H0) as Heq.
    cbn. destruct Heq. rewrite H2.
    assert
      (Hin:
        ∀ u : uvalue,
          In u elts →
          is_concrete u →
          ∃ v : dvalue, uvalue_to_dvalue u = inr v).
    { intros; eapply H; eauto; by apply in_cons. }
    specialize (IHelts Hin H1).
    destruct IHelts.
    cbn in H3.
    destruct (Util.map_monad uvalue_to_dvalue elts);
      subst; inversion H3; eauto. }
  inversion H0.
Qed.

Lemma is_concrete_dvalue_to_uvalue_map l:
  forallb is_concrete (map dvalue_to_uvalue l) = true.
Proof.
  rewrite forallb_forall; intros.
  rewrite in_map_iff in H. destruct H as (?&?&?); subst; eauto.
  apply is_concrete_dvalue_to_uvalue.
Qed.

Lemma is_concrete_concretize_uvalue u :
  is_concrete u ->
  exists x, concretize_uvalue u = Monad.ret x /\ u = dvalue_to_uvalue x.
Proof.
  induction u; intros; try solve [inversion H]; eauto.
  { induction fields; eauto.
    cbn in H0; cbn; rewrite andb_True in H0.
    destruct H0; eauto.
    destruct (H _ (in_eq _ _) H0) as (?&?&?).
    rewrite H2; clear H2; cbn; subst.
    assert
      (∀ u : uvalue,
        In u fields →
        is_concrete u →
        ∃ x : dvalue, concretize_uvalue u = Monad.ret x /\ u = dvalue_to_uvalue x).
    { intros; destruct (H _ (in_cons _ _ _ H2) H3) as (?&?&?); eauto. }
    specialize (IHfields H2 H1); clear H1 H2.
    destruct IHfields as (?&?&?). cbn in H1.
    inversion H1.
    destruct (Util.map_monad concretize_uvalue fields);
      destruct unEitherT, s; inversion H1; subst; cbn; eauto.
    eexists; split; [ done | ]. cbn; do 2 f_equiv.
    cbn in H2. by inversion H2. }

  { induction elts; eauto.
    cbn in H0; cbn; rewrite andb_True in H0.
    destruct H0; eauto.
    destruct (H _ (in_eq _ _) H0) as (?&?&?).
    rewrite H2; clear H2; cbn; subst.
    assert
      (∀ u : uvalue,
        In u elts →
        is_concrete u →
        ∃ x : dvalue, concretize_uvalue u = Monad.ret x /\ u = dvalue_to_uvalue x).
    { intros; destruct (H _ (in_cons _ _ _ H2) H3) as (?&?&?); eauto. }
    specialize (IHelts H2 H1); clear H1 H2.
    destruct IHelts as (?&?&?). cbn in H1.
    inversion H1.
    destruct (Util.map_monad concretize_uvalue elts);
      destruct unEitherT, s; inversion H1; subst; cbn; eauto.
    eexists; split; [ done | ]. cbn; do 2 f_equiv.
    cbn in H2. by inversion H2. }

  cbn in H0; inversion H0.
Qed.

Lemma forallb_is_concrete_concretize_uvalue fields:
  forallb is_concrete fields = true ->
  exists x, (Util.map_monad concretize_uvalue fields) = Monad.ret x.
Proof.
  induction fields; eauto.
  cbn. rewrite andb_true_iff.
  intros (?&?). apply Is_true_true_2 in H.
  apply is_concrete_concretize_uvalue in H; destruct H as (?&?&?).
  rewrite H; cbn.
  specialize (IHfields H0).
  destruct IHfields as (?&IHfields); rewrite IHfields; eauto.
Qed.

Lemma map_monad_dvalue_to_uvalue fields l k x:
  map_monad default_dvalue_of_dtyp fields = inr l ->
  l !! k = Some x ->
  exists v v',
    In v fields /\
    default_dvalue_of_dtyp v = inr v' /\
    x = v'.
Proof.
  revert l k x.
  induction fields; cbn; intros; inversion H;
    subst; [ inversion H0 | ].
  destruct (default_dvalue_of_dtyp a) eqn : Ha; [ inversion H | ].
  destruct (map_monad default_dvalue_of_dtyp fields) eqn: Hfields;
    inversion H; subst; clear H; cbn in H0.
  rewrite lookup_cons in H0.
  destruct k; inversion H0; subst; eauto; [ exists a, x ; eauto | ].
  specialize (IHfields l0 k x eq_refl H0).
  destruct IHfields as (?&?&?&?&?).
  eexists _, _; eauto.
Qed.
