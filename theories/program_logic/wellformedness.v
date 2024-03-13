From Coq Require Import Program.Equality.

From iris.prelude Require Import options.

From Paco Require Import paco.

From ITree Require Import ITree Eq.

From velliris.program_logic Require Import weakest_pre.
From velliris.utils Require Import no_event tactics.

Set Default Proof Using "Type*".

Section WF.

  Context {Λ : language}.

  (* proto-"Subevent" version of [no_event] *)
  (* The left part of the signature is absent *)
  Inductive has_event_F {E F X} (R : itree F X -> Prop) `{E -< F}: itree' F X -> Prop :=
    | has_event_tau: forall t, R t -> has_event_F R (TauF t)
    | has_event_later: forall {Y} (e: _ Y) k, (exists x, R (k x)) -> has_event_F R (VisF e k)
    | has_event_now: forall {Y} (e: E Y) k, has_event_F R (VisF (subevent _ e) k).
  Hint Constructors has_event_F : core.

  Lemma has_event_F_mono : forall {E F X} `{E -< F} (R1 R2 : itree F X -> Prop) (LE : R1 <1= R2),
      @has_event_F E F X R1 _ <1= @has_event_F E F X R2 _.
  Proof.
    intros.
    induction PR; auto. destruct H0; eauto.
  Qed.
  Hint Resolve has_event_F_mono : paco.

  Definition has_event_F_ {E F X} `{E -< F} R (t : itree F X) := @has_event_F E F X R _ (observe t).
  Hint Unfold has_event_F_ : core.

  (* Partial no-event: the tree does not trigger events of type [E] *)
  Definition has_event E {F X} `{E -< F}:= paco1 (@has_event_F_ E F X _) bot1.
  Definition does_not_trigger E {F X} `{E -< F} x := not (@has_event E F X _ x).

  Lemma does_not_trigger_tau_inv {R} (e_t : L2_expr Λ R) E `{E -< L2 Λ}:
    does_not_trigger E (Tau e_t) -> does_not_trigger E e_t.
  Proof.
    intros. unfold does_not_trigger in *.
    intro; apply H0. clear H0.
    pstep; constructor; auto.
  Qed.

  Lemma does_not_trigger_vis_inv {X R} {E : Type -> Type} (e : _ X) (k : _ -> L2_expr Λ R) `{E -< L2 Λ}:
    does_not_trigger E (Vis e k) -> forall v, does_not_trigger E (k v).
  Proof.
    intros. unfold does_not_trigger in *.
    intro; apply H0. clear H0.
    pstep; constructor; auto. exists v. intros; left.
    punfold H1.
  Qed.

  #[global] Instance has_event_Proper_impl {R E F} `{E -< F}:
    Proper (eq_itree (R2 := R) eq ==> impl) (has_event E (F := F)).
  Proof.
    repeat intro.
    revert x y H0 H1.
    pcofix CIH.
    intros. punfold H1.
    red in H1. pstep; red.
    remember (observe x); remember (observe y).
    revert x y Heqi Heqi0 H2.
    induction H1; intros; subst; eauto; pclearbot.
    - punfold H2. red in H2. rewrite <- Heqi in H2. inv H2.
    - constructor. right. eapply CIH.
      + exact REL.
      + punfold H2. red in H2. rewrite <- Heqi in H2.
        inv H2; pclearbot; auto.
    - intros.
      punfold H2. red in H2. rewrite <- Heqi in H2.
      inv H2; pclearbot; auto.
      { dependent destruction H3.
        dependent destruction H4.
        destruct H1; pclearbot.
        constructor.
        exists x0; right; eapply CIH; eauto.
        eapply REL. }
      { dependent destruction H3.
        dependent destruction H4.
        eapply has_event_now. }
    - punfold H2. red in H2.
      rewrite <- Heqi in H2. inv H2; pclearbot.
      eapply IHeqitF; eauto.
    - constructor; left; pstep. eapply IHeqitF; eauto.
  Qed.

  #[global] Instance has_event_Proper_iff {R E F} `{E -< F}:
    Proper (eq_itree (R2 := R) eq ==> iff) (has_event E (F := F)).
  Proof.
    split; eapply has_event_Proper_impl; eauto.
    by symmetry.
  Qed.

  #[global] Instance does_not_trigger_Proper_impl {R E F} `{E -< F}:
    Proper (eq_itree (R2 := R) eq ==> impl) (does_not_trigger E (F := F)).
  Proof.
    repeat intro.
    rewrite <- H0 in H2; auto.
  Qed.

  #[global] Instance does_not_trigger_Proper {R E F} `{E -< F}:
    Proper (eq_itree (R2 := R) eq ==> iff) (does_not_trigger E (F := F)).
  Proof.
    split; eapply does_not_trigger_Proper_impl; eauto.
    by symmetry.
  Qed.

  Definition no_call_events {R} (e_s : L2_expr Λ R) :=
    no_event_l e_s.
  Arguments no_call_events /.

  Definition closed {R} (e_t e_s : L2_expr Λ R) :=
    no_call_events e_t /\ no_call_events e_s.

  Definition well_behaved {R} (e_s: L2_expr Λ R) :=
    does_not_trigger (UB_events Λ) e_s
    /\ does_not_trigger (exc_events Λ) e_s.

  (* A well-formed source program does not contain undefined behavior or
    exception events, and both source and target programs have no remaining
    call events. *)
  Definition well_formed {R} (e_t e_s : L2_expr Λ R) :=
    well_behaved e_s /\ closed e_t e_s.

  Lemma closed_tau_invL {R} (e_t e_s: L2_expr Λ R):
    closed (Tau e_t) e_s -> closed e_t e_s.
  Proof.
    intros; destruct H.
    split; auto. clear H0.
    rewrite tau_eutt in H; auto.
  Qed.

  Lemma closed_tau_invR {R} (e_t e_s: L2_expr Λ R):
    closed e_t (Tau e_s) -> closed e_t e_s.
  Proof.
    intros; destruct H.
    split; auto. clear H.
    rewrite tau_eutt in H0; auto.
  Qed.

  Lemma well_formed_tau_invL {R} (e_t e_s: L2_expr Λ R):
    well_formed (Tau e_t) e_s -> well_formed e_t e_s.
  Proof.
    intros; inversion H. split; auto.
    apply closed_tau_invL; eauto.
  Qed.

  Lemma well_behaved_tau_inv {R} (e_t : L2_expr Λ R):
    well_behaved (Tau e_t) -> well_behaved e_t.
  Proof.
    intros. inversion H; eauto.
    split; eapply does_not_trigger_tau_inv; eauto.
  Qed.

  Lemma well_formed_tau_invR {R} (e_t e_s: L2_expr Λ R):
    well_formed e_t (Tau e_s) -> well_formed e_t e_s.
  Proof.
    intros; inversion H.
    split; auto; [  | apply closed_tau_invR; eauto] .
    apply well_behaved_tau_inv; auto.
  Qed.

  Lemma well_formed_tau_inv {R} (e_t e_s: L2_expr Λ R):
    well_formed (Tau e_t) (Tau e_s) -> well_formed e_t e_s.
  Proof.
    intros. eapply well_formed_tau_invL, well_formed_tau_invR; auto.
  Qed.

  #[global] Instance well_formed_Proper_impl {R}:
    Proper (eq_itree eq ==> eq_itree eq ==> impl) (well_formed (R := R)).
  Proof.
    repeat intro. destruct H1. destruct H1, H2.
    split; split;
      try solve [ by rewrite <- H0 | by rewrite <- H ].
  Qed.

  #[global] Instance well_formed_Proper {R}:
    Proper (eq_itree eq ==> eq_itree eq ==> iff) (well_formed (R := R)).
  Proof.
    split; eapply well_formed_Proper_impl; by symmetry.
  Qed.

  Lemma well_formed_vis_inv {X R} (e : _ X) (k k': _ -> L2_expr Λ R):
    well_formed (Vis e k) (Vis e k') -> forall v, well_formed (k v) (k' v).
  Proof.
    intros. destruct H.
    split; inv H; split; eauto.
    1, 2 : eapply does_not_trigger_vis_inv; eauto.
    - destruct H0.
      punfold H. inv H.
      dependent destruction H6; pclearbot; eauto.
      eapply H4.
    - destruct H0.
      punfold H0. inv H0.
      dependent destruction H6; pclearbot; eauto.
      eapply H4.
  Qed.

End WF.
