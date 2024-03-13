From iris.bi Require Import bi.
From iris.proofmode Require Import proofmode.
From simuliris.logic Require Import satisfiable.
From simuliris.simulation Require Import simulation language slsls.
From simuliris.utils Require Import no_event.
From iris.prelude Require Import options.
Import bi.

Set Default Proof Using "Type*".

From simuliris.logic Require Import satisfiable.
From simuliris.simulation Require Import slsls wellformedness.
From simuliris.utils Require Import tactics.

From ITree Require Import ITree Eq Events.State Events.StateFacts.
From ITree Require Import Eq.EqAxiom.
From ITree.Interp Require Import TranslateFacts RecursionFacts.
From Paco Require Import paco.

From Coq Require Import Program.Equality.
From Equations Require Import Equations.

Import CatNotations.
Local Open Scope cat.

Section contextual_refinement.

  Context {PROP : bi} `{!BiBUpd PROP, !BiAffine PROP, !BiPureForall PROP}.
  Context {Λ : language} {η: handlers Λ}.

  Definition context := CallEvents Λ ~> itree (CallEvents Λ +' UB_events Λ +' exc_events Λ +' F Λ).

  Definition close_context
    (C : context) (σ : language.state Λ) {R : Type} (t : expr Λ R) : L2_expr Λ R :=
    inject_l (interp_mrec C (⟦ η ⟨ t ⟩ ⟧ σ)).

  Context {sat: PROP → Prop} {Sat: Satisfiable sat}.
  Arguments sat _%I.


  Context `{GS : simulirisGS PROP Λ}.

  Instance sim : SimE PROP Λ := sim_expr_stutter (η := η).

  Corollary close_context_has_no_call_events:
    forall (C : context) (σ : language.state Λ) (R : Type) (t : expr Λ R),
      no_call_events (close_context C σ t).
  Proof.
    rewrite /no_call_events /close_context.
    intros.
    apply inject_no_event_l.
  Qed.

  Ltac sat_crunch :=
    repeat
      match goal with
      | [H : sat (|==> _) |- _] => apply sat_bupd in H
      | [H : sat (_ ∨ _) |- _] => apply sat_or in H; destruct H
      | [H : sat (_ ∗ _) |- _] => apply sat_sep in H; destruct H
      | [H : sat (∃ _, _) |- _] => apply sat_exists in H; destruct H
      | [H : sat (_ ∧ _) |- _] => apply sat_and in H; destruct H
      | [H : sat ⌜_⌝ |- _] => apply sat_elim in H
      end.

  Remark eutt_interp_mrec:
    forall (C : context) R RR,
      Proper (eutt RR ==> eutt (R2 := R) RR) (@interp_mrec _ _ C _).
  Proof.
    intros. ginit. gcofix CIH. intros * H.
    punfold H. red in H.

    remember (observe x) as ox; remember (observe y) as oy.
    revert x y Heqox Heqoy.
    induction H; intros; unfold interp_mrec.

    - setoid_rewrite unfold_iter. subst.
      setoid_rewrite <- Heqox.
      setoid_rewrite <- Heqoy.
      do 2 rewrite bind_ret_l. gstep.
      by constructor.

    - pclearbot.
      do 2 rewrite unfold_iter; cbn.
      setoid_rewrite <- Heqox.
      setoid_rewrite <- Heqoy.
      do 2 rewrite bind_ret_l. gstep.
      constructor. gbase.
      unfold interp_mrec in CIH; cbn in CIH.
      by eapply CIH.

    - pclearbot.
      do 2 rewrite unfold_iter; cbn.
      setoid_rewrite <- Heqox.
      setoid_rewrite <- Heqoy.
      destruct e; [ | destruct s].
      + do 2 rewrite bind_ret_l. gstep.
        constructor. gbase.
        unfold interp_mrec in CIH; cbn in CIH.
        eapply CIH.
        eapply eutt_clo_bind; [reflexivity | intros; subst; eapply REL ].
      + do 2 rewrite bind_vis.
        gstep.
        constructor. intros; cbn.
        do 2 rewrite bind_ret_l. gstep.
        constructor. gbase.
        unfold interp_mrec in CIH; cbn in CIH.
        eapply CIH; eapply REL.
      + do 2 rewrite bind_vis.
        gstep.
        constructor. intros; cbn.
        do 2 rewrite bind_ret_l. gstep.
        constructor. gbase.
        unfold interp_mrec in CIH; cbn in CIH.
        eapply CIH; eapply REL.

    - pclearbot.
      rewrite unfold_iter; cbn.
      setoid_rewrite <- Heqox.
      rewrite bind_ret_l.
      setoid_rewrite tau_euttge.
      eapply IHeqitF; eauto.

    - pclearbot.
      setoid_rewrite unfold_iter at 2; cbn.
      setoid_rewrite <- Heqoy.
      rewrite bind_ret_l.
      setoid_rewrite tau_euttge.
      eapply IHeqitF; eauto.
  Qed.

  Lemma eutt_contextual_refinement:
    forall (C : context) σ R RR,
      Proper (eutt (R1 := R) RR ==> eutt (HeterogeneousRelations.prod_rel eq RR)) (close_context C σ).
  Proof.
    repeat intro; unfold close_context.
    eapply eutt_translate_gen.
    eapply eutt_interp_mrec.
    by eapply eutt_interp_state.
  Qed.

  Notation st_expr_rel' R1 R2 := (@st_exprO' Λ R1 -d> @st_exprO' Λ R2 -d> PROP).

  Notation T := (UB_events Λ +' exc_events Λ +' F Λ).

  Definition f : ∀ T0 : Type, T T0 → (CallEvents Λ +' T) T0 := inr1.
  Definition b R T C t := (@interp_mrec (CallEvents Λ) T C (state Λ * R) t).

  Local Definition cr_coind_pred {R1 R2} C : st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2 :=
    fun (Φ:st_expr_rel' R1 R2) (e_t:st_expr' Λ R1) (e_s:st_expr' Λ R2) =>
      (∃ Ψ, □ (∀ e_t e_s, lift_expr_rel Ψ e_t e_s ∗-∗ Φ e_t e_s) ∗
       (∃ t s,
          ⌜go e_t ≅ (translate f (b R1 _ C t))⌝ ∗
          ⌜go e_s ≅ (translate f (b R2 _ C s))⌝ ∗
          sim_coindF (lift_expr_rel Ψ) (observe t) (observe s)))%I.

  Local Definition cr_coind_rec {R1 R2} C : st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2 :=
    (λ (Φ0 : st_expr_rel' R1 R2) (e_t0 : st_exprO' R1) (e_s0 : st_exprO' R2),
      ((∃ Ψ, □ (∀ e_t e_s, lift_expr_rel Ψ e_t e_s ∗-∗ Φ0 e_t e_s) ∗
       ∃ t s,
          ⌜go e_t0 ≅ (translate f (b R1 _ C t))⌝ ∗
          ⌜go e_s0 ≅ (translate f (b R2 _ C s))⌝ ∗
          sim_coindF (lift_expr_rel Ψ) (observe t) (observe s))
       ∨ sim_coindF Φ0 e_t0 e_s0)%I).

  Typeclasses eauto :=.

  Instance lift_expr_rel_ne {R1 R2} Φ: NonExpansive (lift_expr_rel (R1 := R1) (R2 := R2) Φ).
  Proof. solve_proper. Qed.

  Instance lift_expr_rel2_ne {R1 R2}: NonExpansive (lift_expr_rel (R1 := R1) (R2 := R2) ).
  Proof. solve_proper. Qed.

  Local Instance cr_coind_pred_ne {R1 R2} rhE:
    NonExpansive (cr_coind_pred rhE: st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2).
  Proof. solve_proper. Qed.

  Local Instance cr_coind_rec_ne {R1 R2} rhE:
    NonExpansive (cr_coind_rec rhE: st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2).
  Proof.
    repeat intro. rewrite /cr_coind_rec. f_equiv.
    2 : solve_proper.
    solve_proper.
  Qed.

  Remark close_context_Tau {R} rhE t:
    @translate T (L2 Λ) (@inr1 (CallEvents Λ) T) (state Λ * R)
      (@interp_mrec (CallEvents Λ) T rhE (state Λ * R) (Tau t))
    ≅ Tau
        (@translate T (L2 Λ) (@inr1 (CallEvents Λ) T) (state Λ * R)
          (@interp_mrec (CallEvents Λ) T rhE (state Λ * R) t)).
  Proof.
    etransitivity.
    { apply eq_itree_translate; [ reflexivity | ].
      rewrite /interp_mrec.
      rewrite unfold_iter.
      cbn. rewrite bind_ret_l. reflexivity. }
    rewrite translate_tau. reflexivity.
  Qed.

  Remark close_context_Vis_CallEvent {R}
    (C : context)
    (X : Type)
    (c : (CallEvents Λ) X)
    (k : X → itree (CallEvents Λ +' T) (state Λ * R)):
    @translate T (L2 Λ) (@inr1 (CallEvents Λ) T) (state Λ * R)
      (@interp_mrec (CallEvents Λ) T C (state Λ * R) (Vis (inl1 c) k))
      ≅
    Tau (translate inr1 (interp_mrec C (ITree.bind (C X c) k))).
  Proof.
    etransitivity.
    { apply eq_itree_translate; [ reflexivity | ].
      rewrite /interp_mrec.
      rewrite unfold_iter.
      cbn. rewrite bind_ret_l. reflexivity. }
    rewrite translate_tau. reflexivity.
  Qed.

  Remark close_context_Vis_E {R}
    (C : context) (X : Type) e
    (k : X → itree (CallEvents Λ +' T) (state Λ * R)):
    @translate T (L2 Λ) (@inr1 (CallEvents Λ) T) (state Λ * R)
      (@interp_mrec (CallEvents Λ) T C (state Λ * R) (Vis (inr1 (inr1 (inr1 e))) k))
      ≅
    Vis (inr1 (subevent X (inr1 (inr1 e))))
      (λ x : X, Tau (translate inr1 (interp_mrec C (k x)))).
  Proof.
    etransitivity.
    { apply eq_itree_translate; [ reflexivity | ].
      rewrite /interp_mrec.
      rewrite unfold_iter.
      cbn. rewrite bind_vis. setoid_rewrite bind_ret_l. reflexivity. }
    rewrite translate_vis. setoid_rewrite translate_tau. reflexivity.
  Qed.

  Remark close_context_Vis_UB {R}
    (C : context) (X : Type) e
    (k : X → itree (CallEvents Λ +' T) (state Λ * R)):
    @translate T (L2 Λ) (@inr1 (CallEvents Λ) T) (state Λ * R)
      (@interp_mrec (CallEvents Λ) T C (state Λ * R) (Vis (inr1 (inl1 e)) k))
      ≅
    Vis (inr1 (inl1 e))
      (λ x : X, Tau (translate inr1 (interp_mrec C (k x)))).
  Proof.
    etransitivity.
    { apply eq_itree_translate; [ reflexivity | ].
      rewrite /interp_mrec.
      rewrite unfold_iter.
      cbn. rewrite bind_vis. setoid_rewrite bind_ret_l. reflexivity. }
    rewrite translate_vis. setoid_rewrite translate_tau. reflexivity.
  Qed.

  Remark close_context_Vis_Exc {R}
    (C : context) (X : Type) e
    (k : X → itree (CallEvents Λ +' T) (state Λ * R)):
    @translate T (L2 Λ) (@inr1 (CallEvents Λ) T) (state Λ * R)
      (@interp_mrec (CallEvents Λ) T C (state Λ * R) (Vis (inr1 (inr1 (inl1 e))) k))
      ≅
    Vis (inr1 (inr1 (inl1 e)))
      (λ x : X, Tau (translate inr1 (interp_mrec C (k x)))).
  Proof.
    etransitivity.
    { apply eq_itree_translate; [ reflexivity | ].
      rewrite /interp_mrec.
      rewrite unfold_iter.
      cbn. rewrite bind_vis. setoid_rewrite bind_ret_l. reflexivity. }
    rewrite translate_vis. setoid_rewrite translate_tau. reflexivity.
  Qed.

  Instance sim_indF_Proper {R1 R2} Φ Ψ:
    Proper ((fun x y => eq_itree eq (go x) (go y)) ==> (fun x y => eq_itree eq (go x) (go y)) ==> equiv)
           (sim_indF (R1 := R1) (R2 := R2) Φ Ψ).
  Proof.
    intros e_t e_t' Ht e_s e_s' Hs.
    apply bisimulation_is_eq in Ht, Hs. inv Ht; inv Hs.
    reflexivity.
  Qed.

  (* Contextual refinement, under unfolded definition of [sim_expr] *)
  (* TODO: State corollary in terms of [sim_expr] *)
  (** *Some examples *)

  (*
    int x = 5;
    call #readonly f(&x);
    return x

    ~

    int x = 5;
    call #readonly f(&x);
    return 5

    context  f {} *)

  (*
    int x = 5;
    call f(&x);
    return x

    ~

    int x = 5;
    call f(&x);
    return x

    context  f (int *x){ *x = 4 } *)
  Definition call_spec (C : context) :=
    (□ (∀ X X0 s s0 (c : _ X) (c0 : _ X0),
        ∃ CS, (state_interp s s0 ∗ call_ev c c0 CS) -∗
          sim_coindF
            (fun x y => ∃ v_t v_s,
              ⌜x = RetF v_t⌝ ∗ ⌜y = RetF v_s⌝ ∗
               state_interp s s0 ∗ call_ans c v_t.2 c0 v_s.2 CS)
          (observe (C _ (@StateEff _ (call_events Λ) _ (s, c))))
          (observe (C _ (@StateEff _ (call_events Λ) _ (s0, c0))))))%I.

  Lemma adequacy_sat_sim_indF:
    forall R e_t e_s RR,
      well_formed e_t e_s ->
      sat (sim_indF sim_coindF (lift_expr_rel (lift_post (λ x y : R, ⌜RR x y⌝%I))) (observe e_t) (observe e_s)) ->
      sat (|==>
             ∃ X (e_t' : X -> itree' (L2 Λ) (state Λ * R)) (e_s' : X -> itree' (L2 Λ) (state Λ * R)),
               ⌜eqit_ (λ '(σ_t, v_t) '(σ_s, v_s), RR v_t v_s) true true id
                (λ e_t'' e_s'' : itree (L2 Λ) (state Λ * R),
                    well_formed e_t'' e_s'' /\
                    ∃ x x', x ~= x' /\ (e_t' x) = observe e_t'' ∧ (e_s' x') = observe e_s'') e_t e_s⌝ ∗
              ∀ x x', ⌜x ~= x'⌝ ==∗ sim_coindF (lift_expr_rel (lift_post (λ x y : R, ⌜RR x y⌝%I))) (e_t' x) (e_s' x')).
  Proof.
    intros * WF Hsat.
    eapply sat_mono, Hsat.
    iIntros "Hpre".
    iPoseProof
      (sim_indF_ind
         (λ Φ e_t e_s,
           (∀ e_t e_s, Φ e_t e_s
                         ==∗ ∃ σ_t v_t σ_s v_s, ⌜go e_t ≅ Ret (σ_t, v_t) /\ go e_s ≅ Ret (σ_s, v_s) /\ RR v_t v_s⌝ ∗ Φ e_t e_s)
             ==∗ ∃ X (e_t' : X -> itree' (L2 Λ) (state Λ * R)) (e_s' : X -> itree' (L2 Λ) (state Λ * R)) e_t_ e_s_,
               ⌜well_formed (go e_t) (go e_s)⌝ -∗
               ⌜e_t_ ≅ go e_t
                /\ e_s_ ≅ go e_s
                /\ eqit_ (λ '(σ_t, v_t) '(σ_s, v_s), RR v_t v_s) true true id
                         (λ e_t'' e_s'' : itree (L2 Λ) (state Λ * R),
                             well_formed e_t'' e_s''
                             /\ ∃ x x', x ~= x' /\ (e_t' x) = observe e_t'' ∧ (e_s' x') = observe e_s'') e_t_ e_s_⌝
               ∗ ∀ x x', ⌜x ~= x'⌝ ==∗ sim_coindF Φ (e_t' x) (e_s' x'))%I
                    with "[] Hpre") as "Hind".
    { repeat intro; do 2 f_equiv.
      - do 3 f_equiv; solve_proper.
      - do 18 f_equiv. solve_proper. }

    { iModIntro. clear WF e_t e_s Hsat.
      iIntros (Φ e_t e_s) "Hsim".
      iIntros "Hpre".
      unfold sim_expr_inner; iMod "Hsim";
        iDestruct "Hsim" as (c) "Hsim".
      destruct c.
      { (* [BASE] case *)
        iSpecialize ("Hpre" with "Hsim").
        iMod "Hpre".
        iDestruct "Hpre" as (σ_t v_t σ_s v_s H) "Hpre".
        destruct H as (Ht&Hs&HR).

        iModIntro. repeat iExists _.
        iIntros (WF).
        iSplitL ""; [ iPureIntro; repeat (split; [ done | ]); by constructor | ].
        iIntros.
        rewrite sim_coindF_unfold sim_indF_unfold /sim_expr_inner.
        by provide_case: BASE. }

      { (* [STUTTER_L] case *)
        iDestruct "Hsim" as (??) "Hsim"; subst.
        rewrite H; clear H.
        iSpecialize ("Hsim" with "Hpre").
        iMod "Hsim".
        iDestruct "Hsim" as (?????) "Hsim".

        iModIntro. repeat iExists _.
        iIntros (WF).
        eapply well_formed_tau_invL in WF.
        rewrite (itree_eta t) in WF.
        iSpecialize ("Hsim" $! WF).
        iDestruct "Hsim" as (?) "Hsim".
        destruct H as (Ht&Hs&Heq).
        iSplitL ""; [ | done ].
        iPureIntro.
        rewrite <- itree_eta in Ht.
        split; [ by apply eqit_Tau | ].
        split; [ done | intros ].
          by constructor. }

      { (* [STUTTER_R] case *)
        iDestruct "Hsim" as (??) "Hsim"; subst.
        rewrite H; clear H.
        iSpecialize ("Hsim" with "Hpre").
        iMod "Hsim".
        iDestruct "Hsim" as (?????) "Hsim".

        iModIntro. repeat iExists _.
        iIntros (WF).
        eapply well_formed_tau_invR in WF.
        rewrite (itree_eta s) in WF.
        iSpecialize ("Hsim" $! WF).
        iDestruct "Hsim" as (?) "Hsim".
        destruct H as (Ht&Hs&Heq).

        iSplitL ""; [ | done ].
        iPureIntro.
        rewrite <- itree_eta in Hs.
        split; [ done | ].
        split; [ by apply eqit_Tau | intros ].
          by constructor. }

      { (* [TAU_STEP] case *)
        iDestruct "Hsim" as (????) "Hsim"; subst.
        iModIntro. iExists _, (fun _ => observe t), (fun _ => observe s), _,_.
        iIntros (WF).
        rewrite H H0 in WF.
        eapply well_formed_tau_inv in WF.

        iSplitL ""; [ | iIntros; iApply "Hsim" ].
        iPureIntro. rewrite H H0.
        split; [ done | ].
        split; [ by apply eqit_Tau | ].
        intros.
        constructor. split; try done.
        eexists 2, 2. split; done. }

      { (* [VIS_STEP] case *)
        iDestruct "Hsim" as (????????) "Hsim"; subst.
        iModIntro.
        rewrite H H0.

        destruct e_t0, e_s0 ; [ | done | repeat destruct s; done | ].
        - cbn.
          iExists _, (fun x => observe (k_t x)), (fun x => observe (k_t x)),
            (Vis (inl1 c) k_t), (Vis (inl1 c0) k_s).
          iIntros (WF).
          exfalso. destruct WF.
          destruct H2. punfold H2. inv H2.
        - destruct s, s0; try done; [ by destruct s | destruct s; [ | destruct s0]; try done].
          cbn. rewrite /handle_E.
          iDestruct "Hsim" as (?) "Hsim".
          destruct H1 as (?&?); subst; inv H1.
          iExists _, (fun x => observe (k_t x)), (fun x => observe (k_s x)),
            (Vis _ k_t), (Vis _ k_s).
          iIntros (WF).
          iSplitL "".
          + iPureIntro.
            do 2 (split; [ done |]).
            constructor; intros; cbn; constructor; eauto.
            eapply well_formed_vis_inv in WF; eauto.
          + iIntros.
            iSpecialize ("Hsim" $! _ _ H1).
            by iMod "Hsim". }

      { (* [SOURCE_UB] case *)
        iDestruct "Hsim" as (???) "%H"; subst.
        iModIntro. iExists _, (fun x => VisF (inr1 (inl1 e)) k), _,_,_.
        iIntros (H0).
        iSplitL "".
        { iPureIntro. split; [ done | ].
          split; [ symmetry ; done | ].
          intros. rewrite H in H0. destruct H0. exfalso.
          destruct H0. apply H0.
          pstep. red. cbn. pose proof @has_event_now.
          remember (upaco1 has_event_F_ bot1).
          specialize (H3 _ _ _ P _ _ e k). cbn in H3. eapply H3. }
        iIntros.
        rewrite sim_coindF_unfold sim_indF_unfold.
        by provide_case: SOURCE_UB.
        Unshelve. all : eauto. }

      { (* [SOURCE_EXC] case *)
        iDestruct "Hsim" as (???) "%H"; subst.
        iModIntro. iExists _, (fun x => VisF (inr1 (inr1 (inl1 e))) k), _,_, _.
        iIntros (H0).
        iSplitL "".
        { iPureIntro. do 2 (split; [ done | ]).
          intros. rewrite H in H0. destruct H0. exfalso. destruct H0. apply H2.
          pstep. red. cbn. pose proof @has_event_now.
          remember (upaco1 has_event_F_ bot1).
          specialize (H3 _ _ _ P _ _ e k); eauto. }
        iIntros.
        rewrite sim_coindF_unfold sim_indF_unfold.
        by provide_case: SOURCE_EXC.
        Unshelve. all : eauto. } }

    (* conclude *)
    iAssert
      (∀ e_t0 e_s0 : st_exprO' R,
              lift_expr_rel (lift_post (λ x y : R, ⌜RR x y⌝)) e_t0 e_s0 ==∗
              ∃ (σ_t : state Λ) (v_t : R) (σ_s : state Λ) (v_s : R),
                ⌜{| _observe := e_t0 |} ≅ Ret (σ_t, v_t) ∧ {| _observe := e_s0 |} ≅ Ret (σ_s, v_s) ∧ RR v_t v_s⌝ ∗
                lift_expr_rel (lift_post (λ x y : R, ⌜RR x y⌝)) e_t0 e_s0)%I
      as "Hpre".
    { unfold lift_expr_rel, lift_post. clear WF e_t e_s Hsat.
      iIntros (e_t e_s).
      iIntros "Hpre".
      iModIntro.
      iDestruct "Hpre" as (σ_t v_t σ_s v_s) "[%Ht [%Hs [SI Hpre]]]".
      iDestruct "Hpre" as (v_t' v_s') "[%Ht' [%Hs' %HR]]".
      iExists σ_t, v_t', σ_s, v_s'; iFrame.
      apply eqit_inv in Ht', Hs'; inv Ht'; inv Hs'.
      symmetry in Ht, Hs. iSplitL ""; eauto.
      iExists _,_,_,_. iFrame. iSplitL ""; eauto. }
    iSpecialize ("Hind" with "Hpre").
    iMod "Hind".
    iDestruct "Hind" as (X e_t' e_s' e_t_ e_s_) "H".
    setoid_rewrite itree_eta in WF.
    iSpecialize ("H" $! WF).
    iDestruct "H" as "[%EQ H]".
    iExists _,_,_. iFrame.
    iModIntro. iPureIntro. destruct EQ as (?&?&?); eauto.
    rewrite <-itree_eta in H, H0.
    eapply bisimulation_is_eq in H, H0. subst; eauto.
  Qed.

End contextual_refinement.

Notation "C ⟦ t ⟧ σ" := (close_context C σ t) (at level 10).
