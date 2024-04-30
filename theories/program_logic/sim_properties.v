From iris.prelude Require Import options.

From velliris.program_logic Require Export weakest_pre weakbisim.
From velliris.utils Require Import tactics.

From ITree Require Import ITree Eq EqAxiom Events.State Events.StateFacts.

From Paco Require Import paco.

From Coq Require Import Program.Equality.

From Equations Require Import Equations.

Section sim_expr_properties.

  Context {PROP : bi} `{!BiBUpd PROP, !BiAffine PROP, !BiPureForall PROP}.
  Context {Λ : language} {η : handlers Λ}.
  Context {si : simulirisGS PROP Λ}.
  Set Default Proof Using "Type*".

  (* FIX: Share NonExpansive/Proper instances with [slsls] *)
  Notation st_expr_rel' R1 R2 := (@st_exprO' Λ R1 -d> @st_exprO' Λ R2 -d> PROP).
  Notation st_expr_rel R1 R2 := (@st_exprO Λ R1 -d> @st_exprO Λ R2 -d> PROP).
  Notation expr_rel R1 R2 := (@exprO Λ R1 -d> @exprO Λ R2 -d> PROP).
  Notation expr_rel' R1 R2 := (@exprO' Λ R1 -d> @exprO' Λ R2 -d> PROP).

  Local Instance expr_rel_func_ne {R1 R2} (F: expr_rel R1 R2 -d> expr_rel R1 R2) `{Hne: !NonExpansive F}:
    (∀ n, Proper (dist n ==> dist n ==> dist n ==> dist n) F).
  Proof.
    intros n Φ Φ' HΦ e_t e_t' ->%discrete_iff%leibniz_equiv e_s e_s' ->%discrete_iff%leibniz_equiv
          ; [|apply _..].
    eapply Hne, HΦ.
  Qed.

  Local Instance expr_rel'_func_ne {R1 R2} (F: expr_rel' R1 R2 -d> expr_rel' R1 R2) `{Hne: !NonExpansive F}:
    (∀ n, Proper (dist n ==> dist n ==> dist n ==> dist n) F).
  Proof.
    intros n Φ Φ' HΦ e_t e_t' ->%discrete_iff%leibniz_equiv e_s e_s' ->%discrete_iff%leibniz_equiv
          ; [|apply _..].
    eapply Hne, HΦ.
  Qed.

  Local Instance st_expr_rel'_func_ne {R1 R2} (F: st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2) `{Hne: !NonExpansive F}:
    (∀ n, Proper (dist n ==> dist n ==> dist n ==> dist n) F).
  Proof.
    intros n Φ Φ' HΦ e_t e_t' ->%discrete_iff%leibniz_equiv e_s e_s' ->%discrete_iff%leibniz_equiv
          ; [|apply _..].
    eapply Hne, HΦ.
  Qed.

  Local Instance st_expr_rel_func_ne {R1 R2} (F: st_expr_rel R1 R2 -d> st_expr_rel R1 R2) `{Hne: !NonExpansive F}:
    (∀ n, Proper (dist n ==> dist n ==> dist n ==> dist n) F).
  Proof.
    intros n Φ Φ' HΦ e_t e_t' ->%discrete_iff%leibniz_equiv e_s e_s' ->%discrete_iff%leibniz_equiv
          ; [|apply _..].
    eapply Hne, HΦ.
  Qed.

  Local Instance sim_expr_stutter : SimE PROP Λ := (sim_expr_aux (η := η)).(unseal).

  (* Auxiliary facts about simulation relation *)
  Lemma sim_expr_bind {R1 R2} {Re1 Re2} (Φ : expr_rel R1 R2) (e_t : expr Λ Re1) (e_s : expr Λ Re2) k_t k_s:
    e_t ⪯ e_s [{ fun e_t'' e_s'' => ITree.bind e_t'' k_t ⪯ ITree.bind e_s'' k_s [{ Φ }] }] -∗
    ITree.bind e_t k_t ⪯ ITree.bind e_s k_s [{ Φ }].
  Proof.
    rewrite sim_expr_eq; simpl.
    rewrite sim_expr_eq; simpl.
    iIntros "Hpre" (σ_t σ_s) "SI".
    rewrite /interp_L2.
    iSpecialize ("Hpre" with "SI").

    pose proof (interp_state_bind (handle_L0_L2 η) e_t k_t σ_t).
    pose proof (interp_state_bind (handle_L0_L2 η) e_s k_s σ_s).

    (* Typeclasses instances can't figure out simply [rewrite H]. (a tragedy) *)
    setoid_rewrite itree_eta with (t := ITree.bind e_t k_t) in H.
    setoid_rewrite itree_eta with (t := ITree.bind e_s k_s) in H0.
    pose proof @sim_coindF_Proper as SEP.
    pose proof @lift_expr_rel_Φ_Proper as LEP.
    specialize (SEP PROP _ _ _ Λ η _ R1 R2). repeat red in SEP.
    specialize (LEP PROP _ _ _ Λ η _ R1 R2 Φ).
    specialize (SEP _ _ LEP). clear LEP.
    specialize (SEP _ _ H _ _ H0).
    iApply SEP. clear SEP.

    iPoseProof (sim_coindF_bupd_mono with "[] Hpre") as "Hpre"; last first.
    {
      by iPoseProof ((@sim_coindF_coind_bind PROP _ _ _ Λ η _ _ _ _ _ (lift_expr_rel Φ) _ _
          (λ st : language.state Λ * Re1, interp_state (handle_L0_L2 η) (k_t st.2) st.1)
          (λ st : language.state Λ * Re2, interp_state (handle_L0_L2 η) (k_s st.2) st.1)) with "Hpre") as "Hcoind". }

    clear e_t e_s H H0 σ_t σ_s.
    iIntros (e_t e_s) "HΦ".
    rewrite {1}/lift_expr_rel.
    iDestruct "HΦ" as (σ_t v_t σ_s v_s) "(%Ht & %Hs & SI & HΦ)".
    iSpecialize ("HΦ" with "SI").
    iDestruct "HΦ" as ">HΦ". subst. rewrite /interp_L2.

    pose proof (interp_state_bind (handle_L0_L2 η) (Ret v_t) k_t σ_t).
    pose proof (interp_state_bind (handle_L0_L2 η) (Ret v_s) k_s σ_s).
    eapply eq_sub_eutt in H, H0.

    (* Typeclasses instances can't figure out simply [rewrite H]. *)
    setoid_rewrite itree_eta with (t := ITree.bind (Ret v_t) k_t) in H.
    setoid_rewrite itree_eta with (t := ITree.bind (Ret v_s) k_s) in H0.
    pose proof (@sim_coindF_Proper ) as SEP.
    iApply SEP; eauto.
    { eapply lift_expr_rel_Φ_Proper. }
    { rewrite <- Ht; do 2 rewrite bind_ret_l; reflexivity. }
    { rewrite <- Hs; do 2 rewrite bind_ret_l; reflexivity. }
    Unshelve. all: exact η.
  Qed.

  Lemma sim_expr_vis {R1 R2 Re1 Re2} (Φ : expr_rel R1 R2) (ev_t : L0 Λ Re1) (ev_s : L0 Λ Re2) k_t k_s:
    trigger ev_t ⪯ trigger ev_s [{ fun e_t'' e_s'' => ITree.bind e_t'' k_t ⪯ ITree.bind e_s'' k_s [{ Φ }] }] -∗
      vis ev_t k_t ⪯ vis ev_s k_s [{ Φ }].
  Proof.
    do 2 rewrite sim_expr_eq; simpl.
    iIntros "Hpre %σ_t' %σ_s' SI".
    rewrite /interp_L2.
    iSpecialize ("Hpre" with "SI").

    pose proof (interp_state_vis ev_t k_t (handle_L0_L2 η) σ_t').
    pose proof (interp_state_vis ev_s k_s (handle_L0_L2 η) σ_s').

    pose proof @sim_coindF_Proper as SEP.
    pose proof @lift_expr_rel_Φ_Proper as LEP.
    specialize (SEP PROP _ _ _ Λ η _ R1 R2). repeat red in SEP.
    specialize (LEP PROP _ _ _ Λ η _ R1 R2 Φ).
    specialize (SEP _ _ LEP). clear LEP.

    specialize (SEP _ _ H _ _ H0).
    iApply SEP. clear SEP.

    iPoseProof (sim_coindF_bupd_mono with "[] Hpre") as "Hpre"; last first.
    {
      iPoseProof ((@sim_coindF_coind_bind PROP _ _ _ Λ η _ _ _ _ _ (lift_expr_rel Φ) _ _) with "Hpre") as "Hcoind".

      unfold interp_L2. clear H H0.
      pose proof (interp_state_trigger_eqit ev_t (handle_L0_L2 η) σ_t') as H_eq.
      pose proof @eq_itree_clo_bind.
      specialize (H _ _ _ eq _ _ eq _ _
                    (fun x => interp_state (handle_L0_L2 η) (k_t x.2) x.1)
                    (fun x => interp_state (handle_L0_L2 η) (k_t x.2) x.1)
                    H_eq).

      assert (H_ : (∀ u1 u2 : state Λ * Re1,
         u1 = u2
         → (λ x : state Λ * Re1, interp_state (handle_L0_L2 η) (k_t x.2) x.1) u1
            ≅ (λ x : state Λ * Re1, interp_state (handle_L0_L2 η) (k_t x.2) x.1) u2)).
      { intros; subst; reflexivity. }
      specialize (H H_); clear H_.

      pose proof (interp_state_trigger_eqit ev_s (handle_L0_L2 η) σ_s') as H_eq'.
      pose proof @eq_itree_clo_bind.
      specialize (H0 _ _ _ eq _ _ eq _ _
                    (fun x => interp_state (handle_L0_L2 η) (k_s x.2) x.1)
                    (fun x => interp_state (handle_L0_L2 η) (k_s x.2) x.1) H_eq').

      assert (H_ : (∀ u1 u2 : state Λ * Re2,
          u1 = u2
          → (λ x : state Λ * Re2, interp_state (handle_L0_L2 η) (k_s x.2) x.1) u1
            ≅ (λ x : state Λ * Re2, interp_state (handle_L0_L2 η) (k_s x.2) x.1) u2)).
      { intros;subst;reflexivity. }
      specialize (H0 H_); clear H_.
      clear H_eq H_eq'.

      rewrite bind_bind in H.
      setoid_rewrite bind_tau in H.
      setoid_rewrite bind_ret_l in H.

      rewrite bind_bind in H0.
      setoid_rewrite bind_tau in H0.
      setoid_rewrite bind_ret_l in H0.

      pose proof @sim_coindF_Proper as SEP.
      pose proof @lift_expr_rel_Φ_Proper as LEP.
      specialize (SEP PROP _ _ _ Λ η _ R1 R2). repeat red in SEP.
      specialize (LEP PROP _ _ _ Λ η _ R1 R2 Φ).
      specialize (SEP _ _ LEP _ _ H _ _ H0). clear LEP.
      clear H H0.

      iApply SEP; eauto. }

    iIntros (e_t e_s) "H"; auto.
    unfold lift_expr_rel.
    iDestruct "H" as (σ_t v_t σ_s v_s Ht Hs) "[SI H]".
    apply eqit_inv in Ht, Hs. cbn in *.
    destruct e_t, e_s; try solve [inv Ht | inv Hs].
    subst. unfold sim_expr_.
    iSpecialize ("H" with "SI").
    by iMod "H".
  Qed.

  Ltac sim_rewrite EQ EQ' R1 R2 Φ :=
    pose proof @sim_coindF_Proper as SEP;
    pose proof @lift_expr_rel_Φ_Proper as LEP;
    specialize (SEP PROP _ _ _ Λ η _ R1 R2); repeat red in SEP;
    specialize (LEP PROP _ _ _ Λ η _ R1 R2 Φ);
    specialize (SEP _ _ LEP); clear LEP;
    specialize (SEP _ _ EQ _ _ EQ');
    iApply SEP; clear SEP; clear EQ EQ'.

  Ltac sim_rewrite_eutt EQ EQ' R1 R2 Φ :=
    let H_eq := fresh "EQ" in
    let H_eq' := fresh "EQ'" in
    pose proof @EQ as H_eq; symmetry in H_eq;
    pose proof @EQ' as H_eq'; symmetry in H_eq';
    pose proof @sim_coindF_eutt_Proper as SEP;
    pose proof @lift_expr_rel_Φ_Proper as LEP;
    specialize (SEP R1 R2); specialize (LEP R1 R2 Φ);
    specialize (SEP _ LEP); clear LEP; cbn in SEP;
    specialize (SEP _ _ H_eq _ _ H_eq'); iApply SEP; clear H_eq H_eq' SEP.

  Ltac sim_coindF_ne := unshelve eapply sim_coindF_ne; exact η.

  Lemma sim_expr_tau_coind {R1 R2} (Φ : expr_rel R1 R2) e_t e_s:
    e_t ⪯ e_s [{ fun e_t'' e_s'' => e_t'' ⪯ e_s'' [{ Φ }] }] -∗
        Tau e_t ⪯ Tau e_s [{ Φ }].
  Proof.
    rewrite sim_expr_eq; simpl. unfold sim_expr_.
    iIntros "Hpre" (σ_t σ_s) "SI".
    rewrite /interp_L2.
    iSpecialize ("Hpre" with "SI").

    pose proof (interp_state_tau _ e_t (handle_L0_L2 η) σ_t).
    pose proof (interp_state_tau _ e_s (handle_L0_L2 η) σ_s).
    sim_rewrite H H0 R1 R2 Φ.

    iMod "Hpre".
    iModIntro.
    rewrite (sim_coindF_unfold (lift_expr_rel Φ)).
    rewrite sim_indF_unfold.
    unfold sim_expr_inner; cbn.
    provide_case: TAU_STEP.
    iPoseProof (sim_coindF_bupd_mono with "[] Hpre") as "Hpre"; [ | done].

    clear e_t e_s σ_t σ_s.
    iIntros (e_t e_s) "H".
    unfold lift_expr_rel.
    iDestruct "H" as (σ_t v_t σ_s v_s Ht Hs) "[SI H]".
    iSpecialize ("H" with "SI"). iMod "H".

    apply eqit_inv in Ht, Hs. cbn in *;
      destruct e_t, e_s; try solve [inv Ht | inv Hs]; subst.

    rewrite /sim_coind sim_coindF_unfold sim_indF_unfold.
    unfold sim_expr_inner. iMod "H".
    iDestruct "H" as (c) "H"; destruct c; [ done | ..]; case_solve.
  Qed.

  Lemma sim_expr_tau {R1 R2} (Φ : expr_rel R1 R2) e_t e_s:
    e_t ⪯ e_s [{ Φ }] -∗
      Tau e_t ⪯ Tau e_s [{ Φ }].
  Proof.
    rewrite sim_expr_eq; simpl. unfold sim_expr_.
    iIntros "Hpre" (σ_t σ_s) "SI".
    rewrite /interp_L2.
    iSpecialize ("Hpre" with "SI").

    pose proof (interp_state_tau _ e_t (handle_L0_L2 η) σ_t).
    pose proof (interp_state_tau _ e_s (handle_L0_L2 η) σ_s).
    sim_rewrite H H0 R1 R2 Φ.

    iMod "Hpre".
    iModIntro.
    rewrite (sim_coindF_unfold (lift_expr_rel Φ)). 
    rewrite sim_indF_unfold.
    unfold sim_expr_inner; cbn.
    by provide_case: TAU_STEP.
  Qed.

  Lemma sim_expr_tauL {R1 R2} (Φ:expr_rel R1 R2) e_t e_s:
    e_t ⪯ e_s [{ Φ }] -∗ e_t ⪯ Tau e_s [{ Φ }].
  Proof.
    rewrite sim_expr_eq; simpl.
    iIntros "Hpre" (σ_t σ_s) "SI".
    rewrite /interp_L2.
    iSpecialize ("Hpre" with "SI").

    assert (interp_state (handle_L0_L2 η) e_t σ_t ≅ interp_state (handle_L0_L2 η) e_t σ_t) by reflexivity.
    pose proof (interp_state_tau _ e_s (handle_L0_L2 η) σ_s).
    sim_rewrite H H0 R1 R2 Φ.

    unfold interp_L2.
    iMod "Hpre".
    iModIntro.
    rewrite (sim_coindF_unfold (lift_expr_rel Φ)) sim_indF_unfold.
    setoid_rewrite sim_coindF_unfold.

    unfold sim_expr_inner; cbn.
    by provide_case: STUTTER_R.
  Qed.

  Lemma sim_expr_tauR {R1 R2} (Φ:expr_rel R1 R2) e_t e_s:
    e_t ⪯ e_s [{ Φ }] -∗ Tau e_t ⪯ e_s [{ Φ }].
  Proof.
    rewrite sim_expr_eq; simpl.
    iIntros "Hpre" (σ_t σ_s) "SI".
    rewrite /interp_L2.
    iSpecialize ("Hpre" with "SI").

    pose proof (interp_state_tau _ e_t (handle_L0_L2 η) σ_t).
    assert (interp_state (handle_L0_L2 η) e_s σ_s ≅ interp_state (handle_L0_L2 η) e_s σ_s) by reflexivity.
    sim_rewrite H H0 R1 R2 Φ.

    unfold interp_L2.
    iMod "Hpre".
    iModIntro.

    rewrite (sim_coindF_unfold (lift_expr_rel Φ)) sim_indF_unfold.
    setoid_rewrite sim_coindF_unfold.

    unfold sim_expr_inner; cbn.
    by provide_case: STUTTER_L.
  Qed.

  Lemma sim_expr_decompose {R1 R2} e_t e_s (Φ : expr_rel R1 R2) Ψ:
    e_t ⪯ e_s [{ Ψ }] -∗
    (∀ e_t e_s, Ψ e_t e_s -∗ e_t ⪯ e_s [{ Φ }]) -∗
    e_t ⪯ e_s [{ Φ }].
  Proof.
    iIntros "H1 H2".
    remember (fun x => (Ret x): itree (L0 Λ) R1) as id.
    remember (fun x => (Ret x): itree (L0 Λ) R2) as id'.
    pose proof (bind_ret_r e_t) as Ht.
    pose proof (bind_ret_r e_s) as Hs.
    pose proof (@sim_expr_Φ_Proper PROP _ _ _ Λ η _) as SEP.
    specialize (SEP R1 R2 Φ _ _ Ht _ _ Hs).
    iApply SEP.
    iPoseProof (sim_expr_bind Φ e_t e_s id id') as "Hbind".
    subst. iApply "Hbind". iClear "Hbind".

    iApply (sim_expr_mono with "[H2]"); [ | done].
    iIntros (e_t' e_s'). iIntros. clear SEP Ht Hs.

    pose proof (bind_ret_r e_t') as Ht.
    pose proof (bind_ret_r e_s') as Hs.
    pose proof (@sim_expr_Φ_Proper PROP _ _ _ Λ η _) as SEP.
    specialize (SEP R1 R2 Φ _ _ Ht _ _ Hs).
    symmetry in SEP. cbn in SEP.
    iApply SEP.
      by iApply "H2".
  Qed.

  Local Instance sim_val_stutter : SimV PROP Λ := weakest_pre.sim_stutter (η := η).
  Local Instance sim_stutter : Sim PROP Λ := sim_val.

  Lemma sim_bind {R1 R2 Re1 Re2} (e_t:expr Λ Re1) (e_s:expr Λ Re2) k_t k_s (Φ:expr_rel R1 R2) :
    e_t ⪯ e_s {{ fun e_t'' e_s'' => k_t e_t'' ⪯ k_s e_s'' [{ Φ }] }} -∗
    ITree.bind e_t k_t ⪯ ITree.bind e_s k_s [{ Φ }].
  Proof.
    iIntros "Ha". iApply sim_expr_bind.
    iApply (sim_expr_mono with "[] Ha").
    rewrite /lift_post.
    iIntros (e_t' e_s') "Hv".
    iDestruct "Hv" as (v_t v_s) "[%Ht [%Hs Hsim]]".
    symmetry in Ht, Hs.
    iApply sim_expr_Φ_Proper; [ | | try done].
    { rewrite <- Ht; rewrite bind_ret_l; reflexivity. }
    { rewrite <- Hs; rewrite bind_ret_l; reflexivity. }
  Qed.

  Definition lift {R}: expr Λ R -> state Λ -> st_expr Λ R.
    intros ??.
    exact (interp_L2 η X X0).
  Defined.

  Definition lift_rel {R1 R2}: expr_rel R1 R2 -> st_expr_rel' R1 R2 :=
    fun R t s =>
    (∃ σ_t σ_s e_t e_s,
        state_interp σ_t σ_s ∗
              ⌜t = observe (interp_L2 η e_t σ_t)⌝ ∗
              ⌜s = observe (interp_L2 η e_s σ_s)⌝ ∗ R e_t e_s)%I.

  Definition sim_coind' {R1 R2} :=
    fun Φ x y => sim_coindF (R1 := R1) (R2 := R2) (lift_rel Φ) (observe x) (observe y).

  (* Simulation for coinductive proofs *)
  Definition sim_expr' {R1 R2} : expr_rel R1 R2 -d> expr_rel R1 R2 :=
      fun Φ e_t e_s =>
        (∀ σ_t σ_s, state_interp σ_t σ_s ==∗
            sim_coind' Φ (⟦η⟨e_t⟩⟧ σ_t) (⟦η⟨e_s⟩⟧ σ_s))%I.

  Notation "et '⪯' es [[ Φ ]]" := (sim_expr' Φ et es)
    (at level 70, Φ at level 200,
    format "'[hv' et  '/' '⪯' '/' es  '/' [[  '[ ' Φ  ']' ]] ']'") : bi_scope.

  (* Properties about [sim_expr'] *)
  #[global] Instance sim_expr'_Proper_eq_itree_impl {R1 R2} (Φ:exprO R1 -d> exprO R2 -d> _):
    Proper (eq_itree eq ==> eq_itree eq ==> bi_entails) (sim_expr' Φ).
  Proof.
    iIntros (??????) "HΦ".
    apply EqAxiom.bisimulation_is_eq in H, H0; inversion H; inversion H0.
    done.
  Qed.

  #[global] Instance sim_expr'_Proper_eq_itree {R1 R2} (Φ:exprO R1 -d> exprO R2 -d> _):
    Proper (eq_itree eq ==> eq_itree eq ==> equiv) (sim_expr' Φ).
  Proof.
    intros ??????.
    iSplit; iApply sim_expr'_Proper_eq_itree_impl; done.
  Qed.

  #[global] Instance sim_coind'_Proper_eq_itree_impl {R1 R2} (Φ:exprO R1 -d> exprO R2 -d> _):
    Proper (eq_itree eq ==> eq_itree eq ==> bi_entails) (sim_coind' Φ).
  Proof.
    iIntros (??????) "HΦ".
    apply EqAxiom.bisimulation_is_eq in H, H0; inversion H; inversion H0.
    done.
  Qed.

  #[global] Instance sim_coind'_Proper_eq_itree {R1 R2} (Φ:exprO R1 -d> exprO R2 -d> _):
    Proper (eq_itree eq ==> eq_itree eq ==> equiv) (sim_coind' Φ).
  Proof.
    intros ??????.
    iSplit; iApply sim_coind'_Proper_eq_itree_impl; done.
  Qed.

  Instance lift_rel_Φ_Proper {R1 R2} Φ:
    Proper ((fun x y => eq_itree eq (go x) (go y)) ==>
            (fun x y => eq_itree eq (go x) (go y)) ==> equiv)
           (lift_rel (R1 := R1) (R2 := R2) Φ).
  Proof.
    repeat intro. unfold lift_rel.
    iSplit; iIntros "SI".
    - iDestruct "SI" as (????) "(SI & %Ht & %Hs & HΦ)"; subst.
      iExists σ_t, σ_s, e_t, e_s; iFrame.
      apply EqAxiom.bisimulation_is_eq in H, H0; inversion H; inversion H0.
      iSplitL ""; done.
    - iDestruct "SI" as (????) "(SI & %Ht & %Hs & HΦ)"; subst.
      iExists σ_t, σ_s, e_t, e_s; iFrame.
      apply EqAxiom.bisimulation_is_eq in H, H0; inversion H; inversion H0.
      iSplitL ""; done.
  Qed.

  Lemma sim_expr'_bind {R1 R2} {Re1 Re2} (Φ : exprO R1 -d> exprO R2 -d> _)
    (e_t : exprO Re1) (e_s : exprO Re2) k_t k_s:
    e_t ⪯ e_s [[ fun e_t'' e_s'' => ITree.bind e_t'' k_t ⪯ ITree.bind e_s'' k_s [[ Φ ]] ]] -∗
    ITree.bind e_t k_t ⪯ ITree.bind e_s k_s [[ Φ ]].
  Proof.
    rewrite /sim_expr'.
    iIntros "Hpre" (σ_t σ_s) "SI".
    rewrite /interp_L2.
    iSpecialize ("Hpre" with "SI").

    pose proof (interp_state_bind (handle_L0_L2 η) e_t k_t σ_t).
    pose proof (interp_state_bind (handle_L0_L2 η) e_s k_s σ_s).

    (* Typeclasses instances can't figure out simply [rewrite H]. (a tragedy) *)
    setoid_rewrite itree_eta with (t := ITree.bind e_t k_t) in H.
    setoid_rewrite itree_eta with (t := ITree.bind e_s k_s) in H0.
    pose proof @sim_coindF_Proper as SEP.
    pose proof @lift_rel_Φ_Proper as LEP.
    specialize (SEP PROP _ _ _ Λ η _ R1 R2). repeat red in SEP.
    specialize (LEP R1 R2 Φ).
    specialize (SEP _ _ LEP). clear LEP.
    specialize (SEP _ _ H _ _ H0).
    iApply SEP. clear SEP.

    iPoseProof (sim_coindF_bupd_mono with "[] Hpre") as "Hpre"; last first.
    {
      by iPoseProof ((@sim_coindF_coind_bind PROP _ _ _ Λ η _ _ _ _ _ (lift_rel Φ) _ _
          (λ st : language.state Λ * Re1, interp_state (handle_L0_L2 η) (k_t st.2) st.1)
          (λ st : language.state Λ * Re2, interp_state (handle_L0_L2 η) (k_s st.2) st.1)) with "Hpre") as "Hcoind". }

    clear e_t e_s H H0 σ_t σ_s.
    iIntros (e_t e_s) "HΦ".
    rewrite {1}/lift_rel.
    iDestruct "HΦ" as (????) "(SI & %H_t & %H_s & HΦ)".
    iSpecialize ("HΦ" with "SI").
    iMod "HΦ".
    subst. rewrite /interp_L2.

    pose proof (interp_state_bind (handle_L0_L2 η) e_t0 k_t σ_t).
    pose proof (interp_state_bind (handle_L0_L2 η) e_s0 k_s σ_s).
    eapply eq_sub_eutt in H, H0.

    (* Typeclasses instances can't figure out simply [rewrite H]. *)
    setoid_rewrite itree_eta with (t := ITree.bind e_t0 k_t) in H.
    setoid_rewrite itree_eta with (t := ITree.bind e_s0 k_s) in H0.
    pose proof (@sim_coindF_Proper ) as SEP.
    iApply SEP; eauto.
    { eapply lift_rel_Φ_Proper. }
    { by rewrite interp_state_bind -itree_eta. }
    { by rewrite interp_state_bind -itree_eta. }
    Unshelve. all: exact η.
  Qed.

  Lemma sim_expr'_call_inv {R1 R2 X1 X2}
    c c0 (k_t: X1 -> expr Λ R1) (k_s: X2 -> expr Λ R2) (Φ :expr_rel R1 R2):
    Vis (inl1 c) k_t ⪯ Vis (inl1 c0) k_s [[ Φ ]] -∗
    (∀ σ_t σ_s, state_interp σ_t σ_s ==∗
      (lift_rel Φ (observe (⟦ Vis (inl1 c) k_t⟧ σ_t)) (observe (⟦ Vis (inl1 c0) k_s⟧ σ_s))) ∨

      (∃ C, state_interp σ_t σ_s ∗ call_args_eq c c0 C∗
        (∀ v_t v_s : state Λ * Res (call_events Λ),
           state_interp v_t.1 v_s.1 ∗ res_val_rel v_t.2 v_s.2 C ==∗
           sim_coindF (lift_rel Φ)
              (observe (Tau (⟦k_t (call_returns c v_t.2)⟧ v_t.1)))
              (observe (Tau (⟦k_s (call_returns c0 v_s.2)⟧ v_s.1))))) ∨

      (∃ C, state_interp σ_t σ_s ∗ call_ev c c0 C ∗
        (∀ v_t v_s, state_interp v_t.1 v_s.1 ∗ call_ans c v_t.2 c0 v_s.2 C ==∗
          sim_coindF (lift_rel Φ) (observe (Tau (interp_state (handle_L0_L2 η) (k_t v_t.2) v_t.1)))
                (observe (Tau (interp_state (handle_L0_L2 η) (k_s v_s.2) v_s.1))))))%I.
  Proof.
    iIntros "H" (??) "SI".
    iSpecialize ("H" with "SI").
    iMod "H".
    rewrite /sim_coind'.
    rewrite sim_coindF_unfold; auto.
    setoid_rewrite (sim_indF_unfold (Λ := Λ) (η := η)); auto.
    2 : apply (sim_coindF_ne (η := η)).
    rewrite /sim_expr_inner.
    iMod "H". iDestruct "H" as (C) "H".
    destruct C; try by case_solve; try done.
    { by iLeft. }
    iRight. rewrite /vis_step.
    iDestruct "H" as (????????) "H".

    assert (Ht:⟦ Vis (inl1 c) k_t ⟧ σ_t ≅ Vis e_t k_t0).
    { setoid_rewrite itree_eta at 1. rewrite H. reflexivity. }
    setoid_rewrite interp_state_vis in Ht. cbn in Ht.
    setoid_rewrite bind_trigger in Ht.
    apply eqit_inv in Ht. cbn in Ht. destruct Ht as (?&?&?).
    subst. red in H2, H1. subst. clear H.

    assert (Hs:⟦ Vis (inl1 c0) k_s ⟧ σ_s ≅ Vis e_s k_s0).
    { setoid_rewrite itree_eta at 1. rewrite H0. reflexivity. }
    setoid_rewrite interp_state_vis in Hs. cbn in Hs.
    setoid_rewrite bind_trigger in Hs.
    apply eqit_inv in Hs. cbn in Hs. destruct Hs as (?&?&?).
    subst. red in H1, H. subst. clear H0.

    cbn; repeat unfold resum, ReSum_id, id_, Id_IFun.
    simp handle_call_events.
    iDestruct "H" as "[ Hinner | Hinner ]";
        [iLeft | iRight];
    iDestruct "Hinner" as (?) "(SI & Hcall & Hinner)"; iExists _; iFrame;
    iModIntro; iIntros (??) "H";
    iSpecialize ("Hinner" with "H");
    eapply bisimulation_is_eq in H2, H1; rewrite <- H2; rewrite <- H1; try done.
  Qed.

  Lemma lift_rel_bupd_mono {R1 R2}
    (e_t : st_exprO' R1) (e_s : st_exprO' R2) (Φ Φ' : expr_rel R1 R2):
    (∀ (e_t0 : exprO R1) (e_s0 : exprO R2), Φ e_t0 e_s0 ==∗ Φ' e_t0 e_s0) -∗
    lift_rel Φ e_t e_s ==∗ lift_rel Φ' e_t e_s.
  Proof.
    iIntros "Hmono H".
    rewrite /lift_rel.
    iDestruct "H" as (????) "(SI&H)".
    iDestruct "H" as (??) "HΦ".
    repeat iExists _; iFrame.
    repeat (iSplitL ""; [by iPureIntro | ]).
    iApply ("Hmono" with "HΦ").
  Qed.

  Lemma sim_expr'_bupd_mono {R1 R2} (e_t:expr Λ R1) (e_s:expr Λ R2) (Φ Φ' :expr_rel R1 R2):
    (∀ (e_t0 : exprO R1) (e_s0 : exprO R2), Φ e_t0 e_s0 ==∗ Φ' e_t0 e_s0) -∗
    e_t ⪯ e_s [[ Φ ]] -∗ e_t ⪯ e_s [[ Φ' ]].
  Proof.
    iIntros "HΦ H" (??) "SI".
    iSpecialize ("H" with "SI").
    iMod "H".
    iApply (sim_coindF_bupd_mono with "[HΦ]"); [ | done].
    iIntros (??). iApply (lift_rel_bupd_mono with "HΦ").
    Unshelve. all :auto.
  Qed.

  Definition join_expr {R1 R2} (F: expr_rel R1 R2 -d> expr_rel R1 R2) : expr_rel R1 R2 -d> expr_rel R1 R2:=
    λ Φ, sim_expr' (λ e_t e_s, F Φ e_t e_s ∨ Φ e_t e_s)%I.

  #[global] Instance join_expr_ne {R1 R2} F:
    NonExpansive F →
    NonExpansive (join_expr (R1 := R1) (R2 := R2) F).
  Proof.
    intros HF ??? Heq. rewrite /join_expr /sim_expr'.
    repeat f_equiv. repeat intro. do 6 f_equiv.
    eapply sim_coindF_ne. rewrite /lift_rel.
    repeat intro. solve_proper.
  Qed.

  (* Guarded-ness for coinductive step *)
  Definition lock_step {R1 R2} (Φ: expr_rel R1 R2) (e_t: expr Λ R1) (e_s: expr Λ R2) :=
      (match observe e_t, observe e_s with
          | TauF t, TauF t' => Φ t t'
          | VisF (inl1 c) k, VisF (inl1 c0) k' =>
              ∀ σ_t σ_s, state_interp σ_t σ_s ==∗
                ∃ C, state_interp σ_t σ_s ∗ call_ev c c0 C ∗
                  (∀ v_t v_s, state_interp v_t.1 v_s.1 ∗
                      call_ans c v_t.2 c0 v_s.2 C ==∗
                      state_interp v_t.1 v_s.1 ∗ Φ (k v_t.2) (k' v_s.2))
          | _, _ => |==> ⌜False⌝
       end
      )%I.

  Definition lift_rel_st {R1 R2}: st_expr_rel' R1 R2 -> expr_rel R1 R2 :=
    fun Φ t s => (∀ σ_t σ_s, state_interp σ_t σ_s ==∗ Φ (observe (lift t σ_t)) (observe (lift s σ_s)))%I.

  Definition lift_fix {R1 R2} (F: expr_rel R1 R2 -d> expr_rel R1 R2):
      st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2 :=
    fun Φ t s => (lift_rel (F (lift_rel_st Φ)) t s)%I.

  Lemma sim_expr_paco {R1 R2} F (Φ : expr_rel R1 R2) (e_t:expr Λ R1) (e_s: expr Λ R2):
    NonExpansive (F: expr_rel R1 R2 -d> expr_rel R1 R2) →
    □ (∀ Φ Φ', (∀ e_t e_s, Φ e_t e_s ==∗ Φ' e_t e_s)%I -∗
         ∀ e_t e_s, F Φ e_t e_s -∗ F Φ' e_t e_s) -∗
    □ (∀ Φ e_t e_s, F Φ e_t e_s -∗ lock_step (join_expr F Φ) e_t e_s) -∗
    F Φ e_t e_s -∗ e_t ⪯ e_s [[ Φ ]].
  Proof.
    iIntros (Hne) "#Hb #Hlock_step HF".
    rewrite /sim_expr'. iIntros (??) "SI".
    iApply (sim_coindF_paco (lift_fix F)); last first.
    { rewrite /lift_fix /lift_rel.
      iModIntro. repeat iExists _. iFrame.
      do 2 (iSplitL ""; [ done | ]).
      rewrite /lift_rel_st. iApply "Hb"; [ | done].
      iIntros (??) "HΦ".
      iModIntro. iIntros (??) "SI".
      repeat iExists _; iFrame; eauto. }
    2 : { repeat intro. rewrite /lift_fix /lift_rel.
          do 12 f_equiv. solve_proper. }

    iModIntro. clear Φ e_t e_s. iIntros (Φ e_t e_s) "Hs".
    rewrite /lift_fix /lift_rel.
    iDestruct "Hs" as (????) "(SI&Hs)".
    iDestruct "Hs" as (??) "Hs".
    iSpecialize ("Hlock_step" with "Hs").
    rewrite /lock_step.

    rewrite /lock_st_step. rewrite /lock_step. rewrite H H0.
    destruct (observe e_t0) eqn: Het0; destruct (observe e_s0) eqn: Hes0;
      try iMod "Hlock_step"; try done.
    - assert (Heqt0:observe (⟦ e_t0 ⟧ σ_t0) = TauF (⟦ t ⟧ σ_t0)).
      { assert (⟦ e_t0 ⟧ σ_t0 ≅ Tau (⟦ t ⟧ σ_t0)).
        { rewrite (itree_eta e_t0) Het0. setoid_rewrite interp_state_tau. reflexivity. }
        apply bisimulation_is_eq in H1; subst; by rewrite H1. }

      assert (Heqs0:observe (⟦ e_s0 ⟧ σ_s0) = TauF (⟦ t0 ⟧ σ_s0)).
      { assert (⟦ e_s0 ⟧ σ_s0 ≅ Tau (⟦ t0 ⟧ σ_s0)).
        { rewrite (itree_eta e_s0) Hes0. setoid_rewrite interp_state_tau. reflexivity. }
        apply bisimulation_is_eq in H1; subst; by rewrite H1. }
      rewrite Heqt0 Heqs0; clear Heqt0 Heqs0 Het0 Hes0.
      rewrite /join_expr /join_st_expr.
      rewrite /sim_expr'. iSpecialize ("Hlock_step" with "SI"). iMod "Hlock_step".
      iModIntro. iApply sim_coindF_bupd_mono; [ | done].
      iIntros (??) "H". rewrite /lift_rel.
      iDestruct "H" as (????) "(SI & Hs)".
      iDestruct "Hs" as (??) "[Hs | Hs]"; subst.
      { iLeft; iModIntro; repeat iExists _; iFrame; eauto. }
      { iSpecialize ("Hs" with "SI"). iMod "Hs".
        iModIntro; iRight; repeat iExists _; iFrame; eauto. }
    - destruct e; iMod "Hlock_step"; done.
    - destruct e; iMod "Hlock_step"; done.
    - destruct e, e0; try iMod "Hlock_step"; try done.
       assert (Heqt0:⟦ e_t0 ⟧ σ_t0 ≅ ⟦ e_t0 ⟧ σ_t0) by reflexivity.
      rewrite (itree_eta e_t0) in Heqt0. rewrite Het0 in Heqt0.
      setoid_rewrite interp_state_vis in Heqt0.
      assert (Heqs0:⟦ e_s0 ⟧ σ_s0 ≅ ⟦ e_s0 ⟧ σ_s0) by reflexivity.
      rewrite (itree_eta e_s0) in Heqs0. rewrite Hes0 in Heqs0.
      setoid_rewrite interp_state_vis in Heqs0.
      iSpecialize ("Hlock_step" with "SI"). iMod "Hlock_step".
      cbn in Heqt0. rewrite bind_trigger in Heqt0.
      cbn in Heqs0. rewrite bind_trigger in Heqs0.
      assert (Heqt0':observe (⟦ e_t0 ⟧ σ_t0)
        = VisF (subevent _ (StateEff (call_events Λ) (σ_t0, c)))
            (λ x : state Λ * X, Tau (interp_state (handle_L0_L2 η) (k x.2) x.1))).
      { assert (⟦ e_t0 ⟧ σ_t0 ≅
                  Vis (subevent _ (StateEff (call_events Λ) (σ_t0, c)))
                      (λ x : state Λ * X, Tau (interp_state (handle_L0_L2 η) (k x.2) x.1))).
        { rewrite (itree_eta e_t0) Het0. setoid_rewrite interp_state_vis. cbn.
          rewrite bind_trigger. reflexivity. }
        apply bisimulation_is_eq in H1; subst; by rewrite H1. }

      assert (Heqs0':observe (⟦ e_s0 ⟧ σ_s0)
        = VisF (subevent _ (StateEff (call_events Λ) (σ_s0, c0)))
            (λ x : state Λ * X0, Tau (interp_state (handle_L0_L2 η) (k0 x.2) x.1))) .
      { assert (H1:(⟦ e_s0 ⟧ σ_s0)
        ≅ Vis (subevent _ (StateEff (call_events Λ) (σ_s0, c0)))
            (λ x : state Λ * X0, Tau (interp_state (handle_L0_L2 η) (k0 x.2) x.1))) .
        { rewrite (itree_eta e_s0) Hes0. setoid_rewrite interp_state_vis.
          rewrite bind_trigger. reflexivity. }
        apply bisimulation_is_eq in H1; subst; by rewrite H1. }

      rewrite Heqt0' Heqs0'.
      iModIntro.

      cbn; repeat unfold resum, ReSum_id, id_, Id_IFun.
      simp handle_call_events.

      iDestruct "Hlock_step" as (?) "(Hev & Hcont)"; iFrame.
      iRight.
      iDestruct "Hcont" as "(Hev & Hcont)"; iFrame.
      iExists _; iFrame.
      iIntros (??) "Hans". iSpecialize ("Hcont" with "Hans").
      iMod "Hcont".
      iDestruct "Hcont" as "(SI & Hcont)".

      rewrite /join_expr /join_st_expr.
      iApply sim_coindF_tau.

      subst. rewrite /sim_expr'.
      iSpecialize ("Hcont" with "SI").
      iMod "Hcont".
      iModIntro. iApply sim_coindF_bupd_mono; [ | done].
      iIntros (??) "H". rewrite /lift_rel.
      iDestruct "H" as (????) "(SI & H)".
      iDestruct "H" as (??) "[H | H]".
      { iModIntro. iLeft. repeat iExists _. iFrame.
        subst; auto. }
      { iRight. rewrite /lift_rel_st.
        iSpecialize ("H" with "SI"). iMod "H".
        subst. rewrite /lift. auto. }
  Qed.

  (* LATER: Should be simpler corollary of [sim_expr_lift] *)
  Lemma sim_expr'_pure {R1 R2} Φ (e_t:expr Λ R1) (e_s: expr Λ R2):
    e_t ⪯ e_s [[ fun e_t e_s => ∃ v_t v_s, ⌜Ret v_t = e_t⌝ ∗ ⌜Ret v_s = e_s⌝ ∗ Φ e_t e_s ]] -∗
    e_t ⪯ e_s [{ Φ }].
  Proof.
    rewrite /sim_expr' sim_expr_eq.
    cbn. iIntros "H".
    iIntros (??) "SI".
    iSpecialize ("H" with "SI").
    iApply sim_coindF_bupd_mono; [ | done].
    iIntros (??) "H".
    rewrite /lift_expr_rel /lift_rel.

    iDestruct "H" as (????) "(SI & H)".
    iDestruct "H" as (??) "H".
    iDestruct "H" as (????) "H". subst.
    iModIntro. iExists σ_t0, v_t, σ_s0, v_s.
    iFrame.
    iSplitL ""; iPureIntro;
    setoid_rewrite interp_state_ret; by rewrite <- itree_eta.
    Unshelve. all : eauto.
  Qed.

  Lemma sim_expr_lift {R1 R2} (Φ : expr_rel R1 R2) (e_t:expr Λ R1) (e_s: expr Λ R2):
    e_t ⪯ e_s [{ Φ }] -∗ e_t ⪯ e_s [[ Φ ]].
  Proof.
    rewrite /sim_expr' sim_expr_eq.
    cbn. iIntros "H".
    iIntros (??) "SI".
    iSpecialize ("H" with "SI").
    iApply sim_coindF_bupd_mono; [ | done].
    iIntros (??) "H".
    rewrite /lift_expr_rel /lift_rel.
    iDestruct "H" as (??????) "(SI&HΦ)".
    iModIntro. iExists σ_t0, σ_s0, (Ret v_t), (Ret v_s).
    iFrame.
    iSplitL ""; iPureIntro.
    { assert (⟦ Ret v_t ⟧ σ_t0 ≅ ⟦ Ret v_t ⟧ σ_t0) by reflexivity.
      setoid_rewrite interp_state_ret at 1 in H1. rewrite H in H1.
      apply bisimulation_is_eq in H1. rewrite <- H1. done. }
    assert (⟦ Ret v_s ⟧ σ_s0 ≅ ⟦ Ret v_s ⟧ σ_s0) by reflexivity.
    setoid_rewrite interp_state_ret at 1 in H1. rewrite H0 in H1.
    apply bisimulation_is_eq in H1. rewrite <- H1. done.
  Qed.

  Lemma sim_lift_coind {R1 R2} (inv : expr Λ R1 → expr Λ R2 → PROP) e_t e_s Φ :
    (□ ∀ e_t e_s,
      inv e_t e_s -∗
        lock_step (sim_expr' (λ e_t'' e_s'', Φ e_t'' e_s'' ∨ inv e_t'' e_s'')) e_t e_s) -∗
    inv e_t e_s -∗
    e_t ⪯ e_s [[ Φ ]].
  Proof.
    pose (F  := (λ Ψ e_t e_s, (∀ e_t e_s, Φ e_t e_s ==∗ Ψ e_t e_s) ∗ inv e_t e_s)%I).
    iIntros "#H Inv".
    iApply (sim_expr_paco F).
    { solve_proper. }
    { iModIntro. iIntros (??) "HI". rewrite /F.
      iIntros (??) "(HΦ&Hinv)". iFrame.
      iIntros (??) "Hϕ". iSpecialize ("HΦ" with "Hϕ").
      iSpecialize ("HI" with "HΦ"). do 2 iMod "HI". done. }
    - iModIntro. clear e_t e_s. iIntros (Ψ e_t e_s) "[Himpl Hinv]".
      rewrite /lock_step.
      iSpecialize ("H" with "Hinv").
      destruct (observe e_t) eqn: Ht; destruct (observe e_s) eqn: Hs;
        try destruct e; try destruct e0; try iMod "H"; try iDestruct "H" as "%H"; try done.
      { rewrite /join_expr.
        rewrite /sim_expr'. iIntros (??) "SI".
        iSpecialize ("H" with "SI"). iMod "H".
        iApply (sim_coindF_bupd_mono with "[Himpl] [H]"); [ | done].
        rewrite /lift_rel. iIntros (??) "H".
        iDestruct "H" as (????) "(SI&H)".
        iDestruct "H" as (?) "H". subst.
        iDestruct "H" as "(?&H)"; iFrame.
        iDestruct "H" as "[H | H]".
        - iSpecialize ("Himpl" with "H"); iMod "Himpl".
          iModIntro. repeat iExists _; iFrame; eauto.
        - iModIntro. repeat iExists _; iFrame; eauto.
          iSplitL ""; eauto.
          iLeft. iFrame. }
      { iIntros (??) "SI".
        iSpecialize ("H" with "SI").
        iMod "H". iDestruct "H" as (?) "(SI & ?&H)".
        iExists _; iFrame.
        iModIntro.
        iIntros (??) "Hev".
        iSpecialize ("H" with "Hev"). iMod "H".
        iDestruct "H" as "(SI & H)"; iFrame.
        rewrite /join_expr.
        iApply (sim_expr'_bupd_mono with "[Himpl]"); [ | done].
        iIntros (??) "H".
        iDestruct "H" as "[H | H]".
        - iSpecialize ("Himpl" with "H"); iMod "Himpl".
          iModIntro. repeat iExists _; iFrame; eauto.
        - rewrite /F. iModIntro. iLeft. iFrame. }
    - rewrite /F. iFrame. by iIntros.
  Qed.

  Lemma sim_expr'_base {R1 R2} (e_t:exprO R1) (e_s:exprO R2) Φ :
    ⊢ Φ e_t e_s -∗ e_t ⪯ e_s [[ Φ ]].
  Proof.
    iIntros "HΦ". rewrite /sim_expr'.
    iIntros (σ_t σ_s) "SI".

    rewrite /sim_coind'.
    rewrite sim_coindF_unfold sim_indF_unfold.
    iApply sim_expr_inner_base; iFrame.

    rewrite /lift_rel.

    iModIntro. iIntros. iExists σ_t, σ_s, e_t, e_s.
    iFrame; eauto.
  Qed.

  Ltac sim'_rewrite EQ EQ' R1 R2 Φ :=
    pose proof @sim_coindF_Proper as SEP;
    pose proof @lift_rel_Φ_Proper as LEP;
    specialize (SEP PROP _ _ _ Λ η _ R1 R2); repeat red in SEP;
    specialize (LEP R1 R2 Φ);
    specialize (SEP _ _ LEP); clear LEP;
    specialize (SEP _ _ EQ _ _ EQ');
    iApply SEP; clear SEP; clear EQ EQ'.

  Lemma sim_expr'_tau_base {R1 R2} (e_t:exprO R1) (e_s:exprO R2) Φ :
    ⊢ Φ e_t e_s -∗ Tau e_t ⪯ Tau e_s [[ Φ ]].
  Proof.
    rewrite /sim_expr'; simpl.
    iIntros "Hpre" (σ_t σ_s) "SI".
    rewrite /interp_L2.

    pose proof (interp_state_tau _ e_t (handle_L0_L2 η) σ_t).
    pose proof (interp_state_tau _ e_s (handle_L0_L2 η) σ_s).
    sim'_rewrite H H0 R1 R2 Φ.

    iModIntro.
    rewrite (sim_coindF_unfold (lift_rel Φ)) sim_indF_unfold.
    unfold sim_expr_inner; cbn.
    provide_case: TAU_STEP.
    iApply sim_coindF_base.

    rewrite /lift_rel.

    iExists σ_t, σ_s, e_t, e_s.
    iFrame; eauto.
  Qed.

  Lemma sim_expr'_tau {R1 R2} (e_t:exprO R1) (e_s:exprO R2) Φ :
    ⊢ e_t ⪯ e_s [[ Φ ]] -∗ Tau e_t ⪯ Tau e_s [[ Φ ]].
  Proof.
    rewrite /sim_expr'; simpl.
    iIntros "Hpre" (σ_t σ_s) "SI".
    rewrite /interp_L2.

    pose proof (interp_state_tau _ e_t (handle_L0_L2 η) σ_t).
    pose proof (interp_state_tau _ e_s (handle_L0_L2 η) σ_s).
    sim'_rewrite H H0 R1 R2 Φ.

    iModIntro.
    rewrite (sim_coindF_unfold (lift_rel Φ)) sim_indF_unfold.
    unfold sim_expr_inner; cbn.
    iDestruct ("Hpre" with "SI") as ">Hpre".
    provide_case: TAU_STEP.

    rewrite /sim_coind'.
    rewrite sim_coindF_unfold; done.
  Qed.

  Section iter_sim.
    Context {I R : Type}.
    Context (f_t f_s : I -> (expr Λ) (I + R)) (init : I -> I -> PROP)
        (Ψ : expr Λ R → expr Λ R → PROP) (inv : PROP).

    Variant iter_case := | ret_iter | tau_iter | vis_iter.

    Definition ret_iter_body i_t i_s :=
      (∃ l l' : I, ⌜f_t i_t = Ret (inl l)⌝ ∗ ⌜f_s i_s = Ret (inl l')⌝ ∗
                  ITree.iter f_t l
                  ⪯
                  ITree.iter f_s l'
                  [[ λ r_t r_s : exprO R,
                        (∃ v_t v_s : I,
                          ⌜f_t i_t = Ret (inl v_t)
                            ∧ f_s i_s = Ret (inl v_s) ∧ r_t = ITree.iter f_t v_t ∧ r_s = ITree.iter f_s v_s⌝ ∗
                          init v_t v_s ∗ inv) ∨ Ψ r_t r_s ]])%I.

    Definition tau_iter_body i_t i_s:=
      (∃ t t', ⌜f_t i_t = Tau t⌝ ∗ ⌜f_s i_s = Tau  t'⌝ ∗
        ITree.bind t (λ lr , match lr with
                                            | inl l => Tau (ITree.iter f_t l)
                                            | inr r => Ret r
                                            end) ⪯
        ITree.bind t' (λ lr , match lr with
                                            | inl l => Tau (ITree.iter f_s l)
                                            | inr r => Ret r
                                            end)
        [[ fun r_t r_s =>
              (∃ v_t v_s, ⌜f_t i_t = Ret (inl v_t) /\ f_s i_s = Ret (inl v_s) /\
                          r_t = ITree.iter (I:=I) f_t v_t /\ r_s = ITree.iter f_s v_s⌝ ∗
                          init v_t v_s ∗ inv) ∨ Ψ r_t r_s ]])%I.

    Definition vis_iter_body i_t i_s:=
      (∃ X X0 (c: _ X) k (c0: _ X0) k',
        ⌜f_t i_t = Vis (inl1 c) k⌝ ∗ ⌜f_s i_s = Vis (inl1 c0) k'⌝ ∗
        ∀ σ_t σ_s, state_interp σ_t σ_s ==∗
        ∃ C, (state_interp σ_t σ_s ∗
          call_ev c c0 C) ∗
          (∀ (v_t0 : state Λ * _) (v_s0 : state Λ * _),
            state_interp v_t0.1 v_s0.1 ∗
            call_ans c v_t0.2 c0 v_s0.2 C ==∗
            state_interp v_t0.1 v_s0.1 ∗
        ITree.bind (k v_t0.2) (λ lr , match lr with
                                            | inl l => Tau (ITree.iter f_t l)
                                            | inr r => Ret r
                                            end) ⪯
        ITree.bind (k' v_s0.2) (λ lr , match lr with
                                            | inl l => Tau (ITree.iter f_s l)
                                            | inr r => Ret r
                                            end)
      [[ fun r_t r_s =>
            (∃ v_t v_s, ⌜f_t i_t = Ret (inl v_t) /\ f_s i_s = Ret (inl v_s) /\
                        r_t = ITree.iter (I:=I) f_t v_t /\ r_s = ITree.iter f_s v_s⌝ ∗
                        init v_t v_s ∗ inv) ∨ Ψ r_t r_s ]]))%I.

    Lemma sim_expr'_iter :
      □ (inv -∗
          ∀ i_t i_s, init i_t i_s -∗
          (∃ c:iter_case,
              match c with
                | ret_iter => ret_iter_body i_t i_s
                | tau_iter => tau_iter_body i_t i_s
                | vis_iter => vis_iter_body i_t i_s
              end)) -∗
      inv -∗
      ∀ i_t i_s, init i_t i_s -∗
      ITree.iter (I := I) f_t i_t ⪯ ITree.iter f_s i_s [[ Ψ ]].
    Proof.
      iIntros "#Hrec Hinv". iIntros (??) "Hinit".
      iApply (sim_lift_coind (λ r_t r_s,
              (∃ v_t v_s, ⌜r_t = ITree.iter (I:=I) f_t v_t /\ r_s = ITree.iter f_s v_s⌝ ∗
                          init v_t v_s ∗ inv))%I); last first.
      { iExists i_t, i_s; iFrame; done. }
      iModIntro.
      iIntros (e_t e_s) "[% [% [% (Hinit&Hinv)]]]".
      destruct H as (-> & ->).
      iSpecialize ("Hrec" with "Hinv Hinit").
      pose proof (unfold_iter f_t v_t) as Hiter; eapply bisimulation_is_eq in Hiter; rewrite Hiter.
      pose proof (unfold_iter f_s v_s) as Hiter'; eapply bisimulation_is_eq in Hiter'; rewrite Hiter'.

      clear Hiter Hiter'.

      epose proof (unfold_bind (f_t v_t) (λ lr : I + R, match lr with
                                          | inl l => Tau (ITree.iter f_t l)
                                          | inr r => Ret r
                                          end)) as Hbind;
        eapply bisimulation_is_eq in Hbind;
        rewrite Hbind; clear Hbind.
      epose proof (unfold_bind (f_s v_s) (λ lr : I + R, match lr with
                                              | inl l => Tau (ITree.iter f_s l)
                                              | inr r => Ret r
                                              end)) as Hbind;
        eapply bisimulation_is_eq in Hbind;
        rewrite Hbind; clear Hbind.

      pose proof (itree_eta (f_t v_t)) as Heta; eapply bisimulation_is_eq in Heta;
        rewrite {1}Heta; clear Heta.
      pose proof (itree_eta (f_s v_s)) as Heta; eapply bisimulation_is_eq in Heta;
        rewrite {1}Heta; clear Heta.

      rewrite /lock_step. Unshelve.
      all: try eauto.
      iDestruct "Hrec" as (c) "Hrec". destruct c eqn: Hcase.
      { iDestruct "Hrec" as (????) "Hrec". inv H; inv H0. rewrite H1 H2; cbn.

        iApply (sim_expr'_bupd_mono with "[] [Hrec]"); [ | done].
        iIntros (??) "[H | H]".
        - iDestruct "H" as (???) "(Hinit&Hinv)".
          destruct H as (?&?&?&?); subst.
          iModIntro. iRight; repeat iExists _; iSplitL ""; iFrame; eauto.
        - by iLeft. }
      { iDestruct "Hrec" as (????) "Hrec". inv H; inv H0. rewrite H1 H2; cbn.
        iApply (sim_expr'_bupd_mono with "[] [Hrec]"); [ | done].
        iIntros (??) "[H | H]".
        - iDestruct "H" as (???) "(Hinit&Hinv)".
          destruct H as (?&?&?&?); subst.
          iModIntro. iRight; repeat iExists _; iSplitL ""; iFrame; eauto.
        - by iLeft. }
      { iDestruct "Hrec" as (????????) "Hrec". inv H; inv H0. rewrite H1 H2; cbn.
        iIntros (??) "SI'".

        unfold resum, ReSum_id, id_, Id_IFun.
        simp handle_call_events.
        iSpecialize ("Hrec" with "SI'"); iMod "Hrec".
        iDestruct "Hrec" as (?) "((SI & Hev)&Hrec)".
        iExists _; iFrame. iModIntro. iIntros (??) "Hans".
        iSpecialize ("Hrec" with "Hans").
        iMod "Hrec". iDestruct "Hrec" as "(SI & Hrec)"; iFrame.
        iApply sim_expr'_bupd_mono; [ | done].
        iIntros (??) "H".
        iDestruct "H" as "[H | H]".
        { iDestruct "H" as (???) "(HInit & HInv)".
          destruct H as (?&?&?&?); subst.
          iModIntro; iRight; repeat iExists _; iFrame; done. }
        { by iLeft. } }
    Qed.

  End iter_sim.


  Definition guarded_iter {E : Type -> Type} {R I: Type}
          (step : I -> itree E (I + R)) : I -> itree E R :=
    cofix iter_ (i : I) : itree E R :=
      ITree.bind (Tau (step i)) (fun lr => match lr with
                                        | inl l => Tau (iter_ l)
                                        | inr r => Ret r
                                        end).

  (* Definition guarded_iter {E : Type -> Type} {R I: Type} *)
  (*          (step : I -> itree E (I + R)) : I -> itree E R := *)
  (*   cofix iter_ (i : I) : itree E R := Tau (lr (step i);; match lr with *)
  (*                                                     | inl l => Tau (iter_ l) *)
  (*                                                     | inr r => Ret r *)
  (*                                                     end). *)

  (* How easy is it to prove this in itree simulation? (compare ease of proof) *)
  (* (Tau body;; (Tau Tau body;; Tau Tau body...)) ~ (body ;; (Tau body;; Tau body...)) *)

  Definition guarded_interp_mrec {D E : Type -> Type}
            (ctx : D ~> itree (D +' E)) : itree (D +' E) ~> itree E :=
    fun R =>
      guarded_iter
        (λ t : itree (D +' E) R,
          match observe t with
          | RetF r => Ret (inr r)
          | TauF t0 => Ret (inl t0)
          | @VisF _ _ _ X (inl1 d) k => Ret (inl (ITree.bind (ctx X d) k))
          | @VisF _ _ _ X (inr1 e) k => Vis e (λ x : X, Ret (inl (k x)))
          end).

  Arguments guarded_interp_mrec {_ _} _ {_}.

  Definition guarded_mrec {D E : Type -> Type}
            (ctx : D ~> itree (D +' E)) : D ~> itree E :=
    fun R d => guarded_interp_mrec ctx (ctx _ d).

  Lemma unfold_guarded_aloop_ {E A B} (f : A -> itree E (A + B)) (x : A) :
    observing eq
      (guarded_iter f x)
      (ITree.bind (Tau (f x)) (fun lr => ITree.on_left lr l (Tau (guarded_iter f l)))).
  Proof. constructor; reflexivity. Qed.

  Lemma unfold_guarded_iter {E A B} (f : A -> itree E (A + B)) (x : A) :
    (guarded_iter f x) ≅ ITree.bind (Tau (f x)) (fun lr => ITree.on_left lr l (Tau (guarded_iter f l))).
  Proof.
    rewrite unfold_guarded_aloop_. reflexivity.
  Qed.

  Lemma guarded_iter_eutt:
    forall (E : Type -> Type) (R I : Type) (step : I -> itree E (I + R)) x,
      guarded_iter step x ≈ ITree.iter step x.
  Proof.
    intros E R I. einit. ecofix CIH.
    intros. rewrite unfold_guarded_iter unfold_iter.
    ebind. econstructor.
    - rewrite tau_eutt; reflexivity.
    - intros; subst; destruct u2; [ estep | ].
      efinal.
  Qed.

  Definition guarded_iter' (E : Type -> Type) (R I : Type) (step : I -> itree E (I + R)) x:=
    Tau (ITree.iter step x).

  Lemma guarded_iter_eutt':
    forall (E : Type -> Type) (R I : Type) (step : I -> itree E (I + R)) x,
      guarded_iter step x ≈ ITree.iter step x.
  Proof.
    intros E R I.
    einit. ecofix CIH.
    intros. rewrite unfold_guarded_iter unfold_iter.
    ebind. econstructor.
    - rewrite tau_eutt; reflexivity.
    - intros; subst; destruct u2; [ estep | ].
      efinal.
  Qed.

  Lemma sim_expr_guarded_iter
    {I R : Type} (f_t f_s : I -> (expr Λ) (I + R)) (inv : I -> I -> PROP)
        (Ψ : exprO R → exprO R → PROP) :
    □ (∀ i_t i_s, inv i_t i_s -∗
        f_t i_t ⪯ f_s i_s
        [[ fun e_t e_s => (∃ r_t r_s, ⌜e_t = Ret (inl r_t)⌝ ∗ ⌜e_s = Ret (inl r_s)⌝ ∗ inv r_t r_s) ∨
              (∃ r_t r_s, ⌜e_t = Ret (inr r_t)⌝ ∗ ⌜e_s = Ret (inr r_s)⌝ ∗ Ψ (Ret r_t) (Ret r_s)) ]]) -∗
    ∀ i_t i_s, inv i_t i_s -∗
    guarded_iter (I := I) f_t i_t ⪯ guarded_iter f_s i_s [[ Ψ ]].
  Proof.
    iIntros "#Hrec". iIntros (??) "Hinv".
    iApply (sim_lift_coind (λ r_t r_s,
            (∃ v_t v_s, ⌜r_t = guarded_iter (I:=I) f_t v_t /\ r_s = guarded_iter f_s v_s⌝ ∗
                        inv v_t v_s))%I); last first.
    { iExists i_t, i_s; iFrame; done. }
    iModIntro.
    iIntros (e_t e_s) "[% [% [% Hinv]]]".
    destruct H as (-> & ->).
    iSpecialize ("Hrec" with "Hinv").
    pose proof (unfold_guarded_iter f_t v_t) as Hiter;
      eapply EqAxiom.bisimulation_is_eq in Hiter; rewrite Hiter.
    pose proof (unfold_guarded_iter f_s v_s) as Hiter';
      eapply EqAxiom.bisimulation_is_eq in Hiter'; rewrite Hiter'.
    clear Hiter Hiter'.
    rewrite /lock_step. cbn.
    iApply sim_expr'_bind.
    iApply sim_expr'_bupd_mono; [ | done].

    iIntros (r_t r_s) "[ H | H ]".

    { iDestruct "H" as (????) "Hinv". subst.
      do 2 rewrite bind_ret_l.
      iApply sim_expr'_tau_base. iRight; eauto. }
    { iDestruct "H" as (????) "Hinv". subst.
      do 2 rewrite bind_ret_l.
      iApply sim_expr'_base. by iLeft. }
  Qed.

  Lemma sim_expr_guarded_iter'
    {I R : Type} (f_t f_s : I -> (exprO) (I + R)) (inv : I -> I -> PROP)
        (Ψ : exprO R → exprO R → PROP) :
    □ (∀ i_t i_s, inv i_t i_s -∗
        f_t i_t ⪯ f_s i_s
        [[ fun e_t e_s => (∃ r_t r_s, ⌜e_t = Ret (inl r_t)⌝ ∗ ⌜e_s = Ret (inl r_s)⌝ ∗ inv r_t r_s) ∨
              (∃ r_t r_s, ⌜e_t = Ret (inr r_t)⌝ ∗ ⌜e_s = Ret (inr r_s)⌝ ∗ Ψ (Ret r_t) (Ret r_s)) ]]) -∗
    ∀ i_t i_s, inv i_t i_s -∗
    guarded_iter' _ _ I f_t i_t ⪯ guarded_iter' _ _ I f_s i_s [[ Ψ ]].
  Proof.
    iIntros "#Hrec". iIntros (??) "Hinv".
    iApply (sim_lift_coind (λ r_t r_s,
            (∃ v_t v_s, ⌜r_t = guarded_iter' _ _ I f_t v_t /\ r_s = guarded_iter' _ _ I f_s v_s⌝ ∗
                        inv v_t v_s))%I); last first.
    { iExists i_t, i_s; iFrame. done. }
    iModIntro.
    iIntros (e_t e_s) "[% [% [% Hinv]]]".
    destruct H as (-> & ->).
    iSpecialize ("Hrec" with "Hinv").
    rewrite /guarded_iter'.
    pose proof (unfold_iter f_t v_t) as Hiter;
      eapply EqAxiom.bisimulation_is_eq in Hiter; rewrite Hiter.
    pose proof (unfold_iter f_s v_s) as Hiter';
      eapply EqAxiom.bisimulation_is_eq in Hiter'; rewrite Hiter'.
    clear Hiter Hiter'.
    rewrite /lock_step. cbn.
    iApply sim_expr'_bind.
    iApply sim_expr'_bupd_mono; [ | done].

    iIntros (r_t r_s) "[ H | H ]".

    { iDestruct "H" as (????) "Hinv". subst.
      do 2 rewrite bind_ret_l.
      iApply sim_expr'_base.
      iRight; eauto. }
    { iDestruct "H" as (????) "Hinv". subst.
      do 2 rewrite bind_ret_l.
      iApply sim_expr'_base. by iLeft. }
  Qed.

  Lemma sim_expr_ret_inv {R1 R2} (r_t: R1) (r_s: R2) σ_t σ_s Φ:
    ⊢ state_interp σ_t σ_s ∗ Ret r_t ⪯ Ret r_s [{ (v_t, v_s), Φ v_t v_s }] ==∗
      state_interp σ_t σ_s ∗ Φ r_t r_s.
  Proof.
    iIntros "[SI H]". rewrite sim_expr_unfold. cbn.
    iSpecialize ("H" with "SI"). iMod "H". iDestruct "H" as (?) "H".
    destruct c.
    - rewrite /lift_expr_rel.
      iDestruct "H" as (??????) "(?&H)".
      iDestruct "H" as (????) "H".
      apply eqit_inv in H; apply eqit_inv in H0.
      cbn in H, H0. inv H; inv H0.
      subst.
      apply eqit_inv in H1; apply eqit_inv in H2.
      cbn in H1, H2. subst.
      iModIntro; iFrame.
    - rewrite /stutter_l.
      iDestruct "H" as (??) "H". inv H.
    - rewrite /stutter_r.
      iDestruct "H" as (??) "H". inv H.
    - rewrite /tau_step.
      iDestruct "H" as (???) "H". inv H.
    - rewrite /vis_step.
      iDestruct "H" as (???????) "H". inv H.
    - rewrite /source_ub.
      iDestruct "H" as (???) "%H". inv H.
    - rewrite /source_exc.
      iDestruct "H" as (???) "%H". inv H.
  Qed.

  Lemma sim_coindF_vis_ret_abs {R1 R2 X} r e (k : X -> _) (Φ: exprO R1 -d> exprO R2 -d> PROP) :
    ⊢ sim_coindF (lift_expr_rel Φ) (VisF e k) (RetF r) ==∗ False.
  Proof.
    iIntros "H".
    rewrite sim_coindF_unfold sim_indF_unfold /sim_expr_inner. iMod "H".
    iDestruct "H" as (?) "H".
    destruct c.
    - rewrite /lift_expr_rel.
      iDestruct "H" as (??????) "H".
      apply eqit_inv in H; inv H.
    - rewrite /stutter_l.
      iDestruct "H" as (??) "H". inv H.
    - rewrite /stutter_r.
      iDestruct "H" as (??) "H". inv H.
    - rewrite /tau_step.
      iDestruct "H" as (???) "H". inv H.
    - rewrite /vis_step.
      iDestruct "H" as (????????) "H". inv H0.
    - rewrite /source_ub.
      iDestruct "H" as (???) "%H". inv H.
    - rewrite /source_exc.
      iDestruct "H" as (???) "%H". inv H.
  Qed.

  (* The trigger for [state_events] should be stated as primitive laws for the
    specific language: it is not possible in advance to know how the
    [state_handler] will deal with certain events. *)

End sim_expr_properties.

#[global]
  Notation "et '⪯' es ⦉ Φ ⦊" := (sim_expr' Φ et es) (at level 70, Φ at level 200,
    format "'[hv' et  '/' '⪯'  '/' es  '/' ⦉  '[ ' Φ  ']' ⦊ ']'") : bi_scope.
