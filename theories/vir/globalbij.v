(** * Bijection between global variables *)

From iris.prelude Require Import options.

From velliris.program_logic Require Import program_logic.
From velliris.vir Require Import heapbij spec.

From Vellvm Require Import Semantics.LLVMEvents Handlers.
From ITree Require Import ITree Eq Eq.EqAxiom.

Set Default Proof Using "Type*".

Section globalbij.

  Context {Σ : gFunctors} `{!sheapGS Σ, !checkedoutGS Σ, !heapbijGS Σ}.

  Lemma sim_global_read (f: LLVMAst.global_id) Φ:
    (∀ (v_t v_s : dvalue),
        dval_rel v_s v_t -∗
        Φ v_s v_t) -∗
    trigger (GlobalRead f) ⪯ trigger (GlobalRead f)
    [{ (v_t, v_s), Φ v_t v_s }].
  Proof.
    iIntros "Hl".

    rewrite sim_expr_unfold.
    iIntros "%σ_t %σ_s SI".
    destruct σ_t as ((?&?)&?&?); destruct σ_s as ((?&?)&?&?).
    provide_case: TAU_STEP.

    (iSplitL ""; [ iPureIntro | ]).
    { apply EqAxiom.bisimulation_is_eq. rewrite <- itree_eta.
      rewrite /interp_L2 StateFacts.interp_state_trigger_eqit; cbn; rewrite /add_tau.
      rewrite bind_tau. apply eqitree_Tau; cbn. rewrite bind_bind.
      reflexivity. }

    (iSplitL ""; [ iPureIntro | ]).
    { apply EqAxiom.bisimulation_is_eq. rewrite <- itree_eta.
      rewrite /interp_L2 StateFacts.interp_state_trigger_eqit; cbn; rewrite /add_tau.
      rewrite bind_tau. apply eqitree_Tau; cbn. rewrite bind_bind.
      reflexivity. }

    cbn.
    iDestruct "SI" as (???) "(Hhs & Hht & Hgv & Hi & %WF & Hlo & Hbij)".
    iDestruct "Hbij" as "(%Hsub&#Hgs_t&#Hgs_s&#Hrel)".
    destruct (g0 !! f) eqn: Hs.

    { assert (Hs'' := Hs).

      assert (Hs' := Hs).
      apply elem_of_dom_2 in Hs.
      iDestruct (big_sepM_lookup_acc _ _ _ _ Hs' with "Hrel") as "(Helem & Hrel')".

      iAssert (global sheapG_heap_source f d)%I as "Hs_elem".
      { rewrite global_eq /global_def.
        iExists g0.
        iSplitL ""; [ | iApply "Hgs_s"].
        by iPureIntro. }
      iDestruct "Helem" as (v' Hv') "Helem".
      iDestruct (global_in with "Hgs_s Hs_elem") as %Hin.
      iDestruct (global_intro with "Hgs_t") as "#Hg_t".
      { eauto. }

      rewrite Hv' Hin; cbn.

      iApply sim_coindF_tau; iApply sim_coindF_base.
      rewrite /lift_expr_rel.
      iExists (g, p, (p0, f0)), v', (g0, p1, (p2, f1)), d; iFrame.
      do 2 (iSplitL ""; [ iPureIntro; rewrite <- itree_eta; reflexivity | ]).
      rewrite /state_interp. cbn.
      iFrame.
      iSplitL "Hhs Hht Hgv Hi".
      { iExists C, S, G. repeat iExists _. iFrame. destruct p; iFrame.
        iSplitL ""; first done.

        rewrite /globalbij_interp.
        iSplitL ""; [ iPureIntro; exact Hsub
          | iSplitL "" ; [iApply "Hgs_t" | ] ].
        iSplitL "" ; [iApply "Hgs_s" | ].
        iApply "Hrel". }
      iSpecialize ("Hl" with "Helem").
      iExists v', d.
      do 2 (iSplitL ""; [ iPureIntro; reflexivity | ]); done.
    }
    { cbn.
      rewrite sim_coindF_unfold sim_indF_unfold /sim_expr_inner.
      provide_case: SOURCE_EXC.
      iPureIntro. rewrite Hs. cbn. reflexivity. }
  Qed.

  Lemma sim_global_read1 (f: LLVMAst.global_id) g g0 x_t x_s:
    g !! f = Some x_t ->
    g0 !! f = Some x_s ->
    target_globals g -∗
    source_globals g0 -∗
    trigger (GlobalRead f) ⪯ trigger (GlobalRead f)
    [{ (v_t, v_s), dval_rel v_t v_s ∗ ⌜v_t = x_t⌝ ∗ ⌜v_s = x_s⌝ }].
  Proof.
    iIntros (??) "Hg Hg0".

    rewrite sim_expr_eq.
    iIntros "%σ_t %σ_s SI".
    destruct σ_t as ((?&?)&?&?); destruct σ_s as ((?&?)&?&?).
    iDestruct "SI" as (???) "(Hhs & Hht & Hgv & Hi & %WF & Hlo & Hbij)".
    iDestruct "Hbij" as "(%Hsub&#Hgs_t&#Hgs_s&#Hrel)".
    iDestruct (globals_agree with "Hgs_t Hg") as %Ht; subst.
    iDestruct (globals_agree with "Hgs_s Hg0") as %Ht; subst.
    setoid_rewrite StateFacts.interp_state_vis; setoid_rewrite bind_tau; cbn.
    cbn in *. rewrite H H0.

    iApply sim_coind_tau.
    rewrite bind_bind !bind_ret_l.
    iApply sim_coind_tau.
    rewrite !StateFacts.interp_state_ret.
    iApply sim_coind_base; eauto.
    iFrame.
      iSplitL "Hhs Hht Hgv Hi".
    { iExists C, S, G. repeat iExists _. iFrame. destruct p; iFrame.
      repeat (iSplitL ""; first done). done. }
    iExists _, _; eauto.
    repeat (iSplitL ""; first done). cbn.
    iDestruct (big_sepM_lookup_acc _ _ _ _ H0 with "Hrel") as "(Helem & Hrel')".
    iDestruct "Helem" as (??) "#Helem".
    rewrite H1 in H; inv H. iFrame "Helem"; done.
  Qed.

  Lemma sim_global_write f v_t v_s g g0:
    g !! f = Some v_t ->
    g0 !! f = Some v_s ->
    target_globals g -∗
    source_globals g0 -∗
    trigger (GlobalWrite f v_t) ⪯ trigger (GlobalWrite f v_s)
    [{ (v_t, v_s), True }].
  Proof.
    iIntros (??) "Hg Hg0".

    rewrite sim_expr_unfold.
    iIntros "%σ_t %σ_s SI".
    destruct σ_t as ((?&?)&?&?); destruct σ_s as ((?&?)&?&?).
    provide_case: TAU_STEP.

    (iSplitL ""; [ iPureIntro | ]).
    { apply EqAxiom.bisimulation_is_eq. rewrite <- itree_eta.
      rewrite /interp_L2 StateFacts.interp_state_trigger_eqit; cbn; rewrite /add_tau.
      rewrite bind_tau. apply eqitree_Tau; cbn. rewrite bind_bind.
      reflexivity. }

    (iSplitL ""; [ iPureIntro | ]).
    { apply EqAxiom.bisimulation_is_eq. rewrite <- itree_eta.
      rewrite /interp_L2 StateFacts.interp_state_trigger_eqit; cbn; rewrite /add_tau.
      rewrite bind_tau. apply eqitree_Tau; cbn. rewrite bind_bind.
      reflexivity. }

    cbn.
    iDestruct "SI" as (???) "(Hhs & Hht & Hgv & Hi & %WF & Hlo & Hbij)".
    iDestruct "Hbij" as "(%Hsub&#Hgs_t&#Hgs_s&#Hrel)".

    iDestruct (globals_agree with "Hgs_t Hg") as %Ht; subst.
    iDestruct (globals_agree with "Hgs_s Hg0") as %Ht; subst.

    rewrite !insert_id; eauto.
    iApply sim_coindF_tau.
    iApply sim_coindF_base.
    rewrite /lift_expr_rel.
    iExists (g , p, (p0, f0)), tt,
      (g0, p1, (p2, f1)), tt; iFrame.
    do 2 (iSplitL ""; [ iPureIntro; rewrite <- itree_eta; reflexivity | ]).
    rewrite /state_interp. cbn.
    iFrame.
      iSplitL "Hhs Hht Hgv Hi".
    { iExists C, S, G. repeat iExists _. iFrame. destruct p; iFrame.
      repeat (iSplitL ""; first done). done. }
    iExists tt, tt; eauto.
  Qed.

End globalbij.
