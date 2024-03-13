(* From Coq Require Import String List Program.Equality. *)
From iris.prelude Require Import options.
From iris.base_logic.lib Require Export iprop.

(* From ITree Require Import ITree Eq Interp.InterpFacts Interp.RecursionFacts. *)

(* From Vellvm Require Import Syntax.LLVMAst Syntax.DynamicTypes *)
(*   Semantics.InterpretationStack Handlers Utils.Util Semantics.LLVMEvents. *)

From Equations Require Import Equations.

From Paco Require Import paco.

From simuliris.logic Require Import satisfiable.
From simuliris.simulation Require Import slsls simulation sim_properties contextual.

From simuliris.simulation Require Import wellformedness slsls simulation sim_properties contextual.
(*   vir spec globalbij heapbij logical_relations fundamental interp_properties. *)
(* From simuliris.utils Require Import no_event. *)

Set Default Proof Using "Type*".

Section Adequacy.

  Context {Σ : gFunctors}.
  Context `{sat: iPropI Σ → Prop} {Sat: Satisfiable sat}.

  Arguments sat _%I.

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

  Theorem adequacy:
    forall σ_t σ_s ie_t ie_s,
      well_formed (R := uvalue) (⟦ ie_t ⟧ σ_t) (⟦ie_s⟧ σ_s) ->
      sat (|==>
      ∃ `{sheapGS Σ} `{heapbijGS Σ} `{checkedoutGS Σ},
          state_interp σ_t σ_s ∗ ie_t ⪯ ie_s
               [[ lift_post (fun x y => ⌜obs_val x y ⌝) ]]) ->
      eutt obs_val_res (⟦ie_t⟧ σ_t) (⟦ie_s⟧ σ_s).
  Proof.
    intros * H_wf Hsim.

    assert (sat (|==>
      ∃ `{sheapGS Σ} `{heapbijGS Σ} `{checkedoutGS Σ},
                   sim_coindF
                   (lift_expr_rel (lift_post (fun x y => ⌜obs_val x y ⌝)))
                   (observe (⟦ vir_handler ⟨ ie_t ⟩ ⟧ σ_t))
                   (observe (⟦ vir_handler ⟨ ie_s ⟩ ⟧ σ_s)))).
    { eapply sat_mono; [ |apply Hsim].
      iIntros "H"; iMod "H".
      iDestruct "H" as (Hb Hh Hc) "[SI Hsim]".
      iSpecialize ("Hsim" with "SI"). iMod "Hsim".
      iModIntro. iExists Hb, Hh, Hc.
      iApply sim_coindF_bupd_mono; [ | iApply "Hsim"].
      iIntros (??); rewrite /lift_rel /lift_expr_rel.
       iIntros "H".
       iDestruct "H" as (????) "(SI&H)"; iDestruct "H" as (??) "H".
       rewrite /logrel_post /lift_post.
       iDestruct "H" as (????) "H".
       iModIntro; rewrite H H0.
       setoid_rewrite <- itree_eta.
       setoid_rewrite H1; setoid_rewrite H2.
       setoid_rewrite StateFacts.interp_state_ret.
       repeat iExists _; repeat (iSplitL ""; [ done | ]); iFrame.
       repeat iExists _; repeat (iSplitL ""; [ done | ]); iFrame.
    }

    sat_crunch.

    remember (⟦ie_t⟧ σ_t) as e_t.
    remember (⟦ie_s⟧ σ_s) as e_s.

    clear Heqe_t Heqe_s H0 H1 σ_t σ_s ie_t ie_s.

    (* Initialize coinductive hypothesis *)
    revert e_t e_s H_wf H.
    pcofix CIH. intros.
    pstep.
    eapply sat_mono in H0.
    2 : {
      iApply sim_coindF_bupd_mono.
      iIntros (??). iApply lift_expr_rel_mono.
      iIntros (??). Unshelve.
      2 : exact (lift_post (λ x7 y : uvalue, ⌜obs_val x7 y⌝))%I.
      done. }

    pose proof @adequacy_sat_sim_indF as Hind.
    rewrite sim_coindF_unfold in H0.
    specialize (Hind (iPropI Σ) _ _ _ vir_lang vir_handler sat _ _).
    specialize (Hind _ _ _ _ H_wf H0).

    sat_crunch; cycle 1.
    unfold upaco2.
    eapply eqit__mono; [ eauto with paco | | ].
    { eapply H. }
    { intros.
      right. eapply CIH;
        destruct PR as (?&?&?&?&?&?); auto.
      rewrite <- H4, <- H5.
      eapply (sat_forall _ x10) in H1.
      eapply (sat_forall _ x11) in H1.
      eapply (sat_wand (⌜JMeq.JMeq x10 x11⌝%I)) in H1.
      2 : by iPureIntro.
      sat_crunch.
      eapply sat_mono.
      { iApply sim_coindF_bupd_mono.
        iIntros (??). iApply lift_expr_rel_mono.
        iIntros (??). Unshelve.

        2 : exact (lift_post (λ x7 y : uvalue, ⌜obs_val x7 y⌝))%I. done. }
      eauto. }
  Qed.

End Adequacy.
