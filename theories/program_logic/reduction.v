(* Asymmetric reductions on simulation *)

(* Given a full simulation, [source_red] and [source_target] allows to focus the
  reasoning on the source and target expression. *)

From iris.prelude Require Import options.
From iris.bi Require Import bi lib.fixpoint.

From velliris.program_logic Require Export weakest_pre.
From velliris.utils Require Import tactics.

From ITree Require Import ITree
     Eq.Eqit Events.State Events.StateFacts Extra.IForest.

From Paco Require Import paco.

Section reduction.

  Context {PROP : bi} `{!BiBUpd PROP, !BiAffine PROP, !BiPureForall PROP}.
  Context {Λ : language} {η : handlers Λ}.
  Context {si : simulirisGS PROP Λ}.
  Set Default Proof Using "Type*".

  Notation expr_rel' R1 R2 := (@exprO' Λ R1 -d> @exprO' Λ R2 -d> PROP).
  Notation st_expr_rel' R1 R2 := (@st_exprO' Λ R1 -d> @st_exprO' Λ R2 -d> PROP).
  Notation expr_rel R1 R2 := (@exprO Λ R1 -d> @exprO Λ R2 -d> PROP).
  Notation st_expr_rel R1 R2 := (@st_exprO Λ R1 -d> @st_exprO Λ R2 -d> PROP).

  Local Instance sim_expr_stutter : SimE PROP Λ := (sim_expr_aux (η := η)).(unseal).

  Global Instance sim_coindF_ne {R1 R2} : NonExpansive (sim_coindF (R1 := R1) (R2 := R2)).
  Proof. solve_proper. Qed.

  (* source reduction up to interpreted result. *)
  Definition source_red_rec {R} (Ψ : expr Λ R -> PROP) (rec : expr Λ R -> PROP) (e_s : expr Λ R) :=
    ((∀ σ_t σ_s, state_interp σ_t σ_s ==∗
        (∃ (X : Type) (v_s : X) (k_s : X -> itree (L0 Λ) _) (σ_s' : state Λ),
            ⌜⟦η⟨e_s⟩⟧ σ_s ≅ ITree.bind (Tau (Ret (σ_s', v_s))) (fun x => ⟦η⟨k_s x.2⟩⟧ x.1)⌝
             ∗ state_interp σ_t σ_s' ∗ rec (k_s v_s)))
     ∨ Ψ e_s)%I.

  Definition source_red_rec_mono {R} (Ψ : expr Λ R -> PROP) l1 l2 :
    □ (∀ e, l1 e -∗ l2 e) -∗ ∀ e, source_red_rec Ψ l1 e -∗ source_red_rec Ψ l2 e.
  Proof.
    iIntros "Hmon" (e) "Hl1". rewrite /source_red_rec.
    iDestruct "Hl1" as "[Hl1 | Hl1]" ; last by iRight.
    iLeft. iIntros (σ_t σ_s) "SI".
    iMod ("Hl1" with "SI") as (X v_t k_t σ_t' Heq) "[SI Hl1]".
    iModIntro. iExists _,_,_,_; iFrame.
    iSplitL ""; first done.
    by iApply ("Hmon" with "Hl1").
  Qed.

  Instance source_red_mon {R} (Ψ : expr Λ R -> PROP) : BiMonoPred (source_red_rec Ψ).
  Proof.
    constructor.
    - iIntros (l1 l2 Hne Hne') "H". by iApply source_red_rec_mono.
    - intros l Hne n e1 e2 Heq. by apply (discrete_iff _ _) in Heq as ->.
  Qed.

  Definition source_red_def {R} (Ψ : expr Λ R -> PROP) :=
    bi_least_fixpoint (source_red_rec Ψ).
  Lemma source_red_def_unfold {R} (Ψ : expr Λ R -> PROP) e_s :
    source_red_def Ψ e_s ⊣⊢ source_red_rec Ψ (source_red_def Ψ) e_s.
  Proof. by rewrite /source_red_def least_fixpoint_unfold. Qed.

  Definition source_red_aux {R} : seal (λ (e : expr Λ R) Ψ, source_red_def Ψ e).
  Proof. by eexists. Qed.
  Definition source_red {R} := (@source_red_aux R).(unseal).
  Lemma source_red_eq {R} : source_red = (λ e Ψ, source_red_def (R := R) Ψ e).
  Proof. rewrite -source_red_aux.(seal_eq) //. Qed.

  Lemma source_red_strong_ind {R} Ψ (Ψi : expr Λ R → PROP) :
    Proper ((≡) ==> (≡)) Ψi →
    □ (∀ e : exprO R, source_red_rec Ψ (λ e', Ψi e' ∧ source_red_def Ψ e') e -∗ Ψi e) -∗
    ∀ e : exprO R, source_red_def Ψ e -∗ Ψi e.
  Proof.
    iIntros (Hproper) "H". rewrite /source_red_def.
    by iApply (@least_fixpoint_ind _ _ (source_red_rec Ψ) _ Ψi).
  Qed.

  Lemma source_red_ind {R} Ψ (Ψi : expr Λ R → PROP) :
    Proper ((≡) ==> (≡)) Ψi →
    □ (∀ e : exprO R, source_red_rec Ψ Ψi e -∗ Ψi e) -∗
    ∀ e : exprO R, source_red_def Ψ e -∗ Ψi e.
  Proof.
    iIntros (Hproper) "H". rewrite /source_red_def.
    by iApply (@least_fixpoint_iter _ _ (source_red_rec Ψ) Ψi).
  Qed.

  Lemma source_red_unfold {R} (e_s : expr Λ R) Ψ :
    source_red e_s Ψ ⊣⊢
      (∀ σ_t σ_s : state Λ,
        state_interp σ_t σ_s ==∗
        ∃ (X : Type) (v_s : X) (k_s : X → itree (L0 Λ) R) (σ_s' : state Λ),
          ⌜⟦ η ⟨ e_s ⟩ ⟧ σ_s ≅ ITree.bind (Tau (Ret (σ_s', v_s))) (λ x : state Λ * X, ⟦ η ⟨ k_s x.2 ⟩ ⟧ x.1)⌝ ∗
          state_interp σ_t σ_s' ∗ source_red (k_s v_s) Ψ) ∨ Ψ e_s.
  Proof. rewrite source_red_eq. rewrite {1}source_red_def_unfold /source_red_rec //. Qed.

  Lemma source_red_base {R} Ψ (e_s : _ R) :
    Ψ e_s -∗ source_red e_s Ψ.
  Proof.
    iIntros "HPsi". rewrite source_red_unfold. by iRight.
  Qed.

  Lemma source_red_sim_expr {R1 R2} (e_s : _ R1) (e_t : _ R2) Φ:
    source_red e_s (λ e_s', e_t ⪯ e_s' [{ Φ }]) -∗
               e_t ⪯ e_s [{ Φ }].
  Proof.
    iIntros "Hsource".
    rewrite source_red_eq.
    iApply (source_red_ind _ (λ e_s, e_t ⪯ e_s [{ Φ }])%I); last by rewrite /flip.
    iModIntro. clear e_s. iIntros (e_s) "Hsource".
    rewrite /source_red_rec.
    iDestruct "Hsource" as "[Hsource| Hsource]"; last done.
    rewrite {2}sim_expr_eq /sim_expr_.
    iIntros (??) "Hstate".
    iMod ("Hsource" with "Hstate") as (X v_t k_t σ_t' Heq) "[SI Htarget]".
    iModIntro.
    iApply sim_coindF_Proper;
      [eapply lift_expr_rel_Φ_Proper | reflexivity | rewrite Heq bind_tau bind_ret_l; reflexivity |].
    rewrite sim_coindF_unfold sim_indF_unfold /sim_expr_inner.
    cbn.
    rewrite {1}sim_expr_eq /sim_expr_.
    iMod ("Htarget" with "SI") as "Hsim".
    provide_case: STUTTER_R.
    by rewrite /sim_coind sim_coindF_unfold.
  Qed.

  Lemma source_red_bind {R1 R2} (e_s : _ R1) (k_s : _ -> _ R2) Ψ :
    source_red e_s (λ e_s', source_red (ITree.bind e_s' k_s) Ψ) -∗
    source_red (ITree.bind e_s k_s) Ψ.
  Proof.
    iIntros "He".
    iApply (source_red_ind _ (λ e_s, source_red (ITree.bind e_s k_s) Ψ)%I); last by rewrite source_red_eq /flip.
    iModIntro. clear e_s. iIntros (e_s) "IH". rewrite source_red_eq /flip source_red_def_unfold.
    iDestruct "IH" as "[IH | IH]"; last by rewrite source_red_def_unfold.
    iLeft.
    iIntros (??) "Hstate".
    iMod ("IH" with "Hstate") as (X v_s k_s' σ_s' Heq) "[SI Hsource]".
    iModIntro. iExists _,_,_,_.
    iSplitL "".
    { iPureIntro. rewrite /interp_L2.
      rewrite interp_state_bind. rewrite /interp_L2 in Heq. rewrite Heq.
      rewrite bind_bind. eapply eq_itree_clo_bind; first by reflexivity.
      intros; subst. symmetry.
      rewrite <- interp_state_bind. Unshelve.
      2 : { exact (fun x => ITree.bind (k_s' x) k_s). }
      reflexivity. }
    iFrame.
  Qed.

  Lemma source_red_tau {R} (Ψ : _ R -> PROP) e_s:
     source_red e_s Ψ -∗ source_red (Tau e_s) Ψ.
  Proof.
    iIntros "He".
    iApply (source_red_ind _ (λ e_s, source_red (Tau e_s) Ψ)%I); last by rewrite source_red_eq /flip.
    iModIntro. clear e_s. iIntros (e_s) "IH". rewrite source_red_eq /flip source_red_def_unfold.
    iDestruct "IH" as "[IH | IH]".
    { iLeft.
      iIntros (??) "Hstate".
      iMod ("IH" with "Hstate") as (X v_s k_s' σ_s' Heq) "[SI Hsource]".
      iExists X,v_s,(fun x => Tau (k_s' x)),σ_s'; iModIntro; iSplitL "".
      { unfold interp_L2; unfold interp_L2 in Heq.
        setoid_rewrite interp_state_tau. rewrite Heq.
        rewrite !bind_tau. iPureIntro.
        by rewrite !bind_ret_l. }
      iFrame. }
    { iLeft.
      iIntros (??) "Hstate".
      iExists unit, tt, (fun x => e_s),σ_s; iModIntro; iSplitL ""; iFrame.
      { unfold interp_L2.
        setoid_rewrite interp_state_tau.
        rewrite !bind_tau. iPureIntro.
        by rewrite !bind_ret_l. }
      rewrite /flip source_red_def_unfold.
      iFrame. }
  Qed.

  Lemma source_red_mono {R} (Φ Ψ : _ R -> PROP) :
    (∀ e_s, Φ e_s -∗ Ψ e_s) -∗
    ∀ e_s, source_red e_s Φ -∗ source_red e_s Ψ.
  Proof.
    iIntros "Hw" (e_s) "Hs".
    iApply (source_red_ind _ (λ e_s, (∀ e_s', Φ e_s' -∗ Ψ e_s') -∗ source_red e_s Ψ)%I with "[] [Hs] Hw"); last by rewrite source_red_eq /flip.
    iModIntro. clear e_s. iIntros (e_s) "IH Hw".
    rewrite source_red_unfold.
    iDestruct "IH" as "[IH | IH]"; last (iRight; iApply ("Hw" with "IH")).
    iLeft. iIntros (σ_t σ_s) "SI";
      iMod ("IH" with "SI") as (X v_s k_s σ_s' Heq) "[SI IH]"; iModIntro.
    iExists _,_,_,_; iFrame. iSplitL ""; [iPureIntro; eapply Heq|].
    rewrite source_red_eq.
    iApply ("IH" with "Hw").
  Qed.

  Lemma source_red_wand {R} (Φ Ψ : _ R -> PROP) e_t :
    source_red e_t Φ -∗ (∀ e_t', Φ e_t' -∗ Ψ e_t') -∗ source_red e_t Ψ.
  Proof. iIntros "Ht Hw". iApply (source_red_mono with "Hw Ht"). Qed.

  (* target reduction up to interpreted result. *)
  Definition target_red_rec {R} (Ψ : expr Λ R -> PROP) (rec : expr Λ R -> PROP) (e_t : expr Λ R) :=
    ((∀ σ_t σ_s, state_interp σ_t σ_s ==∗
        (∃ (X : Type) (v_t : X) (k_t : X -> itree (L0 Λ) _) (σ_t' : state Λ),
            ⌜⟦η⟨e_t⟩⟧ σ_t ≅ ITree.bind (Tau (Ret (σ_t', v_t))) (fun x => ⟦η⟨k_t x.2⟩⟧ x.1)⌝
             ∗ state_interp σ_t' σ_s ∗ rec (k_t v_t)))
     ∨ Ψ e_t)%I.

  Definition target_red_rec_mono {R} (Ψ : expr Λ R -> PROP) l1 l2 :
    □ (∀ e, l1 e -∗ l2 e) -∗ ∀ e, target_red_rec Ψ l1 e -∗ target_red_rec Ψ l2 e.
  Proof.
    iIntros "Hmon" (e) "Hl1". rewrite /target_red_rec.
    iDestruct "Hl1" as "[Hl1 | Hl1]" ; last by iRight.
    iLeft. iIntros (σ_t σ_s) "SI".
    iMod ("Hl1" with "SI") as (X v_t k_t σ_t' Heq) "[SI Hl1]".
    iModIntro. iExists _,_,_,_; iFrame.
    iSplitL ""; first done.
    by iApply ("Hmon" with "Hl1").
  Qed.

  Instance target_red_mon {R} (Ψ : expr Λ R -> PROP) : BiMonoPred (target_red_rec Ψ).
  Proof.
    constructor.
    - iIntros (l1 l2 Hne Hne') "H". by iApply target_red_rec_mono.
    - intros l Hne n e1 e2 Heq. by apply (discrete_iff _ _) in Heq as ->.
  Qed.

  Definition target_red_def {R} (Ψ : expr Λ R -> PROP) :=
    bi_least_fixpoint (target_red_rec Ψ).
  Lemma target_red_def_unfold {R} (Ψ : expr Λ R -> PROP) e_s :
    target_red_def Ψ e_s ⊣⊢ target_red_rec Ψ (target_red_def Ψ) e_s.
  Proof. by rewrite /target_red_def least_fixpoint_unfold. Qed.

  Definition target_red_aux {R} : seal (λ (e : expr Λ R) Ψ, target_red_def Ψ e).
  Proof. by eexists. Qed.
  Definition target_red {R} := (@target_red_aux R).(unseal).
  Lemma target_red_eq {R} : target_red = (λ e Ψ, target_red_def (R := R) Ψ e).
  Proof. rewrite -target_red_aux.(seal_eq) //. Qed.

  Lemma target_red_strong_ind {R} Ψ (Ψi : expr Λ R → PROP) :
    Proper ((≡) ==> (≡)) Ψi →
    □ (∀ e : exprO R, target_red_rec Ψ (λ e', Ψi e' ∧ target_red_def Ψ e') e -∗ Ψi e) -∗
    ∀ e : exprO R, target_red_def Ψ e -∗ Ψi e.
  Proof.
    iIntros (Hproper) "H". rewrite /target_red_def.
    by iApply (@least_fixpoint_ind _ _ (target_red_rec Ψ) _ Ψi).
  Qed.

  Lemma target_red_ind {R} Ψ (Ψi : expr Λ R → PROP) :
    Proper ((≡) ==> (≡)) Ψi →
    □ (∀ e : exprO R, target_red_rec Ψ Ψi e -∗ Ψi e) -∗
    ∀ e : exprO R, target_red_def Ψ e -∗ Ψi e.
  Proof.
    iIntros (Hproper) "H". rewrite /target_red_def.
    by iApply (@least_fixpoint_iter _ _ (target_red_rec Ψ) Ψi).
  Qed.

  Lemma target_red_unfold {R} (e_t : expr Λ R) Ψ :
    target_red e_t Ψ ⊣⊢
      (∀ σ_t σ_s : state Λ,
        state_interp σ_t σ_s ==∗
        ∃ (X : Type) (v_t : X) (k_t : X → itree (L0 Λ) R) (σ_t' : state Λ),
          ⌜⟦ η ⟨ e_t ⟩ ⟧ σ_t ≅ ITree.bind (Tau (Ret (σ_t', v_t))) (λ x : state Λ * X, ⟦ η ⟨ k_t x.2 ⟩ ⟧ x.1)⌝ ∗
          state_interp σ_t' σ_s ∗ target_red (k_t v_t) Ψ) ∨ Ψ e_t.
  Proof. rewrite target_red_eq. rewrite {1}target_red_def_unfold /target_red_rec //. Qed.

  Lemma target_red_base {R} Ψ (e_t : _ R) :
    Ψ e_t -∗ target_red e_t Ψ.
  Proof.
    iIntros "HPsi". rewrite target_red_unfold. by iRight.
  Qed.

  Lemma target_red_sim_expr {R1 R2} (e_s : _ R1) (e_t : _ R2) Φ:
    target_red e_t (λ e_t', e_t' ⪯ e_s [{ Φ }]) -∗
               e_t ⪯ e_s [{ Φ }].
  Proof.
    iIntros "Hsource".
    rewrite target_red_eq.
    iApply (target_red_ind _ (λ e_t, e_t ⪯ e_s [{ Φ }])%I); last by rewrite /flip.
    iModIntro. clear e_t. iIntros (e_t) "Htarget".
    rewrite /target_red_rec.
    iDestruct "Htarget" as "[Htarget | Htarget]"; last done.
    rewrite {2}sim_expr_eq /sim_expr_.
    iIntros (??) "Hstate".
    iMod ("Htarget" with "Hstate") as (X v_t k_t σ_t' Heq) "[SI Htarget]".
    iModIntro.
    iApply sim_coindF_Proper;
      [eapply lift_expr_rel_Φ_Proper | rewrite Heq bind_tau bind_ret_l; reflexivity | reflexivity |].
    rewrite sim_coindF_unfold sim_indF_unfold /sim_expr_inner
      {1}sim_expr_eq /sim_expr_.
    iMod ("Htarget" with "SI") as "Hsim".
    provide_case: STUTTER_L.
    by rewrite /sim_coind sim_coindF_unfold.
  Qed.

  Lemma target_red_bind {R1 R2} (e_t : _ R1) (k_t : _ -> _ R2) Ψ :
    target_red e_t (λ e_t', target_red (ITree.bind e_t' k_t) Ψ) -∗
    target_red (ITree.bind e_t k_t) Ψ.
  Proof.
    iIntros "He".
    iApply (target_red_ind _ (λ e_t, target_red (ITree.bind e_t k_t) Ψ)%I); last by rewrite target_red_eq /flip.
    iModIntro. clear e_t. iIntros (e_t) "IH". rewrite target_red_eq /flip target_red_def_unfold.
    iDestruct "IH" as "[IH | IH]"; last by rewrite target_red_def_unfold.
    iLeft.
    iIntros (??) "Hstate".
    iMod ("IH" with "Hstate") as (X v_t k_t' σ_t' Heq) "[SI Htarget]".
    iModIntro. iExists _,_,_,_.
    iSplitL "".
    { iPureIntro. rewrite /interp_L2.
      rewrite interp_state_bind. rewrite /interp_L2 in Heq. rewrite Heq.
      rewrite bind_bind. eapply eq_itree_clo_bind; first by reflexivity.
      intros; subst. symmetry.
      rewrite <- interp_state_bind. Unshelve.
      2 : { exact (fun x => ITree.bind (k_t' x) k_t). }
      reflexivity. }
    iFrame.
  Qed.

  Lemma target_red_tau {R} (Ψ : _ R -> PROP) e_t:
     target_red e_t Ψ -∗ target_red (Tau e_t) Ψ.
  Proof.
    iIntros "He".
    iApply (target_red_ind _ (λ e_t, target_red (Tau e_t) Ψ)%I); last by rewrite target_red_eq /flip.
    iModIntro. clear e_t. iIntros (e_t ) "IH". rewrite target_red_eq /flip target_red_def_unfold.
    iDestruct "IH" as "[IH | IH]".
    { iLeft.
      iIntros (??) "Hstate".
      iMod ("IH" with "Hstate") as (X v_t k_t' σ_t' Heq) "[SI Htarget]".
      iExists X,v_t,(fun x => Tau (k_t' x)),σ_t'; iModIntro; iSplitL "".
      { unfold interp_L2; unfold interp_L2 in Heq.
        setoid_rewrite interp_state_tau. rewrite Heq.
        rewrite !bind_tau. iPureIntro.
        by rewrite !bind_ret_l. }
      iFrame. }
    { iLeft.
      iIntros (??) "Hstate".
      iExists unit, tt, (fun x => e_t),σ_t; iModIntro; iSplitL ""; iFrame.
      { unfold interp_L2.
        setoid_rewrite interp_state_tau.
        rewrite !bind_tau. iPureIntro.
        by rewrite !bind_ret_l. }
      rewrite /flip target_red_def_unfold.
      iFrame. }
  Qed.

  Lemma target_red_mono {R} (Φ Ψ : _ R -> PROP) :
    (∀ e_t, Φ e_t -∗ Ψ e_t) -∗
    ∀ e_t, target_red e_t Φ -∗ target_red e_t Ψ.
  Proof.
    iIntros "Hw" (e_t) "Ht".
    iApply (target_red_ind _ (λ e_t, (∀ e_t', Φ e_t' -∗ Ψ e_t') -∗ target_red e_t Ψ)%I with "[] [Ht] Hw"); last by rewrite target_red_eq /flip.
    iModIntro. clear e_t. iIntros (e_t) "IH Hw".
    rewrite target_red_unfold.
    iDestruct "IH" as "[IH | IH]"; last (iRight; iApply ("Hw" with "IH")).
    iLeft. iIntros (σ_t σ_s) "SI";
      iMod ("IH" with "SI") as (X v_t k_t σ_t' Heq) "[SI IH]"; iModIntro.
    iExists _,_,_,_; iFrame. iSplitL ""; [iPureIntro; eapply Heq|].
    rewrite target_red_eq.
    iApply ("IH" with "Hw").
  Qed.

  Lemma target_red_wand {R} (Φ Ψ : _ R -> PROP) e_t :
    target_red e_t Φ -∗ (∀ e_t', Φ e_t' -∗ Ψ e_t') -∗ target_red e_t Ψ.
  Proof. iIntros "Ht Hw". iApply (target_red_mono with "Hw Ht"). Qed.

  Lemma target_red_Proper_entails {R} (Φ : _ R -> PROP) :
    Proper (eq_itree eq ==> bi_entails) Φ ->
    Proper (eq_itree eq ==> bi_entails) (fun e_t => target_red e_t Φ).
  Proof.
    repeat intro.
    iIntros "H". rewrite !target_red_unfold.
    iDestruct "H" as "[H | H]".
    { iLeft.
      iIntros (??) "SI". iSpecialize ("H" with "SI"). iMod "H".
      iDestruct "H" as (?????) "(SI & H)".
      iModIntro.
      iExists X, v_t, k_t, σ_t'.
      rewrite -H0. iSplitL ""; [ done |]. iFrame. }
    { iRight. by iApply H. }
  Qed.

  Lemma target_red_Proper {R} (Φ : _ R -> PROP) :
    Proper (eq_itree eq ==> equiv) Φ ->
    Proper (eq_itree eq ==> equiv) (fun e_t => target_red e_t Φ).
  Proof.
    repeat intro.
    iSplit; iIntros "H";
      iApply (target_red_Proper_entails with "H").
    2 : auto. 3 : symmetry; eauto.
    all : repeat intro; iIntros "H"; iApply H; eauto.
    all : symmetry; auto.
  Qed.

  Definition lift_unary_post {R} (Φ : R -> PROP) (e : expr Λ R) : PROP :=
    ∃ v, ⌜e ≅ Ret v⌝ ∗ Φ v.

  Lemma target_red_lift_Proper {R} (Φ : R -> PROP) :
    Proper (eq_itree eq ==> bi_entails) (fun e_t => target_red e_t (lift_unary_post Φ)).
  Proof.
    repeat intro.
    iIntros "H". rewrite !target_red_unfold.
    iDestruct "H" as "[H | H]".
    { iLeft.
      iIntros (??) "SI". iSpecialize ("H" with "SI"). iMod "H".
      iDestruct "H" as (?????) "(SI & H)".
      iModIntro.
      iExists X, v_t, k_t, σ_t'.
      rewrite -H. iSplitL ""; [ done |]. iFrame. }
    { iRight. rewrite /lift_unary_post.
      iDestruct "H" as (??) "H". iExists v; rewrite -H.
      by iFrame. }
  Qed.

  #[global] Instance target_red_Proper1 {R1 R2} (Φ : _ R1 -> _ R2 -> PROP) e_s :
    Proper (eq_itree eq ==> equiv) (fun e_t => target_red e_t (λ e_t', (e_t' ⪯ e_s [{ Φ }])%I)).
  Proof.
    eapply target_red_Proper.
    repeat intro. rewrite H; done.
  Qed.

  Lemma source_red_Proper_entails {R} (Φ : _ R -> PROP) :
    Proper (eq_itree eq ==> bi_entails) Φ ->
    Proper (eq_itree eq ==> bi_entails) (fun e_s => source_red e_s Φ).
  Proof.
    repeat intro.
    iIntros "H". rewrite !source_red_unfold.
    iDestruct "H" as "[H | H]".
    { iLeft.
      iIntros (??) "SI". iSpecialize ("H" with "SI"). iMod "H".
      iDestruct "H" as (?????) "(SI & H)".
      iModIntro.
      iExists X, v_s, k_s, σ_s'.
      rewrite -H0. iSplitL ""; [ done |]. iFrame. }
    { iRight. by iApply H. }
  Qed.

  Lemma source_red_Proper {R} (Φ : _ R -> PROP) :
    Proper (eq_itree eq ==> equiv) Φ ->
    Proper (eq_itree eq ==> equiv) (fun e_s => source_red e_s Φ).
  Proof.
    repeat intro.
    iSplit; iIntros "H";
      iApply (source_red_Proper_entails with "H").
    2 : auto. 3 : symmetry; eauto.
    all : repeat intro; iIntros "H"; iApply H; eauto.
    all : symmetry; auto.
  Qed.

  Lemma source_red_lift_Proper {R} (Φ : R -> PROP) :
    Proper (eq_itree eq ==> bi_entails) (fun e_s => source_red e_s (lift_unary_post Φ)).
  Proof.
    repeat intro.
    iIntros "H". rewrite !source_red_unfold.
    iDestruct "H" as "[H | H]".
    { iLeft.
      iIntros (??) "SI". iSpecialize ("H" with "SI"). iMod "H".
      iDestruct "H" as (?????) "(SI & H)".
      iModIntro.
      iExists X, v_s, k_s, σ_s'.
      rewrite -H. iSplitL ""; [ done |]. iFrame. }
    { iRight. rewrite /lift_unary_post.
      iDestruct "H" as (??) "H". iExists v; rewrite -H.
      by iFrame. }
  Qed.

  #[global] Instance source_red_Proper1 {R1 R2} (Φ : _ R1 -> _ R2 -> PROP) e_t :
    Proper (eq_itree eq ==> equiv) (fun e_s => source_red e_s (λ e_s', (e_t ⪯ e_s' [{ Φ }])%I)).
  Proof.
    eapply source_red_Proper.
    repeat intro. rewrite H; done.
  Qed.

  #[global] Instance source_red_eq_itree {R} Φ :
    Proper (eq_itree eq ==> equiv) (fun e => source_red (R := R) e Φ).
  Proof.
    repeat intro.
    apply EqAxiom.bisimulation_is_eq in H. subst.
    iSplitL ""; iIntros "H"; done.
  Qed.

  #[global] Instance target_red_eq_itree {R} Φ :
    Proper (eq_itree eq ==> equiv) (fun e => target_red (R := R) e Φ).
  Proof.
    repeat intro.
    apply EqAxiom.bisimulation_is_eq in H. subst.
    iSplitL ""; iIntros "H"; done.
  Qed.


End reduction.
