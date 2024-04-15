From iris.prelude Require Import options.

From Coq Require Import Program.Equality.

From velliris.program_logic Require Import program_logic.
From velliris.vir Require Import
  vir val_rel heapbij adequacy spec globalbij logical_relations fundamental
  interp_properties.

From Vellvm Require Import Syntax.DynamicTypes Handlers Syntax.LLVMAst
  Semantics.InterpretationStack.

From Equations Require Import Equations.

From ITree Require Import
  ITree Recursion Eq.Eqit Events.StateFacts Interp.InterpFacts.
From Equations Require Import Equations.

Set Default Proof Using "Type*".

Import StateFacts.
Import ListNotations.
Import SemNotations.
Import LLVMEvents.


(** *Top-level Contextual Refinement *)
Section CR.

  Context {Σ} `{!vellirisGS Σ}.

  Definition globals_WF (g : global_env) : iPropI Σ :=
    ([∗ map] g0↦v ∈ g, ∃ v' : dvalue, ⌜g !! g0 = Some v'⌝ ∗ dval_rel v' v)%I.

  Definition mcfg_fn_disjoint_keys (C : CFG.mcfg dtyp) e :=
     forall c, Leaf.Leaf c (mcfg_definitions C) -> disjoint_keys c e.

  Definition lift_eutt_post {E} {R1 R2}
    (Φ: R1 → R2 → iProp Σ) :=
    (λ (e_t : itree E R1) (e_s : itree E R2), ∃ v_t v_s, ⌜e_t ≈ Ret v_t⌝ ∗ ⌜e_s ≈ Ret v_s⌝ ∗ Φ v_t v_s)%I.

  (* Relating results on the hole. *)
  Definition logrel_eutt_post : expr vir_lang uvalue → expr vir_lang uvalue → iPropI Σ :=
    lift_eutt_post uval_rel.

  #[global] Instance Proper_eutt_lift_eutt_post {E R1 R2} (Φ: R1 → R2 → iProp Σ) :
    Proper (eutt eq ==> eutt (E := E) eq ==> equiv) (lift_eutt_post Φ).
  Proof.
    repeat intro; iSplit; iIntros "H";
      rewrite /lift_eutt_post; iDestruct "H" as (????) "H";
      repeat iExists _; repeat iSplitL ""; try iPureIntro; auto.
    all : try rewrite -H1;try rewrite -H2; auto; symmetry; auto.
  Qed.

  Notation st_expr_rel' R1 R2 :=
    (@st_exprO' vir_lang R1 -d> @st_exprO' vir_lang R2 -d> iPropI Σ).

  (* An obligation for each of the defined calls; it satisfies the external
      call specifications *)
  Definition context_rel_call_inv
      (f : ∀ T : Type, CallE T → L0'expr T)
      (g : ∀ T : Type, CallE T → L0'expr T) :=
    (□ (∀ fn1 fn2 dt1 dt2 attr1 attr2 args1 args2 C,
          let call1 := ExternalCall dt1 fn1 args1 attr1 in
          let call2 := ExternalCall dt2 fn2 args2 attr2 in
          call_ev call1 call2 C -∗
          ⟅ f _ (Call dt1 fn1 args1 attr1) ⟆ ⪯
          ⟅ g _ (Call dt2 fn2 args2 attr2) ⟆
          [[ (fun v1 v2 => call_ans call1 v1 call2 v2 C) ⤉ ]]) )%I.

  (* Should follow by reflexivity theorem *)
  Definition context_rel_refl
      (f : ∀ T : Type, CallE T → L0'expr T)
      (g : ∀ T : Type, CallE T → L0'expr T) :=
    (□ (∀ fn1 fn2 dt attr args1 args2 C,
          arg_val_rel (fn1, args1) (fn2, args2) C -∗
          ⟅ f _ (Call dt fn1 args1 attr) ⟆ ⪯
          ⟅ g _ (Call dt fn2 args2 attr) ⟆
          [[ (fun x y => res_val_rel x y C) ⤉ ]]))%I.

  Definition context_call
      (f : ∀ T : Type, CallE T → L0'expr T) :=
    (forall τ addr args attrs,
      f uvalue (Call τ addr args (FNATTR_Internal :: attrs)) =
      f uvalue (Call τ addr args attrs)) /\
    (forall τ addr args attrs,
      f uvalue (Call τ addr args (FNATTR_External:: attrs)) =
      f uvalue (Call τ addr args attrs)).

  Definition context_rel
      (f : ∀ T : Type, CallE T → L0'expr T)
      (g : ∀ T : Type, CallE T → L0'expr T) :=
    (⌜context_call f⌝ ∗ ⌜context_call g⌝ ∗
       context_rel_call_inv f g ∗ context_rel_refl f g)%I.

  (* Auxiliary definitions for [Proper_interp_mrec] *)
  (* Because [sim_expr] includes stateful interpretation, showing properness result
    for [interp_mrec] amounts to proving a simulation *)
  Local Definition interp_mrec_pred {R1 R2} :=
    fun (Φ:st_expr_rel' R1 R2) (e_t:st_expr' vir_lang R1) (e_s:st_expr' vir_lang R2) =>
      (∃ f a1 σ_t g a2 σ_s,
          ⌜e_t = observe (⟦ interp_mrec f a1 ⟧ σ_t)⌝ ∗
          ⌜e_s = observe (⟦ interp_mrec g a2 ⟧ σ_s)⌝ ∗
         □ (∀ x y, (base x y ∗ Φ x y) ∗-∗ Φ x y) ∗
         context_rel f g ∗
         sim_coindF Φ (observe (⟦ ⟅ a1 ⟆ ⟧ σ_t)) (observe (⟦ ⟅ a2 ⟆ ⟧ σ_s)))%I.

  Local Definition interp_mrec_rec {R1 R2} :=
    fun (Φ:st_expr_rel' R1 R2) (e_t:st_expr' vir_lang R1) (e_s:st_expr' vir_lang R2) =>
      ((∃ f a1 σ_t g a2 σ_s,
          ⌜e_t = observe (⟦ interp_mrec f a1 ⟧ σ_t)⌝ ∗
          ⌜e_s = observe (⟦ interp_mrec g a2 ⟧ σ_s)⌝ ∗
         □ (∀ x y, (base x y ∗ Φ x y) ∗-∗ Φ x y) ∗
         context_rel f g ∗
          sim_coindF Φ (observe (⟦ ⟅ a1 ⟆ ⟧ σ_t)) (observe (⟦ ⟅ a2 ⟆ ⟧ σ_s)))
        ∨ sim_coindF Φ e_t e_s)%I.

  Local Instance interp_mrec_pred_ne {R1 R2}:
    NonExpansive (interp_mrec_pred: st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2).
  Proof.
    intros x y * H. solve_proper_prepare. do 18 f_equiv; try solve_proper.
  Qed.

  Local Instance interp_mrec_rec_ne {R1 R2}:
    NonExpansive (interp_mrec_rec: st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2).
  Proof.
    intros x y * H. solve_proper_prepare. repeat f_equiv; try solve_proper.
  Qed.

  Local Definition interp_mrec_ind {T} :=
    (λ Φ e_t e_s,
      ∀ (f g : ∀ T : Type, LLVMEvents.CallE T → L0'expr T)
        (a1 a2 : itree (CallE +' language.L0 vir_lang) T) σ_t σ_s,
      □ (∀ x y, (base x y ∗ Φ x y) ∗-∗ Φ x y) -∗
      ⌜e_t = observe (⟦ ⟅ a1 ⟆ ⟧ σ_t) ⌝ -∗
      ⌜e_s = observe (⟦ ⟅ a2 ⟆ ⟧ σ_s) ⌝ -∗
      context_rel f g -∗
      sim_indF interp_mrec_rec Φ
          (observe (⟦ interp_mrec f a1 ⟧ σ_t))
          (observe (⟦ interp_mrec g a2 ⟧ σ_s)))%I.

  Local Instance interp_mrec_ind_ne {T}:
    NonExpansive (interp_mrec_ind: st_expr_rel' _ _ -d> st_expr_rel' _ T).
  Proof.
    solve_proper_prepare. clear -H. repeat f_equiv. done.
  Qed.

  Lemma interp_mrec_F_ind_case {T}
    (f g : ∀ T : Type, LLVMEvents.CallE T → L0'expr T) Ψ
    t X (e : _ X) k σ_s σ_t (a1 a2 : _ T):
    a1 ≅ vis e k ->
    t ≅ vis (e : language.F _ _) (λ x, Tau (Tau (⟦ ⟅ k x ⟆ ⟧ σ_t))) ->
    □ (∀ x y, (base x y ∗ Ψ x y) ∗-∗ Ψ x y) -∗
    context_rel f g -∗
    interp_mrec_ind Ψ (observe t) (observe (⟦ ⟅ a2 ⟆ ⟧ σ_s))
              ∧ sim_indF sim_coindF Ψ (observe t) (observe (⟦ ⟅ a2 ⟆ ⟧ σ_s)) -∗
    sim_expr_inner interp_mrec_rec (sim_indF interp_mrec_rec) Ψ
      (observe (⟦ interp_mrec f a1 ⟧ σ_t))
      (observe (⟦ interp_mrec g a2 ⟧ σ_s)).
  Proof.
    intros Ha Ht.
    to_eq in Ht; rewrite Ht; clear Ht.
    to_eq in Ha; rewrite Ha; clear Ha.

    iIntros "#HΨ Hfg Hinner".
    iDestruct "Hinner" as "(_ & Hinner)".
    rewrite -sim_coindF_unfold. rewrite /sim_expr_inner.
    iPoseProof (sim_coindF_F_inv_L with "HΨ Hinner") as ">Hinner".

    change
      (|==>
        ∃ c : sim_case,
          match c with
          | BASE => _
          | STUTTER_L => stutter_l
          | STUTTER_R => stutter_r
          | TAU_STEP => tau_step
          | VIS_STEP => _
          | SOURCE_UB => source_ub
          | SOURCE_EXC => source_exc
          end)%I with
          (sim_expr_inner interp_mrec_rec (sim_indF interp_mrec_rec) Ψ
            (observe (⟦ interp_mrec f (vis e k) ⟧ σ_t))
            (observe (⟦ interp_mrec g a2 ⟧ σ_s))).

    iDestruct "Hinner" as "[ Hinner | [ Hinner | Hinner ] ]".
    { iDestruct "Hinner" as (???) "Hinner".
      rewrite -itree_eta in H.
      apply interp_L2_conv_F_tau_n_inv with (g := g) in H.
      destruct H as (?&?&?&?&?).
      to_eq in H0; rewrite H0 -sim_indF_unfold.
      rewrite interp_mrec_vis.
      iApply sim_indF_n_taus_R.
      rewrite sim_indF_unfold; provide_case: STUTTER_L.
      cbn. rewrite sim_indF_unfold; provide_case: VIS_STEP.
      rewrite /handle_event; cbn; rewrite /handle_E.
      iSplitL ""; first (iPureIntro; by exists eq_refl).
      iIntros. dependent destruction H1; cbn.
      change (TauF ?x) with (observe (Tau x)).
      rewrite -!interp_mrec_tau.
      iLeft; iModIntro.
      iExists f, _, _, g, _, _; iFrame.
      repeat (iSplitL ""; first done).
      rewrite !interp_L2_conv_tau.
      specialize (H v_s); to_eq in H; rewrite -H.
      by do 2 iApply sim_coindF_tauL. }

    { iDestruct "Hinner" as (?????) "Hinner".
      rewrite -itree_eta in H.
      eapply interp_L2_conv_UB_tau_n_inv with (g := g) in H.
      destruct H as (?&?).
      to_eq in H; rewrite H.
      rewrite -sim_indF_unfold; iApply sim_indF_n_taus_R.
      rewrite sim_indF_unfold; by provide_case: SOURCE_UB. }

    { iDestruct "Hinner" as (?????) "Hinner".
      rewrite -itree_eta in H.
      eapply interp_L2_conv_failure_tau_n_inv with (g := g) in H.
      destruct H as (?&?&?).
      to_eq in H; rewrite H.
      rewrite -sim_indF_unfold; iApply sim_indF_n_taus_R.
      rewrite sim_indF_unfold; by provide_case: SOURCE_EXC.
      Unshelve. all : eauto. }
  Qed.

  Lemma interp_mrec_F_ind_case' {T}
    (f g : ∀ T : Type, LLVMEvents.CallE T → L0'expr T) Ψ
    t X (e : _ X) k σ_s σ_t (a1 a2 : _ T):
    a2 ≅ vis e k ->
    t ≅ vis (e : language.F _ _) (λ x, Tau (Tau (⟦ ⟅ k x ⟆ ⟧ σ_s))) ->
    □ (∀ x y, (base x y ∗ Ψ x y) ∗-∗ Ψ x y) -∗
    context_rel f g -∗
    interp_mrec_ind Ψ (observe (⟦ ⟅ a1 ⟆ ⟧ σ_t)) (observe t) 
              ∧ sim_indF sim_coindF Ψ (observe (⟦ ⟅ a1 ⟆ ⟧ σ_t)) (observe t) -∗
    sim_expr_inner interp_mrec_rec (sim_indF interp_mrec_rec) Ψ
      (observe (⟦ interp_mrec f a1 ⟧ σ_t)) (observe (⟦ interp_mrec g a2 ⟧ σ_s)).
  Proof.
    intros Ha Ht.
    to_eq in Ht; rewrite Ht; clear Ht.
    to_eq in Ha; rewrite Ha; clear Ha.

    iIntros "#HΨ Hfg Hinner".
    iDestruct "Hinner" as "(_ & Hinner)".
    rewrite -sim_coindF_unfold. rewrite /sim_expr_inner.
    iPoseProof (sim_coindF_F_inv_R with "HΨ Hinner") as ">Hinner".

    change
      (|==>
        ∃ c : sim_case,
          match c with
          | BASE => _
          | STUTTER_L => stutter_l
          | STUTTER_R => stutter_r
          | TAU_STEP => tau_step
          | VIS_STEP => _
          | SOURCE_UB => source_ub
          | SOURCE_EXC => source_exc
          end)%I with
          (sim_expr_inner interp_mrec_rec (sim_indF interp_mrec_rec) Ψ
            (observe (⟦ interp_mrec f a1 ⟧ σ_t))
            (observe (⟦ interp_mrec g (vis e k) ⟧ σ_s))).

    iDestruct "Hinner" as (???) "Hinner".
    rewrite -itree_eta in H.
    apply interp_L2_conv_F_tau_n_inv with (g := f) in H.
    destruct H as (?&?&?&?&?).
    to_eq in H0; rewrite H0 -sim_indF_unfold.
    rewrite interp_mrec_vis.
    iApply sim_indF_n_taus_L.
    rewrite sim_indF_unfold; provide_case: STUTTER_R.
    cbn. rewrite sim_indF_unfold; provide_case: VIS_STEP.
    rewrite /handle_event; cbn; rewrite /handle_E.
    iSplitL ""; first (iPureIntro; by exists eq_refl).
    iIntros. dependent destruction H1; cbn.
    change (TauF ?x) with (observe (Tau x)).
    rewrite -!interp_mrec_tau.
    iLeft; iModIntro.
    iExists f, _, _, g, _, _; iFrame.
    repeat (iSplitL ""; first done).
    rewrite !interp_L2_conv_tau.
    specialize (H v_s); to_eq in H; rewrite -H.
    by do 2 iApply sim_coindF_tauR.
  Qed.

  Require Import LLVMEvents.

  Lemma interp_mrec_failure_ind_case {T}
    (f g : ∀ T : Type, LLVMEvents.CallE T → L0'expr T) Ψ
    t X (e : _ X) k σ_s σ_t (a1 a2: _ T) :
    t ≅ vis (e : FailureE _) k ->
    □ (∀ x y, (base x y ∗ Ψ x y) ∗-∗ Ψ x y) -∗
    interp_mrec_ind Ψ (observe t) (observe (⟦ ⟅ a2 ⟆ ⟧ σ_s))
              ∧ sim_indF sim_coindF Ψ (observe t) (observe (⟦ ⟅ a2 ⟆ ⟧ σ_s)) -∗
    sim_expr_inner interp_mrec_rec (sim_indF interp_mrec_rec) Ψ
      (observe (⟦ interp_mrec f a1 ⟧ σ_t)) (observe (⟦ interp_mrec g a2 ⟧ σ_s)).
  Proof.
    intros H.
    to_eq in H; rewrite H; clear H.
    iIntros "#HΨ Hinner".
    iDestruct "Hinner" as "(_ & Hinner)".
    rewrite -sim_coindF_unfold.
    iPoseProof (sim_coindF_fail_inv with "HΨ Hinner") as "%H'".

    destruct H' as [ (?&?&?) | (?&?&?) ].
    (* exception case *)
    { eapply interp_L2_conv_failure_tau_n_inv in H.
      destruct H as (?&?&?).
      to_eq in H; rewrite H -sim_indF_unfold.
      iApply sim_indF_n_taus_R.
      rewrite sim_indF_unfold /sim_expr_inner.
      by provide_case: SOURCE_EXC. }

    (* UB case *)
    { eapply interp_L2_conv_UB_tau_n_inv with (g := g) in H.
      destruct H as (?&?); to_eq in H; rewrite H -sim_indF_unfold.
      iApply sim_indF_n_taus_R; rewrite sim_indF_unfold.
      by provide_case: SOURCE_UB. }

    Unshelve. all : done.
  Qed.

  Lemma interp_mrec_UB_ind_case {T}
    (f g : ∀ T : Type, LLVMEvents.CallE T → L0'expr T) Ψ
    t X (e : _ X) k σ_s σ_t (a1 a2: _ T):
    t ≅ vis (e : UBE _) k ->
    □ (∀ x y, (base x y ∗ Ψ x y) ∗-∗ Ψ x y) -∗
    interp_mrec_ind Ψ (observe t) (observe (⟦ ⟅ a2 ⟆ ⟧ σ_s))
              ∧ sim_indF sim_coindF Ψ (observe t) (observe (⟦ ⟅ a2 ⟆ ⟧ σ_s)) -∗
    sim_expr_inner interp_mrec_rec (sim_indF interp_mrec_rec) Ψ
      (observe (⟦ interp_mrec f a1 ⟧ σ_t)) (observe (⟦ interp_mrec g a2 ⟧ σ_s)).
  Proof.
    intros H.
    to_eq in H; rewrite H; clear H.
    iIntros "HΨ Hinner".
    iDestruct "Hinner" as "(_ & Hinner)".
    rewrite -sim_coindF_unfold.
    iPoseProof (sim_coindF_UBE_inv with "HΨ Hinner") as "%H'".

    destruct H' as [ (?&?&?) | (?&?&?) ].
    (* exception case *)
    { eapply interp_L2_conv_failure_tau_n_inv in H.
      destruct H as (?&?&?).
      to_eq in H; rewrite H -sim_indF_unfold.
      iApply sim_indF_n_taus_R.
      rewrite sim_indF_unfold /sim_expr_inner.
      by provide_case: SOURCE_EXC. }

    (* UB case *)
    { eapply interp_L2_conv_UB_tau_n_inv with (g := g) in H.
      destruct H as (?&?).
      to_eq in H; rewrite H -sim_indF_unfold.
      iApply sim_indF_n_taus_R.
      rewrite sim_indF_unfold /sim_expr_inner.
      by provide_case: SOURCE_UB. }

    Unshelve. all : done.
  Qed.

  Lemma interp_mrec_pred_coind_init {T}
      (f : ∀ T : Type, CallE T → L0'expr T)
      (g : ∀ T : Type, CallE T → L0'expr T)
      (a1 a2 : itree L0' _) (σ_t σ_s : state vir_lang) Ψ:
      context_rel f g -∗
      ⟅ a1 ⟆ ⪯⟅ a2 ⟆ [[ Ψ ⤉ ]] -∗
      state_interp σ_t σ_s ==∗
      interp_mrec_pred (lift_rel (Ψ ⤉))
        (observe (⟦ interp_mrec (T := T) f a1 ⟧ σ_t))
        (observe (⟦ interp_mrec (T := T) g a2 ⟧ σ_s)).
  Proof.
    iIntros "H H' SI".
    rewrite /interp_mrec_pred.
    iExists f, a1, σ_t, g, a2, σ_s.
    iMod ("H'" with "SI").
    iModIntro.
    do 2 (iSplitL ""; [ done | ]).
    iSplitL ""; [ | iFrame ].
    iIntros (??); iModIntro; iSplitL.
    - iIntros "(H1 & H2)"; eauto.
    - iIntros "H"; eauto.
      iDestruct "H" as (????) "(SI & H)".
      iDestruct "H" as (??) "H".
      iDestruct "H" as (????) "H".
      iSplitL "".
      { rewrite /base. iExists _, _; eauto.
        apply eqitree_inv_Ret_r in H1, H2.
        cbn in H.
        iSplit; iPureIntro.
        { apply EqAxiom.bisimulation_is_eq.
          rewrite H. rewrite -itree_eta.
          rewrite (itree_eta e_t).
          rewrite H1; cbn. rewrite /interp_L2.
          setoid_rewrite StateFacts.interp_state_ret; done. }
        { apply EqAxiom.bisimulation_is_eq.
          rewrite H0. rewrite -itree_eta.
          rewrite (itree_eta e_s).
          rewrite H2; cbn. rewrite /interp_L2.
          setoid_rewrite StateFacts.interp_state_ret; done. } }
      { rewrite /base. iExists _, _; eauto.
        apply eqitree_inv_Ret_r in H1, H2.
        repeat iExists _; iFrame.
        do 2 (iSplitL ""; [ done | ]).
        repeat iExists _; iSplitL ""; try iPureIntro.
        - setoid_rewrite (itree_eta e_t); by rewrite H1.
        - setoid_rewrite (itree_eta e_s); rewrite H2; by iFrame "H". }
  Qed.

  Lemma Proper_interp_mrec_base_case {T}
      (Ψ : st_exprO' T -d> st_exprO' T -d> iPropI Σ)
      (a1 a2 : itree (CallE +' language.L0 vir_lang) T)
      (f : ∀ T : Type, CallE T → L0'expr T)
      (g : ∀ T : Type, CallE T → L0'expr T)
      (σ_t σ_s : state vir_lang) :
    □ (∀ x y : st_exprO' T, base x y ∗ Ψ x y ∗-∗ Ψ x y) -∗
    context_rel f g -∗
    Ψ (observe (⟦ ⟅ a1 ⟆ ⟧ σ_t)) (observe (⟦ ⟅ a2 ⟆ ⟧ σ_s)) -∗
    sim_expr_inner interp_mrec_rec (sim_indF interp_mrec_rec) Ψ
      (observe (⟦ interp_mrec f a1 ⟧ σ_t)) (observe (⟦ interp_mrec g a2 ⟧ σ_s)).
  Proof.
    iIntros "#He Hinner Hr".
    iSpecialize ("He" with "Hr").
    iDestruct "He" as "(Hb & He)".
    iDestruct "Hb" as (???) "%Hb".
    inversion H; inversion Hb.
    symmetry in H1; symmetry in H2.
    apply simpobs, interp_L2_conv_ret_inv in H1, H2.
    to_eq in H1; to_eq in H2; subst; cbn; by provide_case: BASE.
  Qed.

  Lemma Proper_interp_mrec_stutter_l_case {T}
      (Ψ : st_exprO' T -d> st_exprO' T -d> iPropI Σ)
      (f : ∀ T : Type, CallE T → L0'expr T)
      (g : ∀ T : Type, CallE T → L0'expr T)
      (a1 a2 : itree (CallE +' language.L0 vir_lang) T)
      (σ_t σ_s : state vir_lang)
      (t : L2_expr vir_lang T)
      (H0 : observe (⟦ ⟅ a1 ⟆ ⟧ σ_t) = TauF t) :
    □ (∀ x y : st_exprO' T, base x y ∗ Ψ x y ∗-∗ Ψ x y) -∗
    context_rel f g -∗
    interp_mrec_ind Ψ (observe t) (observe (⟦ ⟅ a2 ⟆ ⟧ σ_s))
    ∧ sim_indF sim_coindF Ψ (observe t) (observe (⟦ ⟅ a2 ⟆ ⟧ σ_s)) -∗
    sim_expr_inner interp_mrec_rec (sim_indF interp_mrec_rec) Ψ
      (observe (⟦ interp_mrec f a1 ⟧ σ_t)) (observe (⟦ interp_mrec g a2 ⟧ σ_s)).
  Proof.
    iIntros "He Hr Hinner".

    symmetry in H0; apply simpobs in H0.
    rewrite /sim_expr_inner.
    apply interp_L2_conv_tau_inv in H0.
    destruct H0 as [(?&?&?)| (?&?&?&?&?) ].
    { (* Tau *)
      iDestruct "Hinner" as "(Hinner & _)".
      apply EqAxiom.bisimulation_is_eq in H0.
      iSpecialize ("Hinner" $! f g _ _ _ _ with "He"); subst.
      iSpecialize ("Hinner" $! eq_refl eq_refl with "Hr").
      provide_case: STUTTER_L; symmetry in H.
      apply simpobs, EqAxiom.bisimulation_is_eq in H; subst; cbn; by eauto. }

    { (* Vis case *)
      symmetry in H; apply simpobs in H.
      to_eq in H; rewrite H.

      pose proof (handle_noncall_L0_L2_case x x0 σ_t) as Hnoncall.
      destruct Hnoncall as
        [ (?&?) |
          [ (?&?&?&?) |
            [ (?&?&?&?) |
              (?&?&?) ] ] ].

      { (* [handle_noncall_L0_L2] Ret case *)
        rewrite H1 bind_ret_l in H0.
        iDestruct "Hinner" as "(Hinner & _)".
        rewrite /F -!interp_state_tau -!interp_tau in H0; to_eq in H0; subst.
        iSpecialize ("Hinner" $! f g (Tau (Tau (x1 x2.2)))
                        _ x2.1 _ with "He").
        iSpecialize ("Hinner" $! eq_refl eq_refl with "Hr").
        to_eq in H1; rewrite interp_mrec_vis H1 !interp_mrec_tau.
        by provide_case: STUTTER_L. }

      { (* failure case *)
        iApply (interp_mrec_failure_ind_case with "He Hinner"); eauto.
        rewrite H0 H1; by tau_steps. }

      { (* UB case *)
        iApply (interp_mrec_UB_ind_case with "He Hinner"); eauto.
        rewrite H0 H1; by tau_steps. }

      { (* Other cases *)
        dependent destruction H2.
        iApply (interp_mrec_F_ind_case with "He Hr Hinner"); eauto.
        { apply eqit_Vis; done. }

        rewrite H0 H1 bind_vis. apply eqit_Vis.
        intros. cbn. rewrite bind_ret_l. by cbn. } }
  Qed.

  Lemma Proper_interp_mrec_stutter_r_case {T}
      (Ψ : st_exprO' T -d> st_exprO' T -d> iPropI Σ)
      (f : ∀ T : Type, CallE T → L0'expr T)
      (g : ∀ T : Type, CallE T → L0'expr T)
      (a1 a2 : itree (CallE +' language.L0 vir_lang) T)
      (σ_t σ_s : state vir_lang)
      (t : L2_expr vir_lang T)
      (H0 : observe (⟦ ⟅ a2 ⟆ ⟧ σ_s) = TauF t):
    □ (∀ x y : st_exprO' T, base x y ∗ Ψ x y ∗-∗ Ψ x y) -∗
    context_rel f g -∗
    interp_mrec_ind Ψ (observe (⟦ ⟅ a1 ⟆ ⟧ σ_t)) (observe t)
    ∧ sim_indF sim_coindF Ψ (observe (⟦ ⟅ a1 ⟆ ⟧ σ_t)) (observe t) -∗
    sim_expr_inner interp_mrec_rec (sim_indF interp_mrec_rec) Ψ
      (observe (⟦ interp_mrec f a1 ⟧ σ_t))
      (observe (⟦ interp_mrec g a2 ⟧ σ_s)).
  Proof.
    iIntros "He Hr Hinner".

    symmetry in H0; apply simpobs in H0.
    apply interp_L2_conv_tau_inv in H0.
    destruct H0 as [(?&?&?)| (?&?&?&?&?) ].
    { (* Tau *)
      rewrite /sim_expr_inner.
      iDestruct "Hinner" as "(Hinner & _)".
      apply EqAxiom.bisimulation_is_eq in H0.
      iSpecialize ("Hinner" $! f g _ _ _ _ with "He"); subst.
      iSpecialize ("Hinner" $! eq_refl eq_refl with "Hr").
      provide_case: STUTTER_R; symmetry in H.
      apply simpobs, EqAxiom.bisimulation_is_eq in H; subst; cbn; by eauto. }

    { (* Vis case *)
      symmetry in H; apply simpobs in H.
      to_eq in H; rewrite H.

      pose proof (handle_noncall_L0_L2_case x x0 σ_s) as Hnoncall.
      destruct Hnoncall as
        [ (?&?) |
          [ (?&?&?&?) |
            [ (?&?&?&?) |
              (?&?&?) ] ] ].

      { (* [handle_noncall_L0_L2] Ret case *)
        rewrite H1 bind_ret_l in H0.
        iDestruct "Hinner" as "(Hinner & _)".
        rewrite /F -!interp_state_tau -!interp_tau in H0; to_eq in H0; subst.
        iSpecialize ("Hinner" $! f g _ _ _ _ with "He").
        iSpecialize ("Hinner" $! eq_refl eq_refl with "Hr").
        to_eq in H1; rewrite interp_mrec_vis H1 !interp_mrec_tau.
        by provide_case: STUTTER_R. }

      { (* failure case *)
        iClear "Hinner". rewrite interp_mrec_vis; to_eq in H1; rewrite H1.
        provide_case: STUTTER_R; cbn.
        rewrite sim_indF_unfold. by provide_case: SOURCE_EXC. }

      { (* UB case *)
        iClear "Hinner". rewrite interp_mrec_vis; to_eq in H1; rewrite H1.
        provide_case: STUTTER_R; cbn.
        rewrite sim_indF_unfold. by provide_case: SOURCE_UB. }

      { (* Other cases *)
        dependent destruction H2.
        iApply (interp_mrec_F_ind_case' with "He Hr Hinner"); eauto.
        { apply eqit_Vis; done. }

        rewrite H0 H1 bind_vis. apply eqit_Vis.
        intros. cbn. rewrite bind_ret_l. by cbn. } }
  Qed.

  Lemma Proper_interp_mrec_tau_case {T}
      (Ψ : st_exprO' T -d> st_exprO' T -d> iPropI Σ)
      (f : ∀ T : Type, CallE T → L0'expr T)
      (g : ∀ T : Type, CallE T → L0'expr T)
      (a1 a2 : itree (CallE +' language.L0 vir_lang) T)
      (σ_t σ_s : state vir_lang)
      (t s : L2_expr vir_lang T)
      (H0 : observe (⟦ ⟅ a1 ⟆ ⟧ σ_t) = TauF t)
      (H1 : observe (⟦ ⟅ a2 ⟆ ⟧ σ_s) = TauF s) :
    □ (∀ x y : st_exprO' T, base x y ∗ Ψ x y ∗-∗ Ψ x y) -∗
    context_rel f g -∗
    sim_coindF Ψ (observe t) (observe s) -∗
    sim_expr_inner interp_mrec_rec (sim_indF interp_mrec_rec) Ψ
      (observe (⟦ interp_mrec f a1 ⟧ σ_t))
      (observe (⟦ interp_mrec g a2 ⟧ σ_s)).
  Proof.
    iIntros "He Hr Hinner".
    symmetry in H0, H1. apply simpobs in H0, H1.

    apply interp_L2_conv_tau_inv in H0.
    (* Target case analysis*)
    destruct H0 as [(?&?&?)| (?&?&?&?&?)].

    { (* Tau Tau *)
      symmetry in H; apply simpobs in H; to_eq in H; subst.
      rewrite interp_mrec_tau.

      apply interp_L2_conv_tau_inv in H1.
      destruct H1 as [(?&?&?)| (?&?&?&?&?) ].
      - symmetry in H; apply simpobs in H; to_eq in H; subst.
        rewrite interp_mrec_tau.
        provide_case: TAU_STEP.
        to_eq in H0; to_eq in H1; subst.
        iLeft; iExists f, _, _, g, _, _;
          do 2 (iSplitL ""; [ done | ]); by iFrame.

      - symmetry in H; apply simpobs in H; to_eq in H; subst.
        pose proof (handle_noncall_L0_L2_case x0 x1 σ_s).
        destruct H as [ (?&?) | [ (?&?&?&?) | [ (?&?&?&?) | (?&?&?) ] ] ].
        { rewrite interp_mrec_vis.
          to_eq in H; rewrite H. rewrite H bind_ret_l in H1.
          to_eq in H0; to_eq in H1; rewrite H0 H1.
          provide_case: TAU_STEP.
          iLeft.
          iExists f, x, σ_t, g, (Tau (Tau (x2 x3.2))), x3.1.
          (iSplitL ""; [ done | ]); iSplitL "".
          { iPureIntro. f_equiv. to_eq. rewrite bind_ret_l.
            by rewrite -!interp_mrec_tau. }
          iFrame. by rewrite !interp_L2_conv_tau. }

        { rewrite interp_mrec_vis.
          to_eq in H; rewrite H. rewrite H bind_vis in H1.
          to_eq in H0; to_eq in H1; rewrite H0 H1.
          provide_case: TAU_STEP.
          iRight; cbn. iClear "Hinner".
          rewrite sim_coindF_unfold sim_indF_unfold.
          rewrite /subevent; unfold_cat.
          by provide_case: SOURCE_EXC. }

        { rewrite interp_mrec_vis.
          to_eq in H; rewrite H. rewrite H bind_vis in H1.
          to_eq in H0; to_eq in H1; rewrite H0 H1.
          provide_case: TAU_STEP.
          iRight; cbn. iClear "Hinner".
          rewrite sim_coindF_unfold sim_indF_unfold.
          rewrite /subevent; unfold_cat.
          by provide_case: SOURCE_UB. }

        { rewrite interp_mrec_vis. iDestruct "He" as "#He".
          to_eq in H; rewrite H. rewrite H bind_vis in H1.
          setoid_rewrite bind_ret_l in H1.
          to_eq in H0; to_eq in H1; rewrite H0 H1.
          cbn; rewrite /subevent; unfold_cat.
          iDestruct (sim_coindF_F_inv_R with "He Hinner") as ">H".
          to_inner (interp_mrec_rec (R1 := T) (R2 := T)).
          iDestruct "H" as (???) "H".
          rewrite -itree_eta in H3.
          pose proof (interp_L2_conv_F_tau_n_inv _ _ _ _ _ f H3) as H';
            clear H3.
          destruct H' as (?&?&?&?&?).
          to_eq in H4. rewrite H4.
          change (TauF (n_taus ?x ?n)) with (observe (n_taus x (S n))).
          pose proof (n_taus_S (vis x3
             (λ x7 : x0, Tau (Tau (⟦ interp_mrec f (x5 x7) ⟧ x6)))) x4).
          to_eq in H5; rewrite -H5; clear H5.
          rewrite -sim_indF_unfold; iApply sim_indF_n_taus_L.
          rewrite sim_indF_unfold; provide_case: STUTTER_L.
          rewrite sim_indF_unfold; provide_case: STUTTER_R.
          rewrite sim_indF_unfold; provide_case: VIS_STEP.
          iSplitL "".
          { by iPureIntro; to_eq; rewrite -itree_eta bind_vis;
            setoid_rewrite bind_ret_l; cbn. }

          cbn; unfold_cat. rewrite /handle_E.
          iSplitL ""; first (iPureIntro; by exists eq_refl).
          iIntros. dependent destruction H5.
          rewrite -!interp_mrec_tau.
          iLeft; iExists f, _, _, g, _, _.
          do 2 (iSplitL ""; [ done | ]); iSplitL ""; iFrame;
          first done. rewrite !interp_L2_conv_tau.
          do 2 iApply sim_coindF_tauR.
          specialize (H3 v_s); to_eq in H3; rewrite -H3; by clear H3. } }

    (* Event *)
    symmetry in H; apply simpobs in H; to_eq in H; subst.
    rewrite interp_mrec_vis.

    pose proof (handle_noncall_L0_L2_case x x0 σ_t).
    destruct H as [ (?&?) | [ (?&?&?&?) | [ (?&?&?&?) | (?&?&?) ] ] ].
    { to_eq in H; rewrite H.
      apply interp_L2_conv_tau_inv in H1.
      destruct H1 as [(?&?&?)| (?&?&?&?&?) ].
      - symmetry in H1; apply simpobs in H1; to_eq in H1; subst.
        rewrite interp_mrec_tau.
        provide_case: TAU_STEP.
        iLeft; iExists f, _, _, g, _, _.
        iSplitL "".
        { iPureIntro. f_equiv. to_eq.
          by rewrite bind_ret_l -!interp_mrec_tau. }
          (iSplitL ""; [ done | ]); iFrame.
        rewrite H bind_ret_l in H0.
        to_eq in H2; to_eq in H0. rewrite -H2.
        by rewrite !interp_L2_conv_tau -H0.

      - symmetry in H1; apply simpobs in H1; to_eq in H1; subst.
        pose proof (handle_noncall_L0_L2_case x3 x4 σ_s).
        destruct H1 as [ (?&?) | [ (?&?&?&?) | [ (?&?&?&?) | (?&?&?) ] ] ].
        { rewrite interp_mrec_vis.
          to_eq in H1; rewrite H1.
          provide_case: TAU_STEP.
          iLeft. iExists f, _, _, g, _, _.

          iSplitL "".
          { iPureIntro. f_equiv. to_eq.
            by rewrite bind_ret_l -!interp_mrec_tau. }
          iSplitL "".
          { iPureIntro. f_equiv. to_eq.
            by rewrite bind_ret_l -!interp_mrec_tau. }
          iFrame.
          rewrite H bind_ret_l in H0. rewrite H1 bind_ret_l in H2.
          to_eq in H2; to_eq in H0.
          by rewrite !interp_L2_conv_tau -H0 -H2. }

        { rewrite interp_mrec_vis.
          to_eq in H1; rewrite H1.
          provide_case: TAU_STEP.
          iRight; cbn. iClear "Hinner".
          rewrite sim_coindF_unfold sim_indF_unfold.
          rewrite /subevent; unfold_cat.
          by provide_case: SOURCE_EXC. }

        { rewrite interp_mrec_vis.
          to_eq in H1; rewrite H1.
          provide_case: TAU_STEP.
          iRight; cbn. iClear "Hinner".
          rewrite sim_coindF_unfold sim_indF_unfold.
          rewrite /subevent; unfold_cat.
          by provide_case: SOURCE_UB. }

        { rewrite interp_mrec_vis. iDestruct "He" as "#He".
          to_eq in H1; rewrite H1. rewrite H1 bind_vis in H2.
          setoid_rewrite bind_ret_l in H2.
          rewrite H bind_ret_l in H0.
          to_eq in H2; to_eq in H0; rewrite H2 H0.

          iPoseProof (contains_base_tauL with "He") as "Ht".
          do 2 iPoseProof (sim_coindF_TauL_inv with "Ht Hinner") as "Hinner".
          iDestruct (sim_coindF_F_inv_R with "He Hinner") as ">H".
          to_inner (interp_mrec_rec (R1 := T) (R2 := T)).
          iDestruct "H" as (???) "H".
          rewrite -itree_eta in H4.
          provide_case: STUTTER_L; cbn.
          rewrite sim_indF_unfold; provide_case: STUTTER_R.
          do 2 (rewrite sim_indF_unfold; provide_case: STUTTER_L).
          pose proof (interp_L2_conv_F_tau_n_inv _ _ _ _ _ f H4) as H';
            clear H4.
          destruct H' as (?&?&?&?&?).
          to_eq in H5. rewrite H5.
          iApply sim_indF_n_taus_L; cbn.
          rewrite sim_indF_unfold; provide_case: VIS_STEP.
          iSplitL "".
          { iPureIntro; by exists eq_refl. }
          iIntros (??) "%Hv". dependent destruction Hv; cbn.
          change (TauF ?x) with (observe (Tau x)).
          rewrite -!interp_mrec_tau.
          iLeft; iExists f, _, _, g, _, _.
          do 2 (iSplitL ""; [ done | ]); iSplitL ""; iFrame;
          first done. rewrite !interp_L2_conv_tau.
          do 2 iApply sim_coindF_tauR.
          specialize (H4 v_s); to_eq in H4; rewrite -H4; by clear H4. } }

    { to_eq in H; rewrite H; rewrite H bind_vis in H0.
      to_eq in H0; rewrite H0.
       iDestruct (sim_coindF_fail_inv with "He Hinner") as %Hfail.

      destruct Hfail as [(?&?&Hfail) | (?&?&?)].

      (* Failure *)
      { rewrite Hfail in H1.
        change (Tau (n_taus ?x ?n)) with (n_taus x (S n)) in H1.
        eapply interp_L2_conv_failure_tau_n_inv in H1.
        destruct H1 as (?&?&?).
        to_eq in H1; rewrite H1.
        rewrite -sim_indF_unfold.
        iApply sim_indF_n_taus_R.
        rewrite sim_indF_unfold /sim_expr_inner.
        by provide_case: SOURCE_EXC. }

      { rewrite H2 in H1.
        change (Tau (n_taus ?x ?n)) with (n_taus x (S n)) in H1.
        eapply interp_L2_conv_UB_tau_n_inv in H1.
        destruct H1 as (?&?).
        to_eq in H1; rewrite H1.
        rewrite -sim_indF_unfold.
        iApply sim_indF_n_taus_R.
        rewrite sim_indF_unfold /sim_expr_inner.
        by provide_case: SOURCE_UB. } }

    { to_eq in H; rewrite H;  rewrite H bind_vis in H0.
      to_eq in H0; rewrite H0.
      iDestruct (sim_coindF_UBE_inv with "He Hinner") as %Hfail.

      destruct Hfail as [(?&?&Hfail) | (?&?&?)].
      { rewrite Hfail in H1.
        change (Tau (n_taus ?x ?n)) with (n_taus x (S n)) in H1.
        eapply interp_L2_conv_failure_tau_n_inv in H1.

        destruct H1 as (?&?&?).
        to_eq in H1; rewrite H1.
        rewrite -sim_indF_unfold.
        iApply sim_indF_n_taus_R.
        rewrite sim_indF_unfold /sim_expr_inner.
        by provide_case: SOURCE_EXC. }

      { rewrite H2 in H1.
        change (Tau (n_taus ?x ?n)) with (n_taus x (S n)) in H1.
        eapply interp_L2_conv_UB_tau_n_inv in H1.
        destruct H1 as (?&?).
        to_eq in H1; rewrite H1.
        rewrite -sim_indF_unfold.
        iApply sim_indF_n_taus_R.
        rewrite sim_indF_unfold /sim_expr_inner.
        by provide_case: SOURCE_UB. } }

    { to_eq in H; rewrite H; rewrite H bind_vis in H0.
      setoid_rewrite bind_ret_l in H0; cbn in H0.
      to_eq in H0; rewrite H0.
      iDestruct "He" as "#He".

      iDestruct (sim_coindF_F_inv_L with "He Hinner") as
        ">[ Hinner | [ Hinner | Hinner ] ]".
      { to_inner (interp_mrec_rec (R1 := T) (R2 := T)).
        iDestruct "Hinner" as (? ? Hfail) "Hinner".
        pose proof (Heq := Hfail).
        rewrite -itree_eta in Hfail.
        rewrite Hfail in H1.
        change (Tau (n_taus ?x ?n)) with (n_taus x (S n)) in H1.

        apply (interp_L2_conv_F_tau_n_inv _ _ _ _ _ g) in H1.
        destruct H1 as (?&?&?&?&?).
        to_eq in H3; rewrite H3.
        rewrite -itree_eta in Heq; to_eq in Heq.
        to_inner (interp_mrec_rec (R1 := T) (R2 := T)).
        rewrite -sim_indF_unfold.
        iApply sim_indF_n_taus_R.
        rewrite sim_indF_unfold; provide_case:STUTTER_L.
        cbn.
        rewrite sim_indF_unfold; provide_case:VIS_STEP.
        cbn. rewrite /handle_E.
        iSplitL ""; first (iPureIntro; exists eq_refl; reflexivity).
        iIntros (???). dependent destruction H3.
        cbn; change (TauF ?x) with (observe (Tau x)).
        rewrite -!interp_mrec_tau.
        iLeft.
        iExists f, _, _, g, _, _;
          do 2 (iSplitL ""; [ done | ]); iFrame; iSplitL ""; first done.
        iModIntro. rewrite !interp_L2_conv_tau.
        specialize (H1 v_s); to_eq in H1; rewrite -H1.
        do 2 iApply sim_coindF_tauL. by dependent destruction H4. }

      { iDestruct "Hinner" as (?????) "Hinner".
        rewrite -itree_eta in H3.
        rewrite H3 in H1.
        change (Tau (n_taus ?x ?n)) with (n_taus x (S n)) in H1.
        eapply interp_L2_conv_UB_tau_n_inv with (g := g) in H1.
        destruct H1 as (?&?).
        to_eq in H1; rewrite H1.
        to_inner (interp_mrec_rec (R1 := T) (R2 := T)).
        rewrite -sim_indF_unfold.
        change (Tau (n_taus ?x ?n)) with (n_taus x (S n)).
        iApply sim_indF_n_taus_R.
        rewrite sim_indF_unfold; by provide_case: SOURCE_UB. }

      { iDestruct "Hinner" as (?????) "Hinner".
        rewrite -itree_eta in H3.
        rewrite H3 in H1.
        change (Tau (n_taus ?x ?n)) with (n_taus x (S n)) in H1.
        eapply interp_L2_conv_failure_tau_n_inv with (g := g) in H1.
        destruct H1 as (?&?&?).
        to_eq in H1; rewrite H1.
        to_inner (interp_mrec_rec (R1 := T) (R2 := T)).
        rewrite -sim_indF_unfold.
        change (Tau (n_taus ?x ?n)) with (n_taus x (S n)).
        iApply sim_indF_n_taus_R.
        rewrite sim_indF_unfold; by provide_case: SOURCE_EXC. } }

    Unshelve. all : eauto.
  Qed.

  Lemma vir_call_ans_attr τ addr args attr τ' addr' args' attr' v1 v2 C:
    vir_call_ans Σ (ExternalCall τ addr args attr) v1 (ExternalCall τ' addr' args' attr') v2 C -∗
    vir_call_ans Σ (ExternalCall τ addr args (FNATTR_External :: attr)) v1
                   (ExternalCall τ' addr' args' (FNATTR_External :: attr')) v2 C.
  Proof.
    destruct C as (?&?).
    simp vir_call_ans.
    iIntros "H". done.
  Qed.

  Theorem Proper_interp_mrec {T}
    (f g : ∀ T : Type, LLVMEvents.CallE T → L0'expr T) a1 a2 Ψ:
    context_rel f g -∗
    ⟅ a1 ⟆ ⪯ ⟅ a2 ⟆ [[ Ψ ⤉ ]] -∗
    interp_mrec (T := T) f a1 ⪯ interp_mrec (T := T) g a2 [[ Ψ ⤉ ]].
  Proof.
    iIntros "H H'"; iIntros (??) "SI".

    iApply (sim_coindF_strong_coind interp_mrec_pred);
      last iApply (interp_mrec_pred_coind_init with "H H' SI"); eauto.

    iModIntro. clear f g a1 a2 σ_t σ_s.
    iIntros (Φ e_t e_s) "IH".
    iDestruct "IH" as (????????) "(H1 & H2 & H3)"; subst.

    rewrite sim_coindF_unfold.
    iAssert (∀ Ψ e_t e_s, (sim_indF sim_coindF Ψ e_t e_s) -∗
      interp_mrec_ind Ψ e_t e_s)%I as "Hgen"; last first.
    { iSpecialize ("Hgen" with "H3").
      iSpecialize ("Hgen" $! _ _ _ _ _ _ with "H1"); try done.
      iSpecialize ("Hgen" $! eq_refl eq_refl with "H2").
      iApply "Hgen". }

    clear Φ f a1 σ_t g a2 σ_s Ψ.
    iIntros (Ψ e_t e_s) "Hsim".

    iApply (sim_indF_strong_ind with "[] Hsim"); clear Ψ e_t e_s.

    iModIntro. iIntros (Ψ e_t e_s) "Hinner".
    iIntros (??????) "#He".
    iIntros (??) "Hr". subst.

    (* [Hinner] for the "inner" expression, i.e. [e_s] *)
    rewrite /sim_expr_inner.
    cbn -[F] in *; rewrite sim_indF_unfold /sim_expr_inner.
    iMod "Hinner".

    to_inner (interp_mrec_rec (R1 := T) (R2 := T)).

    iDestruct "Hinner" as ( c ) "Hinner";
      destruct c; try case_solve; try done.

    { (* [BASE] case *)
      by iApply (Proper_interp_mrec_base_case with "He Hr Hinner"). }

    { (* [STUTTER_L] case *)
      by iApply (Proper_interp_mrec_stutter_l_case with "He Hr Hinner"). }

    { (* [STUTTER_R] case*)
      by iApply (Proper_interp_mrec_stutter_r_case with "He Hr Hinner"). }

    { (* [TAU_STEP] case*)
      by iApply (Proper_interp_mrec_tau_case with "He Hr Hinner"). }

    { (* [VIS] case *)
      symmetry in H0; apply simpobs in H0;
      symmetry in H1; apply simpobs in H1.
      pose proof (H0' := H0).
      pose proof (H1' := H1).
      apply interp_L2_conv_vis_inv in H0; apply interp_L2_conv_vis_inv in H1.

      destruct H0 as [ (?&?&?&?&?&?) | (?&?&?&?) ];
      destruct H1 as [ (?&?&?&?&?&?) | (?&?&?&?) ].
      { (* Internal call *)
        to_eq in H; to_eq in H0;
          rewrite H H0 !interp_mrec_call.
        rewrite H in H0'; rewrite H0 in H1'.
        rename x into τ, x0 into addr,
          x1 into args, x2 into attrs, x3 into k;
        rename x4 into τ', x5 into addr',
          x6 into args', x7 into attrs', x8 into k'.

        setoid_rewrite interp_vis in H0';
        rewrite /subevent in H0'; unfold_cat in H0'; simp L0'_conv in H0'.
        setoid_rewrite interp_vis in H1';
        rewrite /subevent in H1'; unfold_cat in H1'; simp L0'_conv in H1'.

        rewrite bind_trigger in H0'. rewrite bind_trigger in H1'.
        setoid_rewrite interp_state_vis in H0';
        rewrite /subevent in H0'; unfold_cat in H0'; cbn in H0';
          rewrite /handle_stateEff in H0'; rewrite bind_vis in H0'.

        setoid_rewrite interp_state_vis in H1';
        rewrite /subevent in H1'; unfold_cat in H1'; cbn in H1';
          rewrite /handle_stateEff in H1'; rewrite bind_vis in H1'.

        setoid_rewrite bind_ret_l in H0';
        setoid_rewrite interp_state_tau in H0'.

        setoid_rewrite bind_ret_l in H1';
        setoid_rewrite interp_state_tau in H1'.

        apply eqit_inv_Vis_weak in H0', H1'.
        destruct H0' as (d&He&Hk); dependent destruction d.
        destruct H1' as (d&He'&Hk'); dependent destruction d.
        red in He; red in He'.
        rewrite /subevent in He He'; unfold_cat in He; unfold_cat in He'.
        subst. red in Hk, Hk'.

        rewrite /handle_event. simp handle_call_events.

        iDestruct "Hinner" as "[ Hinner | Hinner ]"; cycle 1.

        (* Internal call was "external" and now meets the spec *)
        { iDestruct "Hinner" as (?) "(SI & Hev & Hinner)".
          provide_case: TAU_STEP.
          iLeft. iDestruct "Hr" as "#Hr".
          iExists f, _, _, g, _, _.
          repeat (iSplitL ""; first done); iFrame.
          iDestruct "Hr" as (??) "(Hr_inv & _)".

          (* Cut on internal call *)
          rewrite !interp_L2_conv_bind; iApply sim_coindF_coind_bind.

          iSpecialize ("Hr_inv" with "Hev SI").
          match goal with
            | |- environments.envs_entails _ (sim_coindF ?Φ _ _) => remember Φ
          end.
          setoid_rewrite sim_coindF_unfold at 3.
          rewrite sim_indF_unfold /sim_expr_inner. iMod "Hr_inv".

          to_inner (sim_coindF (R1 := uvalue) (R2 := uvalue)).
          rewrite -sim_indF_unfold -sim_coindF_unfold.
          destruct H. rewrite H. destruct H0. rewrite H0.
          iApply (sim_coindF_bupd_mono with "[Hinner]"); last done; subst.
          iIntros (??) "HΦ". clear H H1 H0 H2.

          iDestruct "HΦ" as (????) "(SI & %Ht & %Hs & HΦ)"; subst.
          iDestruct "HΦ" as (????) "HΦ".
          to_eq in H; to_eq in H0; rewrite H H0; cbn -[state_interp].
          pose proof (bind_ret_l (σ_t0, v_t) (fun x => ⟦ ⟅ k x.2 ⟆ ⟧ x.1)).
          to_eq in H1; rewrite H1; clear H1.
          pose proof (bind_ret_l (σ_s0, v_s) (fun x => ⟦ ⟅ k' x.2 ⟆ ⟧ x.1)).
          to_eq in H1; rewrite H1; clear H1.

          cbn -[state_interp].
          specialize (Hk (σ_t0, v_t)); specialize (Hk' (σ_s0, v_s)).

          iCombine "SI HΦ" as "H"; iSpecialize ("Hinner" $! (σ_t0, v_t) (σ_s0, v_s));
            cbn -[state_interp].
          iSpecialize ("Hinner" with "H"); iMod "Hinner".
          to_eq in Hk; to_eq in Hk'; rewrite -Hk -Hk'.

          iPoseProof (contains_base_tauL with "He") as "#HL".
          iPoseProof (contains_base_tauR with "He") as "#HR".

          do 2 (iPoseProof (sim_coindF_TauL_inv with "HL Hinner") as "Hinner").
          do 2 (iPoseProof (sim_coindF_TauR_inv with "HR Hinner") as "Hinner");
          done.
        }

        { (* Calls eq *)
          iDestruct "Hinner" as (?) "(SI & Hcall & Hinner)".
          rewrite /call_args_eq.

          Opaque arg_val_rel.
          iDestruct "Hcall" as "(Hcall & %Hev)"; cbn in Hev; inversion Hev; subst.
          cbn -[state_interp].
          provide_case: TAU_STEP.
          iLeft. iDestruct "Hr" as "#Hr".
          iExists f, _, _, g, _, _.
          repeat (iSplitL ""; first done).

          (* Cut on internal call *)
          rewrite !interp_L2_conv_bind; iApply sim_coindF_coind_bind.
          iDestruct "Hr" as (Hcf Hcg) "(_ & Hr_refl)".
          iSpecialize ("Hr_refl" with "Hcall SI").
          match goal with
            | |- environments.envs_entails _ (sim_coindF ?Φ _ _) => remember Φ
          end.
          setoid_rewrite sim_coindF_unfold at 3.
          rewrite sim_indF_unfold /sim_expr_inner. iMod "Hr_refl".

          to_inner (sim_coindF (R1 := uvalue) (R2 := uvalue)).
          rewrite -sim_indF_unfold -sim_coindF_unfold.
          iApply (sim_coindF_bupd_mono with "[Hinner]"); last done; subst.
          iIntros (??) "HΦ".

          iDestruct "HΦ" as (????) "(SI & %Ht & %Hs & HΦ)"; subst.
          iDestruct "HΦ" as (????) "HΦ".
          to_eq in H; to_eq in H0; rewrite H H0; cbn -[state_interp].
          pose proof (bind_ret_l (σ_t0, v_t) (fun x => ⟦ ⟅ k x.2 ⟆ ⟧ x.1)).
          to_eq in H1; rewrite H1; clear H1.
          pose proof (bind_ret_l (σ_s0, v_s) (fun x => ⟦ ⟅ k' x.2 ⟆ ⟧ x.1)).
          to_eq in H1; rewrite H1; clear H1.

          cbn -[state_interp].
          specialize (Hk (σ_t0, v_t)); specialize (Hk' (σ_s0, v_s)).

          iCombine "SI HΦ" as "H"; iSpecialize ("Hinner" $! (σ_t0, v_t) (σ_s0, v_s));
            cbn -[state_interp].
          destruct C as (?&?).
          iSpecialize ("Hinner" with "H"); iMod "Hinner".
          to_eq in Hk; to_eq in Hk'; rewrite -Hk -Hk'.

          iPoseProof (contains_base_tauL with "He") as "#HL".
          iPoseProof (contains_base_tauR with "He") as "#HR".

          do 2 (iPoseProof (sim_coindF_TauL_inv with "HL Hinner") as "Hinner").
          do 2 (iPoseProof (sim_coindF_TauR_inv with "HR Hinner") as "Hinner");
          done.
        }
      }

      { (* Asymmetric internal-external call - absurd *)
        to_eq in H. rewrite H in H0'.
        setoid_rewrite interp_vis in H0'.
        rewrite /subevent in H0'; unfold_cat in H0'.
        simp call_conv in H0'; rewrite bind_vis in H0'.
        setoid_rewrite interp_state_vis in H0'.
        setoid_rewrite bind_ret_l in H0'.
        setoid_rewrite interp_state_tau in H0'.
        rewrite /subevent in H0'; unfold_cat in H0'.
        cbn in H0'. rewrite /handle_stateEff in H0'.
        rewrite bind_vis in H0'.

        apply eqit_inv_Vis_weak in H0'.
        destruct H0' as (d&He&Hk); dependent destruction d.
        red in He; rewrite /subevent in He; unfold_cat in He.
        subst. red in Hk.
        rewrite /handle_event. destruct es; try done.

        destruct c, p. simp handle_call_events. destruct c.
        to_eq in H0; rewrite H0 in H1'.
        destruct x5.
        - setoid_rewrite interp_vis in H1'.
          rewrite /subevent in H1'; unfold_cat in H1'.
          rewrite /ReSum_sum /case_ /Case_sum1 /case_sum1 /resum in H1'.
          destruct e.
          simp call_conv in H1'. rewrite bind_vis in H1'.
          setoid_rewrite interp_state_vis in H1'.
          cbn in H1'. rewrite bind_vis in H1'.
          apply eqit_inv_Vis_weak in H1'. destruct H1' as (?&?&?).
          dependent destruction x4.
          red in H; inversion H; subst.
          iDestruct "Hinner" as "[ Hinner | Hinner]".
          + iDestruct "Hinner" as (?) "(SI & Hargs & Hinner)".
            rewrite /call_args_eq.
            iDestruct "Hargs" as "(Hargs & %Ha)".
            inversion Ha.
          + iDestruct "Hinner" as (?) "(SI & Hargs & Hinner)".
            rewrite /call_ev. iExFalso. cbn. destruct C as (?&?).
            simp vir_call_ev.
            iDestruct "Hargs" as "(#Hdv & Hargs)".
            iDestruct "Hargs" as (??) "H".
            inversion H2.
        - setoid_rewrite interp_vis in H1'.
          rewrite /subevent in H1'; unfold_cat in H1'.
          rewrite /ReSum_sum /case_ /Case_sum1 /case_sum1 /resum in H1'.
          rewrite bind_vis in H1'.
          setoid_rewrite interp_state_vis in H1'.
          iExFalso. iClear "Hinner".
          destruct s0 as [ | [ | [ | [ | ] ] ] ]; cbn in H1';
            simp call_conv in H1'; cbn in H1'.
          all: try solve [rewrite bind_tau in H1'; by apply eqit_inv in H1'].
          destruct s0.
          all: try solve [rewrite bind_tau in H1'; by apply eqit_inv in H1']. }

      { (* Asymmetric internal-external call *)
        to_eq in H0. rewrite H0 in H1'.
        setoid_rewrite interp_vis in H1'.
        rewrite /subevent in H1'; unfold_cat in H1'.
        simp call_conv in H1'; rewrite bind_vis in H1'.
        setoid_rewrite interp_state_vis in H1'.
        setoid_rewrite bind_ret_l in H1'.
        setoid_rewrite interp_state_tau in H1'.
        rewrite /subevent in H1'; unfold_cat in H1'.
        cbn in H1'. rewrite /handle_stateEff in H1'.
        rewrite bind_vis in H1'.

        apply eqit_inv_Vis_weak in H1'.
        destruct H1' as (d&He&Hk); dependent destruction d.
        red in He; rewrite /subevent in He; unfold_cat in He.
        subst. red in Hk.
        rewrite /handle_event. destruct et; try destruct s; try done.
        2 : destruct s; done.

        destruct c, p. simp handle_call_events. destruct c.
        to_eq in H; rewrite H in H0'.
        destruct x0.
        - setoid_rewrite interp_vis in H0'.
          rewrite /subevent in H0'; unfold_cat in H0'.
          rewrite /ReSum_sum /case_ /Case_sum1 /case_sum1 /resum in H0'.
          destruct e.
          simp call_conv in H0'. rewrite bind_vis in H0'.
          setoid_rewrite interp_state_vis in H0'.
          cbn in H0'. rewrite bind_vis in H0'.
          apply eqit_inv_Vis_weak in H0'. destruct H0' as (?&?&?).
          dependent destruction x.
          red in H0; inversion H0; subst.
          iDestruct "Hinner" as "[ Hinner | Hinner]".
          + iDestruct "Hinner" as (?) "(SI & Hargs & Hinner)".
            rewrite /call_args_eq.
            iDestruct "Hargs" as "(Hargs & %Ha)".
            inversion Ha.
          + iDestruct "Hinner" as (?) "(SI & Hargs & Hinner)".
            rewrite /call_ev. iExFalso. cbn.
            destruct C as (?&?).
            simp vir_call_ev.
            iDestruct "Hargs" as "(#Hdv & Hargs)".
            iDestruct "Hargs" as (??) "H".
            inversion H2.
        - setoid_rewrite interp_vis in H0'.
          rewrite /subevent in H0'; unfold_cat in H0'.
          rewrite /ReSum_sum /case_ /Case_sum1 /case_sum1 /resum in H0'.
          rewrite bind_vis in H0'.
          setoid_rewrite interp_state_vis in H0'.
          iExFalso. iClear "Hinner".
          destruct s0 as [ | [ | [ | [ | ] ] ] ]; cbn in H0';
            simp call_conv in H0'; cbn in H0'.
          all: try solve [rewrite bind_tau in H0'; by apply eqit_inv in H0'].
          destruct s0.
          all: try solve [rewrite bind_tau in H0'; by apply eqit_inv in H0']. }

      { (* External call *)
        to_eq in H; rewrite H in H0'; to_eq in H0; rewrite H0 in H1'.
        pose proof (H0'' := H0').
        apply interp_L2_conv_vis_ECall_noncall in H0'.
        destruct H0' as (?&?&?&?&?&?&?&?).
        cbn in *.
        subst.
        cbn in H0''. setoid_rewrite interp_vis in H0''.
        rewrite /resum in H0''. unfold_cat in H0''.
        simp L0'_conv in H0''. rewrite bind_vis in H0''.
        setoid_rewrite interp_state_vis in H0''.
        rewrite {1} /handle_L0_L2 in H0''.
        cbn in H0''. rewrite /handle_stateEff in H0''.
        rewrite bind_vis in H0''.
        repeat setoid_rewrite bind_ret_l in H0''.
        setoid_rewrite interp_state_tau in H0''.

        apply eqit_inv in H0''. cbn in H0''. destruct H0'' as (?&?&?).
        dependent destruction x. clear x.
        destruct H. red in H0. rewrite /handle_event. cbn -[interp_L2].

        pose proof (H1'' := H1').
        apply interp_L2_conv_vis_ECall_noncall in H1'.
        destruct H1' as (?&?&?&?&?&?&?&?).
        cbn in H, H1.
        subst.
        cbn in H1''. setoid_rewrite interp_vis in H1''.
        rewrite /resum in H1''. unfold_cat in H1''.
        simp L1'_conv in H1''. rewrite bind_vis in H1''.
        setoid_rewrite interp_state_vis in H1''.
        rewrite {1} /handle_L0_L2 in H1''.
        cbn in H1''. rewrite /handle_stateEff in H1''.
        rewrite bind_vis in H1''.
        apply eqit_inv in H1''. cbn in H1''. destruct H1'' as (?&?&?).
        dependent destruction x2. red in H. red in H3. subst; cbn -[interp_L2].
        rewrite /resum. unfold_cat.
        rewrite /resum /inl_ /Inl_sum1.

        rewrite !interp_mrec_external_call.
        provide_case: VIS_STEP. rewrite /subevent /resum /ReSum_inl /cat; unfold_cat.
        rewrite /inl_ /Inl_sum1.
        rewrite /handle_event. rewrite /Id_IFun.

        simp handle_call_events.
        iDestruct "Hinner" as "[ Hinner |  Hinner ]".
        { iDestruct "Hinner" as (?) "(SI & Hargs & Hk)".
          iLeft. iFrame.
          rewrite /call_args_eq.
          iDestruct "Hargs" as "(Hargs & %Hargs)".
          inversion Hargs; subst; iFrame.
          iExists _; iFrame.
          iSplitL ""; first (iPureIntro; eauto).
          iIntros (??) "H".
          iSpecialize ("Hk" with "H").
          iMod "Hk". rewrite -!interp_mrec_tau. iLeft.
          iExists f, _, _, g, _, _; iFrame.
          repeat (iSplitL ""; first done).
          rewrite !interp_L2_conv_tau.
          specialize (H0 (v_t.1, call_returns (ExternalCall x2 x6 x7 x10) v_t.2)).
          to_eq in H0; rewrite -H0.
          specialize (H3 (v_s.1, call_returns (ExternalCall x2 x6 x7 x10) v_s.2)).
          repeat rewrite bind_ret_l in H3.
          rewrite interp_state_tau in H3. to_eq in H3. rewrite -H3. done. }

        { iDestruct "Hinner" as (?) "(SI & Hargs & Hk)".
          iRight. iFrame.
          rewrite /call_ev.
          cbn -[state_interp].
          destruct C as (?&?).
          simp vir_call_ev.
          iDestruct "Hargs" as "(#Hdv & Hargs)".
          iDestruct "Hargs" as (??) "(#Hv & HC & #HWF & Hst & Hss)".
          subst; iFrame.
          iExists (l, l0).
          iSplitL "Hst Hss HC".
          { simp vir_call_ev. iFrame. inversion H4; subst; eauto. }

          iIntros (??) "H".
          iDestruct "H" as "(SI & H)".
          iPoseProof (vir_call_ans_attr with "H") as "H".
          iCombine "SI H" as "H".
          change (TauF ?x) with (observe (Tau x)).

          iSpecialize ("Hk" with "H").
          iMod "Hk". rewrite -!interp_mrec_tau. iLeft.
          iExists f, _, _, g, _, _; iFrame.
          repeat (iSplitL ""; first done).
          rewrite !interp_L2_conv_tau.
          specialize (H0 v_t).
          to_eq in H0; rewrite -H0.
          specialize (H3 v_s).
          repeat rewrite bind_ret_l in H3.
          rewrite interp_state_tau in H3. to_eq in H3. rewrite -H3. done. } } }

    { (* [UB] case *)
      inversion Heq.
      symmetry in H0; apply simpobs in H0.
      by eapply interp_L2_conv_UB_inv in H0. }

    { (* [EXC] case *)
      inversion Heq.
      symmetry in H0; apply simpobs in H0.
      by eapply interp_L2_conv_failure_inv in H0. }
  Qed.

  Definition inv i_t i_s :=
    (frame_WF i_t i_s ∗ checkout ∅ ∗ stack_tgt i_t ∗ stack_src i_s)%I.

  Theorem Proper_interp_mrec' {R}
    (f g : ∀ T : Type, LLVMEvents.CallE T → L0'expr T) a1 a2
    (Ψ : R -d> R -d> iPropI Σ) i_t i_s :
    inv i_t i_s -∗
    context_rel f g -∗
    <pers>
      (inv i_t i_s -∗ ⟅ a1 ⟆ ⪯ ⟅ a2 ⟆ [[ (fun x y => Ψ x y ∗ inv i_t i_s) ⤉ ]]) -∗
    interp_mrec f a1 ⪯ interp_mrec g a2
    [[ (fun x y => Ψ x y ∗ inv i_t i_s) ⤉ ]].
  Proof.
    iIntros "Hinv Hrel #Hr".
    iSpecialize ("Hr" with "Hinv").
    iApply (Proper_interp_mrec with "Hrel Hr").
  Qed.

  From Vellvm Require Import Utils.Util.

  Lemma sim_pick_unique_args args1 args2:
    ⊢ ([∗ list] x;y ∈ args1;args2, uval_rel x y) -∗
    ⟅ map_monad (λ uv : uvalue, pickUnique uv) args1 ⟆ ⪯
    ⟅ map_monad (λ uv : uvalue, pickUnique uv) args2 ⟆
    [[ (fun r1 r2 =>
          ([∗ list] d; u ∈ r1; args1, ⌜determine_uvalue u d⌝) ∗
          ([∗ list] d; u ∈ r2; args2, ⌜determine_uvalue u d⌝)) ⤉ ]].
  Proof.
    iIntros "#Hl".
    iInduction args2 as [ | ] "IH" forall (args1).
    { iDestruct (big_sepL2_nil_inv_r with "Hl") as %Hargs1; subst; cbn.
      setoid_rewrite interp_ret. iApply sim_expr'_base.
      iExists _, _; repeat (iSplitL ""; first done); done. }

    { iDestruct (big_sepL2_cons_inv_r with "Hl") as (???) "(Ha & Hl')";
        subst; cbn.
      setoid_rewrite interp_bind.
      rewrite {3 5} /pickUnique.

      iApply sim_expr'_bind.
      iPoseProof (L0_conv_concretize_or_pick_strong with "Ha") as "H".
      iApply sim_expr'_bupd_mono; cycle 1.
      { iApply sim_expr_lift; rewrite /instr_conv; iApply "H". }
      iIntros (??) "H'".
      iDestruct "H'" as (????) "(Hd & %Ht & %Hs)".
      rewrite H H0; rewrite !bind_ret_l; clear H H0.
      rewrite !interp_bind.

      iApply sim_expr'_bind; iModIntro.
      iApply sim_expr'_bupd_mono; [ | iApply ("IH" with "Hl'")].

      clear e_t0 e_s0. iClear "H".
      iIntros (??); iIntros "H".
      iDestruct "H" as (????) "(H1 & H2)".
      rewrite H H0 !bind_ret_l !interp_ret.
      iApply sim_expr'_base. iModIntro; iExists _, _.
      do 2 (iSplitL ""; first done); cbn; iFrame.
      iSplitL ""; done. }
  Qed.

  Lemma determine_uvalue_uval_rel uv1 dv1 uv2 dv2:
    determine_uvalue uv1 dv1 ->
    determine_uvalue uv2 dv2 ->
    uval_rel uv1 uv2 -∗
    uval_rel (dv1 ̂) (dv2 ̂).
  Proof.
    rewrite /determine_uvalue.
    iIntros (Hd1 Hd2) "#Hr".
    destruct (is_concrete uv1) eqn: Hv1.
    { apply uvalue_to_dvalue_inv in Hd1; subst.
      destruct (is_concrete uv2) eqn: Hv2.
      { by apply uvalue_to_dvalue_inv in Hd2; subst. }
      { iSpecialize ("Hr" $! _ Hd2).
        iDestruct "Hr" as (??) "Hr".
        iIntros (??).
        rewrite !concretize_uvalue_dvalue_to_uvalue in H, H0.
        inversion H; inversion H0; subst.
        rewrite concretize_uvalue_dvalue_to_uvalue.
        iExists _; iSplitL ""; done. } }
    { destruct (is_concrete uv2) eqn: Hv2.
      { apply uvalue_to_dvalue_inv in Hd2; subst.
        iIntros (??).
        rewrite !concretize_uvalue_dvalue_to_uvalue in H;
          inversion H; subst.
        rewrite /uval_rel.
        rewrite !concretize_uvalue_dvalue_to_uvalue.
        iSpecialize ("Hr" $! _ eq_refl).
        iDestruct "Hr" as (??) "Hv".
        iExists _; iSplitL ""; first done.
        clear H Hv2. rewrite Hd1 in H0; inversion H0; by subst. }
      { iSpecialize ("Hr" $! _ Hd2).
        iDestruct "Hr" as (??) "Hr".
        iIntros (??).
        rewrite !concretize_uvalue_dvalue_to_uvalue in H, H0.
        inversion H; inversion H0; subst.
        rewrite concretize_uvalue_dvalue_to_uvalue.
        iExists _; iSplitL ""; first done. clear H2.
        rewrite Hd1 in H; inversion H; by subst. } }
  Qed.

  Lemma uval_rel_determine_uvalue_dvalue_to_uvalue args_t args_s v_t v_s :
    ([∗ list] x;y ∈ args_t;args_s, uval_rel x y) -∗
    ([∗ list] d;u ∈ v_t;args_t, ⌜determine_uvalue u d⌝) -∗
    ([∗ list] d;u ∈ v_s;args_s, ⌜determine_uvalue u d⌝) -∗
    ([∗ list] x;y ∈ map dvalue_to_uvalue v_t;map dvalue_to_uvalue v_s,
       uval_rel x y).
  Proof.
    iIntros "#HR".
    iInduction args_t as [ | ] "IH" forall (args_s v_t v_s).
    { iIntros "#H_t #H_s".
      iDestruct (big_sepL2_nil_inv_l with "HR") as %Hr; subst.
      iDestruct (big_sepL2_nil_inv_r with "H_t") as %Hr; subst.
      iDestruct (big_sepL2_nil_inv_r with "H_s") as %Hr; subst.
      done. }
    { iDestruct (big_sepL2_cons_inv_l with "HR") as (???) "(Hr & Hl)".
      iIntros "#H_t #H_s".
      iDestruct (big_sepL2_cons_inv_r with "H_t") as (????) "H_t'"; subst.
      iDestruct (big_sepL2_cons_inv_r with "H_s") as (????) "H_s'"; subst.
      cbn.
      iPoseProof (determine_uvalue_uval_rel _ _ _ _ H1 H0 with "Hr") as "Hd".
      iSplitL ""; first done.
      by iSpecialize ("IH" with "Hl H_t' H_s'"). }
  Qed.

  Lemma sim_external_call dτ addr_t addr_s args_t args_s l i_t i_s:
    frame_WF i_t i_s -∗
    stack_tgt i_t -∗
    stack_src i_s -∗
    checkout ∅ -∗
    dval_rel addr_t addr_s -∗
    ([∗ list] x;y ∈ args_t;args_s, uval_rel x y) -∗
    ⟅ dargs <- map_monad (λ uv : uvalue, pickUnique uv) args_t;;
      trigger (ExternalCall dτ addr_t (map dvalue_to_uvalue dargs) l) ⟆
    ⪯
    ⟅ dargs <- map_monad (λ uv : uvalue, pickUnique uv) args_s;;
      trigger (ExternalCall dτ addr_s (map dvalue_to_uvalue dargs) l) ⟆
    [[ (fun x y =>
          uval_rel x y ∗ stack_tgt i_t ∗ stack_src i_s ∗
          checkout ∅) ⤉ ]].
  Proof.
    iIntros "#WF Hs_t Hs_s HC #Haddr #Hargs".
    setoid_rewrite interp_bind.
    iApply sim_expr'_bind.
    iApply (sim_expr'_bupd_mono with "[Hs_t Hs_s HC]");
      last iApply (sim_pick_unique_args with "Hargs").
    iIntros (??) "H".
    iDestruct "H" as (????) "(#H_t & #H_s)".
    rewrite H H0 !bind_ret_l; clear H H0.
    rewrite !interp_vis; cbn.
    setoid_rewrite interp_ret; cbn.
    rewrite /subevent; unfold_cat; simp L0'_conv.
    rewrite !bind_vis.
    setoid_rewrite bind_ret_l.

    iModIntro. simp call_conv.
    iIntros (??) "SI"; iModIntro.
    setoid_rewrite interp_state_vis; cbn -[state_interp].
    rewrite /handle_stateEff !bind_vis.
    rewrite /sim_coind' sim_coindF_unfold sim_indF_unfold.

    provide_case: VIS_STEP.
    rewrite /handle_event; cbn -[state_interp]; unfold_cat.
    simp handle_call_events; cbn -[state_interp]. iFrame.
    iLeft; iExists (i_t, i_s).
    Transparent arg_val_rel.
    rewrite /call_args_eq; rewrite /arg_val_rel; cbn. iFrame. iSplitL "Haddr".
    { rewrite /call_args_eq; cbn; iFrame.
      iSplitL ""; last done.
      rewrite /arg_val_rel; cbn.
      iFrame "WF".

      iSplitL ""; first done.
      iApply (uval_rel_determine_uvalue_dvalue_to_uvalue with
                "Hargs H_t H_s"). }

    iIntros (??) "(SI & UV)".
    iApply sim_coindF_tau; cbn -[state_interp].
    iApply sim_coindF_tau; cbn -[state_interp].
    iApply sim_coindF_base.
    iExists _, _, (Ret _), (Ret _); iFrame.
    iSplitL "".
    { iPureIntro.
      change (RetF (E := language.L2 vir_lang) ?x) with
        (observe (E := language.L2 vir_lang) (Ret x)).
      f_equiv. constructor. f_equiv. to_eq;
        by setoid_rewrite interp_state_ret. }
    iSplitL "".
    { iPureIntro.
      change (RetF (E := language.L2 vir_lang) ?x) with
        (observe (E := language.L2 vir_lang) (Ret x)).
      f_equiv. constructor. f_equiv. to_eq;
        by setoid_rewrite interp_state_ret. }

    iExists _, _. iDestruct "UV" as "(?&?&?&?)"; iFrame.
    by repeat (iSplitL ""; first done).
  Qed.

End CR.
