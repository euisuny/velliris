From Coq Require Import String List Program.Equality.
From iris.prelude Require Import options.
From iris.base_logic.lib Require Export gen_heap ghost_map.
From iris.base_logic Require Import gset_bij.

From ITree Require Import ITree Eq Interp.InterpFacts Interp.RecursionFacts.

From Vellvm Require Import Syntax.LLVMAst Syntax.DynamicTypes
  Semantics.InterpretationStack Handlers Utils.Util Semantics.LLVMEvents.

From Equations Require Import Equations.

From Paco Require Import paco.

From simuliris.logic Require Import satisfiable.
From simuliris.simulation Require Import slsls simulation sim_properties
  wellformedness contextual.
From simuliris.vir Require Import
  vir spec globalbij heapbij logical_relations fundamental interp_properties.
From simuliris.utils Require Import no_event.

Set Default Proof Using "Type*".

Import StateFacts.
Import ListNotations.
Import SemNotations.
Import LLVMEvents.

Ltac to_inner G :=
  change
    (|==>
      ∃ c : sim_case,
        match c with
        | BASE => ?Φ ?x ?y
        | STUTTER_L => stutter_l
        | STUTTER_R => stutter_r
        | TAU_STEP => tau_step
        | VIS_STEP => vis_step ?x ?y
        | SOURCE_UB => source_ub
        | SOURCE_EXC => source_exc
        end)%I with
        (sim_expr_inner G (sim_indF G) Φ x y).

(* Mrec utils *)
Section euttge_utils.

  Lemma euttge_tauR_inv E R (e1 e2 : itree E R):
    e1 ≳ Tau e2 ->
    e1 ≳ e2.
  Proof.
    intros H. rewrite (itree_eta e2) in H.
    punfold H; pstep; red. red in H.
    remember (observe e1).
    remember (observe e2).
    clear Heqi Heqi0 e1 e2. cbn in H.
    remember ((TauF {| _observe := i0 |})).
    induction H; subst; try inversion Heqi1; eauto; pclearbot.
    - constructor; eauto.
      punfold REL. rewrite H0 in REL. done.
    - constructor; eauto.
    - inversion CHECK.
  Qed.

  Lemma euttge_tauR_inv' E R (e1 e2 : itree E R):
    e1 ≳ Tau e2 ->
    ∃ e1', observe e1 = TauF e1'.
  Proof.
    intros H. rewrite (itree_eta e2) in H.
    punfold H; red in H.
    remember (observe e1).
    remember (observe e2).
    clear Heqi Heqi0 e1 e2. cbn in H.
    remember ((TauF {| _observe := i0 |})).
    induction H; subst; try inversion Heqi1; eauto; pclearbot.
    inversion CHECK.
  Qed.

End euttge_utils.

(** *Top-level Contextual Refinement *)
Section CR.

  Context {Σ} `{!sheapGS Σ, !checkedoutGS Σ, !heapbijGS Σ}.

  Definition globals_WF (g : vir.globals) : iPropI Σ :=
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
    (□ (∀ fn_t fn_s dt_t dt_s args_t args_s C,
          let call_t := ExternalCall dt_t fn_t args_t nil in
          let call_s := ExternalCall dt_s fn_s args_s nil in
          call_ev call_t call_s C -∗
          ⟅ f _ (Call dt_t fn_t args_t nil) ⟆ ⪯
          ⟅ g _ (Call dt_s fn_s args_s nil) ⟆
          [[ (fun v_t v_s => call_ans call_t v_t call_s v_s C) ⤉ ]]) )%I.

  (* Should follow by reflexivity theorem *)
  Definition context_rel_refl
      (f : ∀ T : Type, CallE T → L0'expr T)
      (g : ∀ T : Type, CallE T → L0'expr T) :=
    (□ (∀ fn_t fn_s dt attr args_t args_s C,
          arg_val_rel (fn_t, args_t) (fn_s, args_s) C -∗
          ⟅ f _ (Call dt fn_t args_t attr) ⟆ ⪯
          ⟅ g _ (Call dt fn_s args_s attr) ⟆
          [[ (fun x y => res_val_rel x y C) ⤉ ]]))%I.

  (* Well-formed property over function calls: the [Internal] and [External] tags
    can be ignored. *)
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
      (σ_t σ_s : global_env * (local_env * lstack) * memory_stack) :
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
      (σ_t σ_s : global_env * (local_env * lstack) * memory_stack)
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
      (σ_t σ_s : global_env * (local_env * lstack) * memory_stack)
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
      (σ_t σ_s : global_env * (local_env * lstack) * memory_stack)
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

  Lemma attribute_interp_external τ addr args attr τ' addr' args' attr' C:
    attribute_interp (ExternalCall τ addr args (FNATTR_External :: attr))
                    (ExternalCall τ' addr' args' (FNATTR_External :: attr')) C ->
    attribute_interp (ExternalCall τ addr args attr)
                    (ExternalCall τ' addr' args' attr') C.
  Proof.
    simp attribute_interp.
  Qed.

  Lemma vir_call_ans_attr τ addr args attr τ' addr' args' attr' v1 v2 C:
    vir_call_ans Σ (ExternalCall τ addr args attr) v1 (ExternalCall τ' addr' args' attr') v2 C -∗
    vir_call_ans Σ (ExternalCall τ addr args (FNATTR_External :: attr)) v1
                   (ExternalCall τ' addr' args' (FNATTR_External :: attr')) v2 C.
  Proof.
    destruct C as ((?&?)&?).
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
  Abort.

  Definition inv i_t i_s :=
    (frame_WF i_t i_s ∗ checkout ∅ ∗ stack_tgt i_t ∗ stack_src i_s)%I.

  (* Theorem Proper_interp_mrec' {R} *)
  (*   (f g : ∀ T : Type, LLVMEvents.CallE T → L0'expr T) a1 a2 *)
  (*   (Ψ : R -d> R -d> iPropI Σ) i_t i_s : *)
  (*   inv i_t i_s -∗ *)
  (*   (* FIXME: Needs to be connected to [a1] and [a2] (maybe also to [inv]?) *) *)
  (*   context_rel f g attr_t attr_s -∗ *)
  (*   <pers> *)
  (*     (inv i_t i_s -∗ ⟅ a1 ⟆ ⪯ ⟅ a2 ⟆ [[ (fun x y => Ψ x y ∗ inv i_t i_s) ⤉ ]]) -∗ *)
  (*   interp_mrec f a1 ⪯ interp_mrec g a2 *)
  (*   [[ (fun x y => Ψ x y ∗ inv i_t i_s) ⤉ ]]. *)
  (* Proof. *)
  (*   iIntros "Hinv Hrel #Hr". *)
  (*   iSpecialize ("Hr" with "Hinv"). *)
  (*   iApply (Proper_interp_mrec with "Hrel Hr"). *)
  (* Qed. *)

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
    iLeft; iExists (∅, i_t, i_s).
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

  Lemma determine_uvalue_dvalue_to_uvalue dτ addr_t addr_s dvs_t dvs_s uvs_t uvs_s  C attrs:
    ⊢ (([∗ list] d;u ∈ dvs_t;uvs_t, ⌜determine_uvalue u d⌝) -∗
       ([∗ list] d;u ∈ dvs_s;uvs_s, ⌜determine_uvalue u d⌝) -∗
       ([∗ list] x; y ∈ uvs_t; uvs_s, uval_rel x y) -∗
       ⌜attribute_interp (ExternalCall dτ addr_t uvs_t attrs) (ExternalCall dτ addr_s uvs_s attrs) C⌝ -∗
       ⌜attribute_interp
        (ExternalCall dτ addr_t (map dvalue_to_uvalue dvs_t) attrs)
        (ExternalCall dτ addr_s (map dvalue_to_uvalue dvs_s) attrs) C⌝) : iProp Σ.
  Proof.
    iInduction uvs_t as [ | ] "IH" forall (dvs_t dvs_s uvs_s).
    { iIntros "#Ht #Hs #Hrel".
      iDestruct (big_sepL2_nil_inv_r with "Ht") as %Ht ; subst.
      iDestruct (big_sepL2_nil_inv_l with "Hrel") as %Hrel; subst.
      iDestruct (big_sepL2_nil_inv_r with "Hs") as %Hs; by subst. }

    { iIntros "#Ht #Hs #Hrel #Hattr".
      iDestruct (big_sepL2_cons_inv_r with "Ht") as (????) "Ht'"; subst.
      iDestruct (big_sepL2_cons_inv_l with "Hrel") as (???) "[#Hr' Hrel']"; subst.
      iDestruct (big_sepL2_cons_inv_r with "Hs") as (????) "Hs'"; subst.
      iSpecialize ("IH" with "Ht' Hs' Hrel'").
  Admitted.

  Lemma sim_external_call' dτ addr_t addr_s args_t args_s i_t i_s C (attrs : list fn_attr):
    attribute_interp (ExternalCall dτ addr_t args_t attrs) (ExternalCall dτ addr_s args_s attrs) C ->
    frame_WF i_t i_s -∗
    stack_tgt i_t -∗
    stack_src i_s -∗
    checkout C -∗
    dval_rel addr_t addr_s -∗
    ([∗ list] x;y ∈ args_t;args_s, uval_rel x y) -∗
    ⟅ dargs <- map_monad (λ uv : uvalue, pickUnique uv) args_t;;
      trigger (ExternalCall dτ addr_t (map dvalue_to_uvalue dargs) (remove_tag attrs)) ⟆
    ⪯
    ⟅ dargs <- map_monad (λ uv : uvalue, pickUnique uv) args_s;;
      trigger (ExternalCall dτ addr_s (map dvalue_to_uvalue dargs) (remove_tag attrs)) ⟆
    [[ (fun x y =>
          uval_rel x y ∗ stack_tgt i_t ∗ stack_src i_s ∗
          checkout C) ⤉ ]].
  Proof.
    iIntros (Hattrs) "#WF Hs_t Hs_s HC #Haddr #Hargs".
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
    iRight; iExists (C, i_t, i_s).
    Transparent arg_val_rel.
    simp vir_call_ev; iFrame. iFrame "Haddr WF".
    rewrite /arg_val_rel; cbn. iSplitL "".
    { repeat (iSplitL ""; first (iPureIntro; done)).
      iSplitL ""; first
      iApply (uval_rel_determine_uvalue_dvalue_to_uvalue with
                "Hargs H_t H_s").
      cbn.
      admit. }

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

    iExists _, _.
    simp vir_call_ans.
    iDestruct "UV" as "(?&?&?&?)"; iFrame.
    by repeat (iSplitL ""; first done).
    Admitted.


End CR.

Section CR_definition.

  Context (Σ : gFunctors).
  Context (I : vir_state -> vir_state -> Prop).
  Context (ret_typ : dtyp) (main : Addr.addr)
          (args : list uvalue)
          (main_function : definition dtyp (CFG.cfg dtyp))
          (glo_t glo_s : vir.globals).

  Import CFG.

  Definition hole (C : CFG.mcfg dtyp) (e : declaration dtyp * definition dtyp (CFG.cfg dtyp)) :=
    {| m_name := m_name C;
      m_target := m_target C;
      m_datalayout := m_datalayout C;
      m_type_defs := m_type_defs C;
      m_globals := m_globals C;
      m_declarations := e.1 :: m_declarations C;
      m_definitions := e.2 :: m_definitions C
    |}.
  Opaque hole.

  Definition context (C : CFG.mcfg dtyp) e :=
      Monad.bind (mcfg_definitions (hole C e))
        (fun defs => denote_mcfg defs ret_typ (DVALUE_Addr main) args).

  Notation " C ⎨ e_t ⎬ " := (context C e_t) (at level 40).

  Definition attributes (C : CFG.mcfg dtyp) := dc_attrs <$> CFG.m_declarations C.

  Definition contextual_refinement e_t e_s: Prop :=
    forall (C : CFG.mcfg dtyp) σ_t σ_s,
      I σ_t σ_s ->
      dc_name (df_prototype e_t.2) = dc_name (df_prototype e_s.2) ->
      CFG_WF (hole C e_t) glo_t glo_s ->
      CFG_WF (hole C e_s) glo_t glo_s ->
      well_formed (⟦ C ⎨ e_t ⎬ ⟧ σ_t) (⟦ C ⎨ e_s ⎬ ⟧ σ_s) ->
      eutt obs_val_res (⟦ C ⎨ e_t ⎬ ⟧ σ_t) (⟦ C ⎨ e_s ⎬ ⟧ σ_s).

End CR_definition.

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

(* Initial relation on states *)
Definition I (main : addr) glo_t glo_s : vir_state -> vir_state -> Prop :=
  fun '(g_t, (l_t, ls_t), (m_t, f_t)) '(g_s, (l_s, ls_s), (m_s, f_s)) =>
  main.1 <> Addr.null.1 /\
  g_t = glo_t /\ g_s = glo_s
  /\ l_t = nil /\ l_s = nil
  /\ ls_t = nil /\ ls_s = nil
  /\ m_t = ({[ main.1 := dvalue_to_block DVALUE_None;
              Addr.null.1 := dvalue_to_block DVALUE_None ]},
            {[ main.1; Addr.null.1 ]})
  /\ m_s = ({[ main.1 := dvalue_to_block DVALUE_None;
              Addr.null.1 := dvalue_to_block DVALUE_None ]},
            {[ main.1; Addr.null.1 ]})
  /\ f_t = Mem.Singleton [ main.1; Addr.null.1 ]
  /\ f_s = Mem.Singleton [ main.1; Addr.null.1 ].

(* Utility functions *)
Lemma address_one_function_leaf a x0 x:
  Leaf.Leaf x0 (address_one_function a) ->
  Leaf.Leaf x (address_one_function a) ->
  x0.2 = x.2.
Proof.
  rewrite /address_one_function.
  intros.
  apply Leaf.Leaf_bind_inv in H0.
  destruct H0 as (?&?&?).
  apply Leaf.Leaf_bind_inv in H.
  destruct H as (?&?&?).
  apply Leaf.Leaf_Ret_inv in H2, H1; subst. done.
Qed.

Lemma mcfg_definitions_leaf C g g_t' g_s' r_t r_s:
  Leaf.Leaf (g_t', r_t) (interp_global (mcfg_definitions C) g) ->
  Leaf.Leaf (g_s', r_s) (interp_global (mcfg_definitions C) g) ->
  r_t = r_s.
Proof.
  destruct C; cbn in *.
  revert r_t r_s g g_t' g_s'.
  induction m_definitions.
  { cbn in *.
    intros.
    inversion H; inv H1; eauto.
    inversion H0; inv H1; eauto. }
  { intros * Ht Hs. cbn in *.
    rewrite interp_global_bind in Ht, Hs.
    apply Leaf.Leaf_bind_inv in Ht, Hs.
    destruct Ht as ((g_t&p_t)&bleaf_t&Ht).
    destruct Hs as ((g_s&p_s)&bleaf_s&Hs).
    unfold address_one_function in *.
    rewrite interp_global_bind interp_global_trigger in bleaf_t, bleaf_s.
    cbn in *.
    destruct (g !! dc_name (df_prototype a)) eqn: G_lookup; try rewrite G_lookup in bleaf_t, bleaf_s.
    { rewrite bind_ret_l interp_global_ret in bleaf_t, bleaf_s.
      apply Leaf.Leaf_Ret_inv in bleaf_t, bleaf_s.
      destruct p_t, p_s.
      inv bleaf_t. inv bleaf_s.
      rewrite interp_global_bind in Ht, Hs.
      apply Leaf.Leaf_bind_inv in Ht, Hs.
      destruct Ht as ((g_t&p_t)&bleaf_t&Ht).
      destruct Hs as ((g_s&p_s)&bleaf_s&Hs).
      do 2 rewrite interp_global_ret in Ht, Hs.
      apply Leaf.Leaf_Ret_inv in Ht, Hs; inv Ht; inv Hs.
      f_equiv.

      eapply IHm_definitions; eauto. }

    { rewrite bind_bind bind_vis in bleaf_t, bleaf_s.
      inv bleaf_t; inv H; done. } }
Qed.

Section CR.

  Context {Σ} `{!sheapGS Σ, !checkedoutGS Σ, !heapbijGS Σ}.

  Lemma CFG_WF_hole C decl e_t g_t g_s:
    CFG_WF (hole C (decl, e_t)) g_t g_s ->
    CFG_WF C g_t g_s.
  Proof.
    rewrite /CFG_WF.
    intros. destructb.
    apply nodup_codomain_cons_inv in H5,H6; eauto.
    cbn in *. split; eauto. nodup.
    apply contains_keys_cons_inv in H3, H4.
    apply Forall_cons in H1, H2.
    destructb.
    repeat split; eauto.
  Qed.

  Lemma CFG_WF_hole_attr C decl e_t g_t g_s:
    CFG_WF (hole C (decl, e_t)) g_t g_s ->
    (dc_attrs decl = nil).
  Proof.
    rewrite /CFG_WF.
    intros. destructb.
    clear -H2. cbn in *.
    apply Forall_cons in H2; by destructb.
  Qed.

End CR.

Lemma attribute_interp_no_attr dt_t fn_t args_t dt_s fn_s args_s C:
  attribute_interp
    (ExternalCall dt_t fn_t args_t [])
    (ExternalCall dt_s fn_s args_s []) C ->
  C = ∅.
Proof.
  simp attribute_interp.
  cbn; intros; destruct H as (c&?); destruct c; destructb; done.
Qed.

Lemma initialize_main `{sheapGpreS Σ} `{heapbijGpreS Σ} `{checkedoutGpreS Σ}
  main e_t e_s decl (g : vir.globals) C σ_t σ_s:
  I main g g σ_t σ_s ->
  (∀ γf γf0 (Hsh: sheapGS Σ) (Hhb : heapbijGS Σ) (Hc : checkedoutGS Σ),
     lb_rel (dvalue_to_block DVALUE_None) (dvalue_to_block DVALUE_None) -∗
    (Addr.null.1, 0%Z) ↔h (Addr.null.1, 0%Z) -∗
    (main.1, 0%Z) ↔h (main.1, 0%Z) -∗
    (* own (globals_name sheapG_heap_target) (to_agree g) -∗ *)
    (* own (globals_name sheapG_heap_source) (to_agree g) -∗ *)
    checkout ∅ -∗
    ghost_var (stack_name sheapG_heap_target) (1 / 2) [γf] -∗
    ghost_var (stack_name sheapG_heap_source) (1 / 2) [γf0] -∗
      context DTYPE_Void main [] C (decl, e_t)
      ⪯
      context DTYPE_Void main [] C (decl, e_s)
      [[ (λ x y : uvalue, ⌜obs_val x y⌝) ⤉ ]]) ==∗
    ∃ (H2 : sheapGS Σ) (H3 : heapbijGS Σ) (H4 : checkedoutGS Σ), state_interp σ_t σ_s ∗
      context DTYPE_Void main [] C (decl, e_t)
      ⪯
      context DTYPE_Void main [] C (decl, e_s)
      [[ (λ x y : uvalue, ⌜obs_val x y⌝) ⤉ ]].
Proof.
  iIntros (HI) "HP".

  iMod (@sheap_init Σ _ g g) as (Hsh) "(Hh_t & Hh_s & H)".
  iMod (@heapbij_init Σ _ _ ∅) as (Hhb) "Hbij".
  iMod (@checkedout_init Σ _ ∅) as (Hc) "[Hc1 Hc2]".

  rewrite /state_interp.

  iDestruct "H" as "(Hh_tf & Hb_t & Hg_t & Hh_sf & Hb_s & Hg_s & H)".

  iDestruct "H" as "(Ht & Hs)".
  iDestruct "Ht" as (?) "(Hst_t & Hl_t & Hld_t & Ha_t)".
  iDestruct "Hs" as (?) "(Hst_s & Hl_s & Hld_s & Ha_s)".

  (* Allocate null bij *)
  destruct σ_t as ((?&?&?)&(?&?)&?).
  destruct σ_s as ((?&?&?)&(?&?)&?).

  Opaque context.
  destruct HI as (Hun & ?&?&?&?&?&?&?&?&?&?); subst.
  inv H8; inv H9.

  (** *Allocate null address *)
  (* Allocate at [Addr.null] on target side *)
  iCombine ("Ha_t Hst_t Hh_t") as "H".
  iPoseProof
    (heap_ctx_alloc _ Addr.null.1
       DVALUE_None ((∅, ∅), ∅) [γf] _ _ _ _ _ DTYPE_Void) as "Halloc_t";
    [ set_solver | cbn; set_solver | constructor | ].
  rewrite allocaS_eq /allocaS_def. rewrite /stack.
  iSpecialize ("Halloc_t" with "H"). iMod "Halloc_t".

  (* Allocate at [Addr.null] on source side *)
  iCombine ("Ha_s Hst_s Hh_s") as "H".
  iPoseProof
    (heap_ctx_alloc _ Addr.null.1
       DVALUE_None ((∅, ∅), ∅) [γf0] _ _ _ _ _ DTYPE_Void) as "Halloc_s";
    [ set_solver | cbn; set_solver | constructor | ].
  rewrite allocaS_eq /allocaS_def. rewrite /stack.
  iSpecialize ("Halloc_s" with "H"). iMod "Halloc_s".

  iDestruct "Halloc_t" as "(Hh_t & %Hin_t & Ha_t & Hst_t & Hv_t & hb_t)".
  iDestruct "Halloc_s" as "(Hh_s & %Hin_s & Ha_s & Hst_s & Hv_s & hb_s)".

  (* Extend global bij *)
  rewrite !mapsto_dval_eq /mapsto_dval_def.
  iAssert (lb_rel (dvalue_to_block DVALUE_None) (dvalue_to_block DVALUE_None))%I as "Hb".
  { rewrite /lb_rel. cbn.
    rewrite /mem_byte_rel. rewrite /init_block; cbn.
    simpl. iSplit.
    { iIntros (???). inversion H2. }
    { done. } }
  iDestruct (heapbij_insert with "Hbij Hv_t Hv_s Hb hb_t hb_s") as ">(Hbij & #Haddr_null)".

  (** *Allocate main address *)
  (* Allocate at [Addr.main] on target side *)
  iCombine ("Ha_t Hst_t Hh_t") as "H".
  iPoseProof
    (heap_ctx_alloc _ main.1
       DVALUE_None (({[Addr.null.1:=dvalue_to_block DVALUE_None]}, {[Addr.null.1]})
         , Mem.Singleton [Addr.null.1]) [γf] _ _ _ _ _ DTYPE_Void) as "Halloc_t".
  { cbn; rewrite lookup_singleton_ne; auto. }
  { cbn; set_solver. }
  { constructor. }

  rewrite allocaS_eq /allocaS_def. rewrite /stack.
  cbn. rewrite !insert_empty !union_empty_r_L.
  iSpecialize ("Halloc_t" with "H"). iMod "Halloc_t".

  (* Allocate at [Addr.main] on source side *)
  iCombine ("Ha_s Hst_s Hh_s") as "H".
  iPoseProof
    (heap_ctx_alloc _ main.1
       DVALUE_None (({[Addr.null.1:=dvalue_to_block DVALUE_None]}, {[Addr.null.1]})
         , Mem.Singleton [Addr.null.1]) [γf0] _ _ _ _ _ DTYPE_Void) as "Halloc_s".
  { cbn; rewrite lookup_singleton_ne; auto. }
  { cbn; set_solver. }
  { constructor. }

  rewrite allocaS_eq /allocaS_def. rewrite /stack.
  iSpecialize ("Halloc_s" with "H"). iMod "Halloc_s".

  iDestruct "Halloc_t" as "(Hh_t & %Hin_t' & Ha_t & Hs_t & Hv_t & hb_t)".
  iDestruct "Halloc_s" as "(Hh_s & %Hin_s' & Ha_s & Hs_s & Hv_s & hb_s)".

  (* Extend global bij *)
  rewrite !mapsto_dval_eq /mapsto_dval_def.
  iDestruct (heapbij_insert with "Hbij Hv_t Hv_s Hb hb_t hb_s") as ">(H & #Haddr_main)".
  iDestruct "Hg_t" as "#Hg_t"; iDestruct "Hg_s" as "#Hg_s".

  iModIntro.
  iExists Hsh, Hhb, Hc. cbn.

  iSplitL "Hh_t Hh_s Hc2 H".
  (* iSplitR "Hc1 HP Hs_t Hs_s". *)
  { iExists ∅, {[(main.1, main.1); (Addr.null.1, Addr.null.1)]}, g; iFrame.

    (* Global init *)
    rewrite /globalbij_interp; cbn.
    rewrite !globals_eq /globals_def; cbn. iFrame.
    iDestruct "Haddr_null" as "(Haddr' & %H')".
    iSplitL ""; first set_solver.
    iSplitL ""; first (iSplitL ""; done).
    iSplitL ""; first set_solver.
    iFrame "Hg_t Hg_s". admit. }
Abort.

(** *Top-level soundness theorem *)
Theorem soundness `{sheapGpreS Σ} `{heapbijGpreS Σ} `{checkedoutGpreS Σ}
  e_t e_s main decl g:
  isat (∀ `(sheapGS Σ, checkedoutGS Σ, heapbijGS Σ),
    globals_WF g ∗ <pers> fun_logrel e_t e_s ∅) ->
  contextual_refinement (I main g g) DTYPE_Void main [] g g
      (decl, e_t) (decl, e_s).
Proof.
  intros Hf C ?? HI WF_name WF_cfg1 WF_cfg2 WF.
  eapply (@adequacy Σ isat); eauto; try typeclasses eauto.

  eapply sat_mono, Hf. clear Hf.
  iStartProof. iIntros "#Hf".

  iMod (@sheap_init Σ _ g g) as (Hsh) "(Hh_t & Hh_s & H)".
  iMod (@heapbij_init Σ _ _ ∅) as (Hhb) "Hbij".
  iMod (@checkedout_init Σ _ ∅) as (Hc) "[Hc1 Hc2]".

  rewrite /state_interp.

  iDestruct "H" as "(Hh_tf & Hb_t & Hg_t & Hh_sf & Hb_s & Hg_s & H)".

  iDestruct "H" as "(Ht & Hs)".
  iDestruct "Ht" as (?) "(Hst_t & Hl_t & Hld_t & Ha_t)".
  iDestruct "Hs" as (?) "(Hst_s & Hl_s & Hld_s & Ha_s)".

  (* Allocate null bij *)
  destruct σ_t as ((?&?&?)&(?&?)&?).
  destruct σ_s as ((?&?&?)&(?&?)&?).

  Opaque context.
  destruct HI as (Hun & ?&?&?&?&?&?&?&?&?&?); subst.
  inv H8; inv H9.

  (** *Allocate null address *)
  (* Allocate at [Addr.null] on target side *)
  iCombine ("Ha_t Hst_t Hh_t") as "H".
  iPoseProof
    (heap_ctx_alloc _ Addr.null.1
       DVALUE_None ((∅, ∅), ∅) [γf] _ _ _ _ _ DTYPE_Void) as "Halloc_t";
    [ set_solver | cbn; set_solver | constructor | ].
  rewrite allocaS_eq /allocaS_def. rewrite /stack.
  iSpecialize ("Halloc_t" with "H"). iMod "Halloc_t".

  (* Allocate at [Addr.null] on source side *)
  iCombine ("Ha_s Hst_s Hh_s") as "H".
  iPoseProof
    (heap_ctx_alloc _ Addr.null.1
       DVALUE_None ((∅, ∅), ∅) [γf0] _ _ _ _ _ DTYPE_Void) as "Halloc_s";
    [ set_solver | cbn; set_solver | constructor | ].
  rewrite allocaS_eq /allocaS_def. rewrite /stack.
  iSpecialize ("Halloc_s" with "H"). iMod "Halloc_s".

  iDestruct "Halloc_t" as "(Hh_t & %Hin_t & Ha_t & Hst_t & Hv_t & hb_t)".
  iDestruct "Halloc_s" as "(Hh_s & %Hin_s & Ha_s & Hst_s & Hv_s & hb_s)".

  (* Extend global bij *)
  rewrite !mapsto_dval_eq /mapsto_dval_def.
  iAssert (lb_rel (dvalue_to_block DVALUE_None) (dvalue_to_block DVALUE_None))%I as "Hb".
  { rewrite /lb_rel. cbn.
    rewrite /mem_byte_rel. rewrite /init_block; cbn.
    simpl. iSplit.
    { iIntros (???). inversion H2. }
    { done. } }
  iDestruct (heapbij_insert with "Hbij Hv_t Hv_s Hb hb_t hb_s") as ">(Hbij & #Haddr_null)".

  (** *Allocate main address *)
  (* Allocate at [Addr.main] on target side *)
  iCombine ("Ha_t Hst_t Hh_t") as "H".
  iPoseProof
    (heap_ctx_alloc _ main.1
       DVALUE_None (({[Addr.null.1:=dvalue_to_block DVALUE_None]}, {[Addr.null.1]})
         , Mem.Singleton [Addr.null.1]) [γf] _ _ _ _ _ DTYPE_Void) as "Halloc_t".
  { cbn; rewrite lookup_singleton_ne; auto. }
  { cbn; set_solver. }
  { constructor. }

  rewrite allocaS_eq /allocaS_def. rewrite /stack.
  cbn. rewrite !insert_empty !union_empty_r_L.
  iSpecialize ("Halloc_t" with "H"). iMod "Halloc_t".

  (* Allocate at [Addr.main] on source side *)
  iCombine ("Ha_s Hst_s Hh_s") as "H".
  iPoseProof
    (heap_ctx_alloc _ main.1
       DVALUE_None (({[Addr.null.1:=dvalue_to_block DVALUE_None]}, {[Addr.null.1]})
         , Mem.Singleton [Addr.null.1]) [γf0] _ _ _ _ _ DTYPE_Void) as "Halloc_s".
  { cbn; rewrite lookup_singleton_ne; auto. }
  { cbn; set_solver. }
  { constructor. }

  rewrite allocaS_eq /allocaS_def. rewrite /stack.
  iSpecialize ("Halloc_s" with "H"). iMod "Halloc_s".

  iDestruct "Halloc_t" as "(Hh_t & %Hin_t' & Ha_t & Hs_t & Hv_t & hb_t)".
  iDestruct "Halloc_s" as "(Hh_s & %Hin_s' & Ha_s & Hs_s & Hv_s & hb_s)".

  (* Extend global bij *)
  rewrite !mapsto_dval_eq /mapsto_dval_def.
  iDestruct (heapbij_insert with "Hbij Hv_t Hv_s Hb hb_t hb_s") as ">(H & #Haddr_main)".
  iDestruct "Hg_t" as "#Hg_t"; iDestruct "Hg_s" as "#Hg_s".

  iModIntro.
  iExists Hsh, Hhb, Hc. cbn.

  iSplitR "Hc1 Hf Hs_t Hs_s".
  { iExists ∅, {[(main.1, main.1); (Addr.null.1, Addr.null.1)]}, g; iFrame.

    (* Global init *)
    rewrite /globalbij_interp; cbn.
    rewrite !globals_eq /globals_def; cbn. iFrame.
    iDestruct "Haddr_null" as "(Haddr' & %H')".
    iSplitL ""; first set_solver.
    iSplitL ""; first (iSplitL ""; done).
    iSplitL ""; first set_solver.
    iFrame "Hg_t Hg_s".
    iSpecialize ("Hf" $! _ _ _). iDestruct "Hf" as "(Hf & H)".
    done. }

  (* Initialize state interpretation and resources *)
  Transparent context. cbn.
  rewrite !bind_bind. setoid_rewrite bind_ret_l.
  iApply sim_expr'_bind.
  cbn in WF_name; subst. rewrite WF_name.
  iApply (sim_expr'_bupd_mono with "[Hc1 Hs_t Hs_s]");
    [ | iApply sim_expr_lift; iApply sim_global_read ]; cycle 1.
  { iIntros (??) "H'". iApply "H'". }
  iIntros (??) "(%dv & %dv' & %Hr1 & %Hr2 & #Hdv)".
  rewrite Hr1 Hr2 !bind_ret_l; clear Hr1 Hr2.
  rewrite !bind_bind; setoid_rewrite bind_ret_l.
  iApply sim_expr'_bind.

  iApply (sim_expr'_bupd_mono with "[Hc1 Hf Hs_t Hs_s]");
    [ | iApply mcfg_definitions_refl' ]; eauto.
  3, 4: by rewrite globals_eq /globals_def.
  2 : by eapply CFG_WF_hole.

  iIntros (??) "H".
  iDestruct "H" as (????????)
    "(#Hv &  %Hl1 & %Hl2 & #(Hrel & %WF_t & %WF_s & #Hlr))"; subst.

  setoid_rewrite bind_ret_l. iModIntro.

  pose proof (mcfg_definitions_leaf _ _ _ _ _ _ Hl1 Hl2) as Hsame. subst.
  rewrite /mcfg_definitions in Hl1.

  iAssert (inv [γf] [γf0])%I with "[Hc1 Hs_t Hs_s]" as "Hinv".
  { iFrame. auto. }

  rewrite -H4 in H5.

  (* Lemma. Proof of compatibility. *)
  iPoseProof
    (Proper_interp_mrec' _ _ _ _ (λ x y : uvalue, ⌜obs_val x y⌝)%I [γf] [γf0]
      with "Hinv") as "Hrec"; eauto.
  iApply (sim_expr'_bupd_mono with "[] [Hrec]"); last iApply "Hrec".
  { iIntros (??) "HΨ"; iDestruct "HΨ" as (????) "(%HΨ & HI)".
    iExists _, _; iFrame. done. }
  { rewrite /context_rel.

    (* Related contexts *)
    iSplitL ""; [ | iSplitL "" ].
    (* context_call *)
    { iPureIntro. red. split.
      - cbn. intros; eauto.
      - cbn. intros; eauto. }
    { iPureIntro. red. split.
      - cbn. intros; eauto.
      - cbn. intros; eauto. }

    iSplitL ""; cycle 1.
    {  (* REFL *)
      iIntros (??).
      iModIntro.
      iIntros (?????).
      destruct C0 as ((?&?)&?).
      rewrite /arg_val_rel. cbn -[denote_function].
      iIntros "Hev".
      iDestruct "Hev" as "(#HWF & HC & Hst & Hss & #Hfn & #Hargs)".
      subst.

      destruct (lookup_defn fn_s ((dv', e_s) :: r_s))
        eqn: Hs; cycle 1.

      (* External call case *)
      { cbn in Hs. destruct_if; reldec.
        iDestruct (dval_rel_ne_inj with "Hfn Hdv") as %Hne.
        assert (dv' <> fn_s) by eauto.
        specialize (Hne H3). cbn -[denote_function].
        destruct (RelDec.rel_dec fn_t dv) eqn: Hfn1; reldec; try done.
        iPoseProof (dval_rel_lookup_none with "Hfn Hv") as "%Hlu".
        rewrite /lookup_defn.
        specialize (Hlu Hs); rewrite Hlu.

        rewrite /call_ev; cbn; simp vir_call_ev.
        rewrite /lookup_defn in Hs. rewrite Hs.

        iApply (sim_expr'_bupd_mono);
          last iApply (sim_external_call with "HWF Hst Hss HC Hfn Hargs").
        iIntros (??) "H'".
        rewrite /lift_post.
        iDestruct "H'" as (????) "(#Hv' & HC & Hs_t & Hs_s)".
        iExists _, _; iFrame.
        repeat (iSplitL ""; first done).
        simp vir_call_ans; by iFrame. }

      (* Internal call case *)
      { rewrite /fundefs_rel_WF.

        apply lookup_defn_cons_Some in Hs.
        destruct Hs.
        (* It is the [e_s] function (the hole) *)
        { destruct H2; subst; cbn -[denote_function].
          iDestruct (dval_rel_inj with "Hdv Hfn") as %Hdef; subst.
          destruct (RelDec.rel_dec fn_t fn_t) eqn: Hf; reldec; subst; last done.
          destruct (RelDec.rel_dec dv' dv') eqn: Hf'; reldec; subst; last done.
          subst.

          iDestruct "HWF" as %HWF; subst.
          iDestruct ("Hf" $! _ _ _) as "(_ & Hf')".

          iSpecialize ("Hf'" $! _ _ _ _ HWF with "Hst Hss Hargs HC").
          iApply sim_expr'_bupd_mono; last (iApply "Hf'").
          iIntros (??) "H'".
          rewrite /lift_post.
          iDestruct "H'" as (????) "(Hs_t & Hs_s & HC & Hval)".
          iExists _, _; iFrame. subst; iModIntro.
          repeat (iSplitL ""; first done).
          simp vir_call_ans; by iFrame. }

        (* It is a function in the context *)
        { destruct H2. cbn -[denote_function].

          iDestruct (dval_rel_ne_inj with "Hdv Hfn") as "%Hne"; subst.
          specialize (Hne H2); subst.
          destruct (RelDec.rel_dec fn_t dv) eqn: Hf; reldec; subst; first done.
          destruct (RelDec.rel_dec fn_s dv') eqn: Hf'; reldec; subst; first done.
          clear H2 Hne Hf.
          iPoseProof (dval_rel_lookup_some with "Hfn Hv") as "%Hlu".
          specialize (Hlu _ H3). destruct Hlu as (?&?).
          rewrite /lookup_defn in H3.
          rewrite /lookup_defn; rewrite H2 H3.

          (* Juicing out information from the WF of fundefs *)
          unfold fundefs_WF in WF_s.
          apply andb_prop_elim in WF_s.
          destruct WF_s as (Hlen & Wdup_s).
          apply andb_prop_elim in Hlen. destruct Hlen as (Hlen & Hfun_wf).
          apply forallb_True in Hfun_wf.
          rewrite List.Forall_forall in Hfun_wf.
          assert (Hr_s := H3).
          apply lookup_defn_Some_In in H3.
          (* Function [d] is well-formed. *)
          specialize (Hfun_wf _ H3); cbn in Hfun_wf.

          (* Using [fundefs_logrel] *)
          assert (Hlen': (length [γf0] > 0)%Z → (length [γf] > 0)%Z) by auto.
          rewrite /fundefs_logrel. rewrite /lookup_defn in Hr_s.
          apply lookup_defn_Some_lookup in Hr_s.
          destruct Hr_s.
          (* Juice information out of fundef rel WF *)
          iDestruct "Hrel" as "(Hrel & Hn)".
          iSpecialize ("Hrel" $! _ _ _ H6).
          iDestruct "Hrel" as (???) "(#Hdv' & %Hattr & %Hattr' & %Hft & %Hfs)".

          iDestruct (dval_rel_inj with "Hfn Hdv'") as %Hf; subst.

          iSpecialize ("Hlr" $! _ _ _ _ _ _ H7 H6 Hattr Hattr'
                        with "Hdv'").
          iDestruct "HWF" as %HWF.
          iSpecialize ("Hlr" $! _ _ _ _ HWF with "Hst Hss Hargs HC").

          eapply lookup_defn_Some in H2; eauto;cycle 1.
          { clear -WF_t.

            unfold fundefs_WF in WF_t.
            apply andb_prop_elim in WF_t.
            destruct WF_t as (Hlen & Wdup_t).
            apply andb_prop_elim in Hlen. destruct Hlen as (Hlen & Hfun_wf).
            apply forallb_True in Hfun_wf.
            rewrite List.Forall_forall in Hfun_wf.
            apply Is_true_true_1 in Wdup_t.
            by apply NoDup_b_NoDup. }
          subst.

          iApply sim_expr'_bupd_mono; last iApply "Hlr".
          iIntros (??) "Hin".
          iDestruct "Hin" as (????) "(Hst & Hss & HC & Hval)".
          iExists _, _.
          repeat (iSplitL ""; first done).
          simp vir_call_ans; subst; by iFrame. } } }

    { (* CALL INV *) (* Should follow by fundamental thm?. *)
      iIntros (??). rename r_s into decls. clear H5.
      iModIntro.
      iIntros (???????).
      destruct C0 as ((?&?)&?).
      rewrite /call_ev. cbn -[denote_function].
      iIntros "Hev". simp vir_call_ev.
      iDestruct "Hev" as
        "(#Hfn &%Hdt & %Hattr& #Hargs & HC & #HWF & Hst & Hss & %Hinterp)".
      subst. rename dt_s into dτ, attr_s into attrs.

      destruct (lookup_defn fn_s ((dv', e_s) :: decls))
        eqn: Hs; cycle 1.

      (* External call case *)
      { cbn in Hs. destruct_if; reldec.
        iDestruct (dval_rel_ne_inj with "Hfn Hdv") as %Hne.
        assert (dv' <> fn_s) by eauto.
        specialize (Hne H3). cbn -[denote_function].
        destruct (RelDec.rel_dec fn_t dv) eqn: Hfn1; reldec; try done.
        iPoseProof (dval_rel_lookup_none with "Hfn Hv") as "%Hlu".
        rewrite /lookup_defn.
        specialize (Hlu Hs); rewrite Hlu.

        rewrite /call_ev; cbn; simp vir_call_ev.
        rewrite /lookup_defn in Hs. rewrite Hs.

        cbn in *.

        iApply (sim_expr'_bupd_mono);
          last iApply (sim_external_call' with "HWF Hst Hss HC Hfn Hargs"); eauto.
        iIntros (??) "H'".
        rewrite /lift_post.
        iDestruct "H'" as (????) "(#Hv' & HC & Hs_t & Hs_s)".
        iExists _, _; iFrame.
        repeat (iSplitL ""; first done).
        simp vir_call_ans; by iFrame. }

      (* Internal call case *)
      { rewrite /fundefs_rel_WF.

        apply lookup_defn_cons_Some in Hs.
        destruct Hs. (* Something is off here. FIXME *)
        (* It is the [e_s] function (the hole) *)
        { destruct H2; subst; cbn -[denote_function].
          (* iDestruct (dval_rel_inj with "Hdv Hfn") as %Hdef; subst. *)
          (* destruct (RelDec.rel_dec fn_t fn_t) eqn: Hf; reldec; subst; last done. *)
          (* destruct (RelDec.rel_dec dv' dv') eqn: Hf'; reldec; subst; last done. *)


          (* iDestruct "HWF" as %HWF; subst. *)

          (* iDestruct ("Hf" $! _ _ _) as "(_ & Hf')". *)
          (* specialize (WF_attr _ _ _ _ _ _ _ _ Hinterp); subst. *)

          (* iSpecialize ("Hf'" $! _ _ _ _ HWF with "Hst Hss Hargs HC"). *)
          (* iApply sim_expr'_bupd_mono; last (iApply "Hf'"). *)
          (* iIntros (??) "H'". *)
          (* rewrite /lift_post. *)
          (* iDestruct "H'" as (????) "(Hs_t & Hs_s & HC & Hval)". *)
          (* iExists _, _; iFrame. subst; iModIntro. *)
          (* repeat (iSplitL ""; first done). *)
          (* simp vir_call_ans; by iFrame. } *)
          admit. }

        (* It is a function in the context *)
        { destruct H2. cbn -[denote_function].

          iDestruct (dval_rel_ne_inj with "Hdv Hfn") as "%Hne"; subst.
          specialize (Hne H2); subst.
          destruct (RelDec.rel_dec fn_t dv) eqn: Hf; reldec; subst; first done.
          destruct (RelDec.rel_dec fn_s dv') eqn: Hf'; reldec; subst; first done.
          clear H2 Hne Hf.
          iPoseProof (dval_rel_lookup_some with "Hfn Hv") as "%Hlu".
          specialize (Hlu _ H3). destruct Hlu as (?&?).
          rewrite /lookup_defn in H3.
          rewrite /lookup_defn; rewrite H2 H3.

          (* Juicing out information from the WF of fundefs *)
          unfold fundefs_WF in WF_s.
          apply andb_prop_elim in WF_s.
          destruct WF_s as (Hlen & Wdup_s).
          apply andb_prop_elim in Hlen. destruct Hlen as (Hlen & Hfun_wf).
          apply forallb_True in Hfun_wf.
          rewrite List.Forall_forall in Hfun_wf.
          assert (Hr_s := H3).
          apply lookup_defn_Some_In in H3.
          (* Function [d] is well-formed. *)
          specialize (Hfun_wf _ H3); cbn in Hfun_wf.

          (* Using [fundefs_logrel] *)
          assert (Hlen': (length [γf0] > 0)%Z → (length [γf] > 0)%Z) by auto.
          rewrite /fundefs_logrel. rewrite /lookup_defn in Hr_s.
          apply lookup_defn_Some_lookup in Hr_s.
          destruct Hr_s.
          (* Juice information out of fundef rel WF *)
          iDestruct "Hrel" as "(Hrel & Hn)".
          iSpecialize ("Hrel" $! _ _ _ H5).
          iDestruct "Hrel" as (???) "(#Hdv' & %Hattr & %Hattr' & %Hft & %Hfs)".

          iDestruct (dval_rel_inj with "Hfn Hdv'") as %Hf; subst.

          specialize (WF_attr _ _ _ _ _ _ _ _ Hinterp); subst.
          iSpecialize ("Hlr" $! _ _ _ _ _ _ H7 H6 Hattr Hattr'
                        with "Hdv'").
          iDestruct "HWF" as %HWF.
          iSpecialize ("Hlr" $! _ _ _ _ HWF with "Hst Hss Hargs HC").

          eapply lookup_defn_Some in H2; eauto;cycle 1.
          { clear -WF_t.

            unfold fundefs_WF in WF_t.
            apply andb_prop_elim in WF_t.
            destruct WF_t as (Hlen & Wdup_t).
            apply andb_prop_elim in Hlen. destruct Hlen as (Hlen & Hfun_wf).
            apply forallb_True in Hfun_wf.
            rewrite List.Forall_forall in Hfun_wf.
            apply Is_true_true_1 in Wdup_t.
            by apply NoDup_b_NoDup. }
          subst.

          iApply sim_expr'_bupd_mono; last iApply "Hlr".
          iIntros (??) "Hin".
          iDestruct "Hin" as (????) "(Hst & Hss & HC & Hval)".
          iExists _, _.
          repeat (iSplitL ""; first done).
          simp vir_call_ans; subst; by iFrame. } } } }

  (* Other obligation that "feels like a duplicate obligation",
   but is a separate one coming from the body of the [mrec] *)
  { iModIntro. iIntros "(#HWF & HC & Hst & Hss)".

    iAssert (dval_rel (DVALUE_Addr main) (DVALUE_Addr main))%I as "#Hmain".
    { rewrite (dval_rel_unfold (DVALUE_Addr _)).
      cbn. iSplitL ""; try done.
      iDestruct "Haddr_main" as "(Haddr_main & _)"; done. }

    destruct (lookup_defn (DVALUE_Addr main) ((dv', e_s) :: r_s))
      eqn: Hs; cycle 1.

    (* External call case *)
    { cbn in Hs. destruct_if; reldec.
      iDestruct (dval_rel_ne_inj with "Hmain Hdv") as %Hne.
      assert (dv' <> DVALUE_Addr main) by eauto.
      specialize (Hne H3). cbn -[denote_function map_monad].
      destruct (RelDec.rel_dec (DVALUE_Addr main) dv) eqn: Hfn1;
        reldec; try done.
      iPoseProof (dval_rel_lookup_none with "Hmain Hv") as "%Hlu".
      rewrite /lookup_defn.
      specialize (Hlu Hs); rewrite Hlu.

      iApply (sim_expr'_bupd_mono);
        last iApply (sim_external_call with "HWF Hst Hss HC Hmain"); try done.
      iIntros (??) "H'".
      rewrite /lift_post.
      iDestruct "H'" as (????) "(#Hv' & HC & Hs_t & Hs_s)".
      iExists _, _; iFrame.
      repeat (iSplitL ""; first done).
      (iSplitR ""; last done).

      iApply (uval_rel_implies_obs_val with "Hv'"). }

    (* Internal call case *)
    { apply lookup_defn_cons_Some in Hs.
      destruct Hs.
      (* It is the [e_s] function (the hole) *)
      { destruct H2; inv H2; subst. cbn -[denote_function].
        iDestruct (dval_rel_inj with "Hdv Hmain") as %Hdef; subst.
        destruct (RelDec.rel_dec (DVALUE_Addr main) (DVALUE_Addr main))
          eqn: Hf; reldec; subst; last done.
        rewrite /fun_logrel.
        iDestruct "HWF" as %HWF.
        iDestruct ("Hf" $! _ _ _) as "(_ & Hf')".

        iSpecialize ("Hf'" $! _ _ nil nil HWF with "Hst Hss").
        cbn -[denote_function].
        iSpecialize ("Hf'" $! Logic.I with "HC").

        iApply sim_expr'_bupd_mono; last (iApply "Hf'").
        iIntros (??) "H'".
        rewrite /lift_post.
        iDestruct "H'" as (????) "(Hs_t & Hs_s & HC & Hval)".
        iExists _, _; iFrame. subst; iModIntro.
        repeat (iSplitL ""; first done).
        (iSplitR ""; last done).
        iApply (uval_rel_implies_obs_val with "Hval"). }

      (* It is a function in the context *)
      { destruct H2; cbn -[denote_function].

        iDestruct (dval_rel_ne_inj with "Hdv Hmain") as "%Hne"; subst.
        specialize (Hne H2); subst.
        destruct (RelDec.rel_dec (DVALUE_Addr main) dv) eqn: Hf;
          reldec; subst; first done.
        clear H2 Hne Hf.
        iPoseProof (dval_rel_lookup_some with "Hmain Hv") as "%Hlu".
        specialize (Hlu _ H3). destruct Hlu as (?&?).
        rewrite /lookup_defn H2.

        (* Juicing out information from the WF of fundefs *)
        unfold fundefs_WF in WF_s.
        apply andb_prop_elim in WF_s.
        destruct WF_s as (Hlen & Wdup_s).
        apply andb_prop_elim in Hlen. destruct Hlen as (Hlen & Hfun_wf).
        apply forallb_True in Hfun_wf.
        rewrite List.Forall_forall in Hfun_wf.
        assert (Hr_s := H3).
        apply lookup_defn_Some_In in H3.
        (* Function [d] is well-formed. *)
        specialize (Hfun_wf _ H3); cbn in Hfun_wf.

        (* Using [fundefs_logrel] *)
        assert (Hlen': (length [γf0] > 0)%Z → (length [γf] > 0)%Z) by auto.
        rewrite /fundefs_logrel.
        apply lookup_defn_Some_lookup in Hr_s.
        destruct Hr_s.
        (* Juice information out of fundef rel WF *)
        iDestruct "Hrel" as "(Hrel & Hn)".
        iSpecialize ("Hrel" $! _ _ _ H6).
        iDestruct "Hrel" as (???)
                              "(#Hdv' & %Hattr & %Hattr' & %Hft & %Hfs)".

        iSpecialize ("Hlr" $! _ _ _ _ _ _ H7 H6 Hattr Hattr'
                      with "Hdv'").
        iSpecialize ("Hlr" $! _ _ nil nil Hlen' with "Hst Hss").
        cbn -[denote_function].
        iSpecialize ("Hlr" $! Logic.I with "HC").

        iDestruct (dval_rel_inj with "Hmain Hdv'") as %Hf; subst.

        eapply lookup_defn_Some in H2; eauto;cycle 1.
        { clear -WF_t.

          unfold fundefs_WF in WF_t.
          apply andb_prop_elim in WF_t.
          destruct WF_t as (Hlen & Wdup_t).
          apply andb_prop_elim in Hlen. destruct Hlen as (Hlen & Hfun_wf).
          apply forallb_True in Hfun_wf.
          rewrite List.Forall_forall in Hfun_wf.
          apply Is_true_true_1 in Wdup_t.
          by apply NoDup_b_NoDup. }
        eauto.
        subst.

        iApply sim_expr'_bupd_mono; last iApply "Hlr".
        iIntros (??) "Hin".
        iDestruct "Hin" as (????) "(Hst & Hss & HC & Hval)".
        iExists _, _; subst.
        repeat (iSplitL ""; first done); iFrame.
        (iSplitR ""; last done).

        iApply (uval_rel_implies_obs_val with "Hval"). } } }
    Unshelve.
    all : eauto. all: do 2 constructor.
  Qed.
