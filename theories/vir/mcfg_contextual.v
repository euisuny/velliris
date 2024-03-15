From iris.prelude Require Import options.

From velliris.program_logic Require Import program_logic.
From velliris.vir Require Import
  vir val_rel heapbij adequacy spec globalbij logical_relations fundamental
  interp_properties.

From Vellvm Require Import Syntax.DynamicTypes Handlers Syntax.LLVMAst
  Semantics.InterpretationStack.

From Equations Require Import Equations.

From ITree Require Import ITree Recursion Eq.Eqit.
From Equations Require Import Equations.

Import LLVMEvents.

Set Default Proof Using "Type*".

Opaque mrec.

(* -------------------------------------------------------------------------- *)

(* ITree-related tactics *)
Ltac obs_hyp :=
  match goal with
  | [ H : {| _observe := observe _ |} = _ |- _] =>
      let Hobs := fresh "Hobs" in
      inversion H as [ Hobs ]; clear H
  end.

(* Turn an [observe] hypothesis to an ITree equivalence. *)
Ltac simpobs_eqit :=
  obs_hyp;
  match goal with
  | [ H : observe _ = _ |- _] =>
      symmetry in H; apply Eqit.simpobs in H
  end.

Section mcfg_contextual.

  Context `(sheapGS Σ, checkedoutGS Σ, heapbijGS Σ).

  Definition args_rel :=
    fun args_t args_s => ([∗ list] x;y ∈ args_t ;args_s, uval_rel x y)%I.

  (* Invariant for frame-related resources across a single function call that
     is satisfied by the fundamental theorem *)
  Definition frame_inv i_t i_s :=
    (frame_WF i_t i_s ∗ checkout ∅ ∗ stack_tgt i_t ∗ stack_src i_s)%I.

  (* An obligation for each of the defined calls; it satisfies the external
      call specifications *)
  Definition context_rel
      (f : ∀ T : Type, CallE T → L0'expr T)
      (g : ∀ T : Type, CallE T → L0'expr T) :=
    (∀ fn1 fn2 dt1 dt2 args1 args2 C,
          let call1 := ExternalCall dt1 fn1 args1 nil in
          let call2 := ExternalCall dt2 fn2 args2 nil in
          call_ev call1 call2 C -∗
          ⟅ f _ (Call dt1 fn1 args1 nil) ⟆ ⪯
          ⟅ g _ (Call dt2 fn2 args2 nil) ⟆
          [[ (fun v1 v2 => call_ans call1 v1 call2 v2 C) ⤉ ]])%I.

  Notation st_expr_rel' R1 R2 :=
    (@st_exprO' vir_lang R1 -d> @st_exprO' vir_lang R2 -d> iPropI Σ).

  Definition contains_base {T} Φ :=
    (∀ x y : st_exprO' T, base x y ∗ Φ x y ∗-∗ Φ x y : iProp Σ)%I.

  (* Auxiliary definitions for [Proper_interp_mrec] *)
  (* Because [sim_expr] includes stateful interpretation, showing properness result
    for [interp_mrec] amounts to proving a simulation *)
  Local Definition mrec_pred :=
    fun (Φ:st_expr_rel' _ _) (e_t:st_expr' vir_lang _) (e_s:st_expr' vir_lang _) =>
      (∃ f g t dv args attr σ_t σ_s,
          ⌜e_t = observe (⟦ mrec f (Call t dv args attr) ⟧ σ_t)⌝ ∗
          ⌜e_s = observe (⟦ mrec g (Call t dv args attr) ⟧ σ_s)⌝ ∗
          (* Function is called on related addresses and arguments *)
          dval_rel dv dv ∗
          args_rel args args ∗
          (* Postcondition contains [base] predicate*)
          □ contains_base Φ ∗
          (* Contexts are related *)
          □ context_rel f g ∗
          sim_coindF Φ
              (observe (⟦ ⟅ f uvalue (Call t dv args attr) ⟆ ⟧ σ_t))
              (observe (⟦ ⟅ g uvalue (Call t dv args attr) ⟆ ⟧ σ_s)))%I.

  Local Definition mrec_rec :=
    fun (Φ:st_expr_rel' _ _) (e_t:st_expr' vir_lang _) (e_s:st_expr' vir_lang _) =>
      ((∃ f g t dv args attr σ_t σ_s,
          ⌜e_t = observe (⟦ mrec f (Call t dv args attr) ⟧ σ_t)⌝ ∗
          ⌜e_s = observe (⟦ mrec g (Call t dv args attr) ⟧ σ_s)⌝ ∗
          dval_rel dv dv ∗ args_rel args args ∗
          □ contains_base Φ ∗
          □ context_rel f g ∗
         sim_coindF Φ
          (observe (⟦ ⟅ f uvalue (Call t dv args attr) ⟆ ⟧ σ_t))
          (observe (⟦ ⟅ g uvalue (Call t dv args attr) ⟆ ⟧ σ_s)))
        ∨ sim_coindF Φ e_t e_s)%I.

  Local Instance mrec_pred_ne:
    NonExpansive (mrec_pred: st_expr_rel' _ _ -d> st_expr_rel' _ _).
  Proof.
    intros x y *. solve_proper_prepare. do 22 f_equiv; try solve_proper.
  Qed.

  Local Instance mrec_rec_ne:
    NonExpansive (mrec_rec: st_expr_rel' _ _ -d> st_expr_rel' _ _).
  Proof.
    intros x y *. solve_proper_prepare.
  Admitted.

  (* -------------------------------------------------------------------------- *)
  (* Local notations to make life "easier".. *)
  Local Notation sim_mrec_ind := (sim_expr_inner mrec_rec (sim_indF mrec_rec)).
  Local Notation "o⟦ e ⟧ σ" := (observe (⟦ e ⟧ σ)) (at level 12).
  (* -------------------------------------------------------------------------- *)

  (* Utility lemmas *)
  Lemma vir_call_ev_nil i_t i_s t dv args :
    frame_inv i_t i_s -∗
    dval_rel dv dv -∗
    args_rel args args -∗
    vir_call_ev Σ
    (ExternalCall t dv args []) (ExternalCall t dv args []) (∅, i_t, i_s).
  Proof.
    iIntros "(?&?&?&?&?) Hv Huv".
    simp vir_call_ev; iFrame; eauto. iPureIntro; do 2 (split; eauto).
    simp attribute_interp. cbn. exists OTHER. tauto.
  Qed.

  (* Access [frame_WF] predicate out of [frame_inv] *)
  Lemma frame_inv_frame_WF i_t i_s :
    frame_inv i_t i_s -∗
    frame_WF i_t i_s.
  Proof. iIntros "(?&?&?&?)"; done. Qed.

(* -------------------------------------------------------------------------- *)

  (* Induction hypothesis for [Proper_mrec] *)
  Local Definition mrec_ind :=
    (λ Φ e_t e_s,
      ∀ (f g : ∀ T : Type, LLVMEvents.CallE T → L0'expr T) t dv args attr σ_t σ_s,
        ⌜e_t = observe (⟦ ⟅ f uvalue (Call t dv args attr) ⟆ ⟧ σ_t) ⌝ -∗
        ⌜e_s = observe (⟦ ⟅ g uvalue (Call t dv args attr) ⟆ ⟧ σ_s) ⌝ -∗
        args_rel args args -∗
        □ contains_base Φ -∗
        □ context_rel f g -∗
        sim_indF mrec_rec Φ
        (observe (⟦ mrec f (Call t dv args attr) ⟧ σ_t))
        (observe (⟦ mrec g (Call t dv args attr) ⟧ σ_s)))%I.

  Local Instance mrec_ind_ne:
    NonExpansive (mrec_ind: st_expr_rel' _ _ -d> st_expr_rel' _ _).
  Proof.
    solve_proper_prepare. clear -H. repeat f_equiv.
  Admitted.

  Lemma Proper_mrec_pred
    (f g : ∀ T : Type, LLVMEvents.CallE T → L0'expr T) i_t i_s t dv args σ_t σ_s:
      (* Function address value and arguments are self-related *)
      dval_rel dv dv -∗
      args_rel args args -∗
      (* Frame invariant holds *)
      frame_inv i_t i_s -∗
      (* Contexts are related *)
      □ context_rel f g -∗
      state_interp σ_t σ_s ==∗
      mrec_pred (lift_rel ((λ _ _ : uvalue, frame_inv i_t i_s) ⤉))
        (observe (⟦ mrec f (Call t dv args []) ⟧ σ_t))
        (observe (⟦ mrec g (Call t dv args []) ⟧ σ_s)).
  Proof.
    rewrite /mrec_pred.
    iIntros "#Hdv #Hargs Hinv #Hrel SI".
    iExists f, g, t, dv, args, nil, σ_t, σ_s.
    do 2 (iSplitL ""; first done); iFrame "Hrel".
    rewrite /call_ev; cbn -[state_interp].
    iSpecialize ("Hrel" $! dv dv t t args args (∅, i_t, i_s)).
    iPoseProof (frame_inv_frame_WF with "Hinv") as "%Hframe_WF".
    iPoseProof (vir_call_ev_nil with "Hinv Hdv Hargs") as "Hev".
    iSpecialize ("Hrel" with "Hev SI").
    iFrame "Hdv Hargs".

    (* Base postcondition *)
    iSplitL "".
    { do 2 iModIntro. iIntros (??). iSplitL ""; iIntros "H".
      - iDestruct "H" as "(H & Hr)"; done.
      - iDestruct "H" as (????) "(SI&H)". (* TODO fact about [base] *)
        iDestruct "H" as (??????) "H".
        iFrame. iSplit.
        { rewrite /base. subst.
          iExists (σ_t0, v_t), (σ_s0, v_s). iPureIntro; split.
          { apply EqAxiom.bisimulation_is_eq.
            rewrite H4. by rewrite -itree_eta. }
          { apply EqAxiom.bisimulation_is_eq.
            rewrite H5. by rewrite -itree_eta. } }
        subst.
        iExists σ_t0, σ_s0, e_t, e_s; iFrame.
        do 2 (iSplitL ""; [ done | ]).
        iExists v_t, v_s; done. }
    iMod "Hrel".

    (* Establish postcondition. *)
    iApply (sim_coindF_bupd_mono with "[] Hrel").
    iIntros (??) "Hrel". rewrite /lift_rel.
    iDestruct "Hrel" as (????) "(SI & %Ht & %Hs & Hrel)"; subst.
    (* Access lifted postcondition *)
    iDestruct "Hrel" as (????) "Hrel". rewrite /call_ans /=.
    simp vir_call_ans. iDestruct "Hrel" as "(?&?&?&#?)"; iFrame.
    (* Prove postcondition. *)
    iExists σ_t0, σ_s0, e_t0, e_s0; iFrame.
    do 2 (iSplitL ""; first done).
    iExists v_t, v_s; done.
  Qed.

  (* Cases for [Proper_mrec] *)
  Lemma Proper_mrec_base f g t dv args attr σ_t σ_s Ψ:
    dval_rel dv dv -∗
    args_rel args args -∗
    <pers> contains_base Ψ -∗
    <pers> context_rel f g -∗
    Ψ (o⟦ ⟅ f uvalue (Call t dv args attr) ⟆ ⟧ σ_t)
      (o⟦ ⟅ g uvalue (Call t dv args attr) ⟆ ⟧ σ_s) -∗
    sim_mrec_ind Ψ
      (o⟦ mrec f (Call t dv args attr) ⟧ σ_t)
      (o⟦ mrec g (Call t dv args attr) ⟧ σ_s).
  Proof.
    iIntros "#Hdv #Hargs #Hbase #Hcrel HΨ".
    iSpecialize ("Hbase" with "HΨ").
    iDestruct "Hbase" as "(Hb & He)".
    iDestruct "Hb" as (???) "%Hb".

    do 2 simpobs_eqit.
    apply interp_L2_conv_ret_inv in Hobs, Hobs0.
    to_eq in Hobs; to_eq in Hobs0; subst; cbn.

    (* force unfold mrec *)
    with_strategy transparent [mrec] unfold mrec.
    rewrite Hobs Hobs0. cbn.
    by provide_case: BASE.
  Qed.

  Theorem Proper_mrec f g i_t i_s t dv args:
    (* Function address value and arguments are self-related *)
    dval_rel dv dv -∗
    args_rel args args -∗
    (* Frame invariant holds *)
    frame_inv i_t i_s -∗
    (* Contexts are related *)
    <pers> context_rel f g -∗
    mrec f (Call t dv args nil) ⪯ mrec g (Call t dv args nil)
    [[ (fun x y => frame_inv i_t i_s) ⤉ ]].
  Proof.
    iIntros "#Hdv #Hargs Hinv #Hrel"; iIntros (??) "SI".

    (* Initialize coinductive hypothesis. *)
    iApply (sim_coindF_strong_coind mrec_pred); cycle 1.
    { iApply (Proper_mrec_pred with "Hdv Hargs Hinv Hrel SI"). }

    (* Set up context *)
    iModIntro. iClear "Hdv Hargs Hrel". clear.
    iIntros (Φ e_t e_s) "IH";
    iDestruct "IH" as (??????????) "(#Hdv & #Hargs & #Hbase & #Hcrel & IH)";
      subst.

    (* Induction on simulation between (f call) and (g call). *)
    rewrite sim_coindF_unfold.
    iAssert (∀ Ψ e_t e_s, (sim_indF sim_coindF Ψ e_t e_s) -∗
      mrec_ind Ψ e_t e_s)%I as "Hgen"; last first.
    { iSpecialize ("Hgen" with "IH").
      rewrite /mrec_ind.
      iApply ("Hgen" $! _ _ _ _ _ _ _ _ eq_refl eq_refl with "Hargs Hbase Hcrel"). }

    (* Set up context *)
    iClear "Hargs Hdv Hcrel Hbase"; clear.
    iIntros (Ψ e_t e_s) "Hsim".
    iApply (sim_indF_strong_ind with "[] Hsim"); clear.
    iModIntro; iIntros (Ψ e_t e_s) "Hinner".
    iIntros (??????????) "#Hargs #Hbase #Hcrel"; subst.

    (* [Hinner] for the "inner" expression, i.e. [e_s] *)
    rewrite /sim_expr_inner;
    cbn -[F] in *; rewrite sim_indF_unfold /sim_expr_inner.
    iMod "Hinner"; to_inner mrec_rec.

    (* Case analysis on the inductive information. *)
    iDestruct "Hinner" as ( c ) "Hinner"; destruct c; try case_solve; try done.

    (* [BASE] case *)
    { iApply (Proper_mrec_base with "Hargs Hbase Hcrel Hinner"). }

    (* [STUTTER_L] case *)
    { admit. }

    (* [STUTTER_R] case *)
    { admit. }

    (* [TAU_STEP] case *)
    { admit. }

    (* [VIS] case *)
    { admit. }

    (* [UB] case *)
    { simpobs_eqit; by eapply interp_L2_conv_UB_inv in Hobs. }

    (* [EXC] case *)
    { simpobs_eqit; by eapply interp_L2_conv_failure_inv in Hobs. }
  Admitted. (* TODO : Port over proof *)

(* -------------------------------------------------------------------------- *)

  (* Type declaration for function definitions, i.e. an association list for
     function definitions with [dvalue] keys. *)
  Definition fundefs : Type := list (dvalue * definition dtyp (CFG.cfg dtyp)).

  Definition fundef_no_attr (def : definition dtyp (CFG.cfg dtyp)) :=
    RelDec.rel_dec (dc_attrs (df_prototype def)) nil.

  (* The function definition map [fd] does not have any attributes at its
    definition site. *)
  Definition fundefs_no_attr (fd : fundefs) :=
    forallb (fun '(_, def) => fundef_no_attr def) fd.

(* -------------------------------------------------------------------------- *)

  Lemma sim_external_call dτ addr_t addr_s args_t args_s l i_t i_s:
    frame_WF i_t i_s -∗
    stack_tgt i_t -∗
    stack_src i_s -∗
    checkout ∅ -∗
    dval_rel addr_t addr_s -∗
    ([∗ list] x;y ∈ args_t;args_s, uval_rel x y) -∗
    ⟅ dargs <- Util.map_monad (λ uv : uvalue, pickUnique uv) args_t;;
    trigger (ExternalCall dτ addr_t (map dvalue_to_uvalue dargs) l) ⟆
      ⪯
      ⟅ dargs <- Util.map_monad (λ uv : uvalue, pickUnique uv) args_s;;
    trigger (ExternalCall dτ addr_s (map dvalue_to_uvalue dargs) l) ⟆
      [[ (fun x y =>
            uval_rel x y ∗ stack_tgt i_t ∗ stack_src i_s ∗
              checkout ∅) ⤉ ]].
  Proof. Admitted.

  (* -------------------------------------------------------------------------- *)

  (* Utility TODO: Move *)
  Lemma dval_rel_lookup_defn_cons {B fn_t fn_s fn_t' fn_s'} e_t e_s F :
    dval_rel fn_t fn_s -∗
    dval_rel fn_t' fn_s' -∗
    ([∗ list] v_t;v_s ∈ F.*1;F.*1, dval_rel v_t v_s) -∗

    (* Both match on the head of the list *)
    ⌜(lookup_defn fn_t ((fn_t', e_t) :: F) = Some e_t /\
        lookup_defn fn_s ((fn_s', e_s) :: F) = Some e_s) ∨

    (* Both match on an element in [F] *)
    (exists f g,
      lookup_defn fn_t F = Some f /\
      lookup_defn fn_s F = Some g /\
      lookup_defn fn_t ((fn_t', e_t) :: F) = Some f /\
      lookup_defn fn_s ((fn_s', e_s) :: F) = Some g) ∨

    (* Or it is not found *)
    (lookup_defn fn_t ((fn_t', e_t) :: F) = None /\
      lookup_defn (B := B) fn_s ((fn_s', e_s) :: F) = None)⌝.
  Proof.
    iIntros "Hv Hv' HF"; cbn.
    destruct (RelDec.rel_dec fn_s fn_s') eqn: Ht;
      [ iLeft; iSplit; eauto; reldec | iRight ]; reldec.
    (* Head *)
    { iDestruct (dval_rel_inj with "Hv Hv'") as "%He"; subst.
      by rewrite Util.eq_dec_eq. }

    (* Rest *)
    { iDestruct (dval_rel_ne_inj with "Hv Hv'") as "%He".
      assert (Hs: fn_s' <> fn_s) by eauto. specialize (He Hs).
      rewrite Util.eq_dec_neq; eauto.

      destruct (lookup_defn fn_s F) eqn: Hf_t.
      { iDestruct (dval_rel_lookup_some with "Hv HF") as %Hft.
        specialize (Hft _ Hf_t); destruct Hft as (?&Hft).
        iLeft; iPureIntro; eauto.
        exists x, b; split; [ | split]; eauto. }

      { iDestruct (dval_rel_lookup_none with "Hv HF") as %Hft.
        specialize (Hft Hf_t).
        iRight; iPureIntro; eauto. } }
  Qed.

  Lemma fundef_no_attr_eq def :
    fundef_no_attr def ->
    (dc_attrs (df_prototype def)) = nil.
  Proof. Admitted.

  (* The contextual refinement on [denote_mcfg]. *)
  Lemma contextual_denote_mcfg :
    ∀ γ_t γ_s addr_t addr_s e_t e_s main F,
      fun_WF e_t ->
      fun_WF e_s ->
      fundefs_WF F nil ->
      fundefs_no_attr F ->
      fundef_no_attr e_t ->
      fundef_no_attr e_s ->
      □ fun_logrel e_t e_s ∅ -∗
        checkout ∅ -∗
        stack_tgt [γ_t] -∗
        stack_src [γ_s] -∗
        dval_rel addr_t addr_s -∗
        ([∗ list] v_t;v_s ∈ F.*1;F.*1, dval_rel v_t v_s) -∗
        denote_mcfg ((addr_t, e_t) :: F) DTYPE_Void (DVALUE_Addr main) []
        ⪯
        denote_mcfg ((addr_s, e_s) :: F) DTYPE_Void (DVALUE_Addr main) []
        [[ (λ x y : uvalue, ⌜obs_val x y⌝) ⤉ ]].
  Proof.
    iIntros (???????? WF_t WF_s WF_F HC H_t H_s) "#Hfun Hc Hs_t Hs_s #Hdv #Hfun_keys".

    (* The frame invariant holds. *)
    iAssert (frame_inv [γ_t] [γ_s])%I with "[Hc Hs_t Hs_s]" as "Hinv".
    { by iFrame. }

    iPoseProof
      (Proper_mrec _ _ (λ x y : uvalue, ⌜obs_val x y⌝)%I [γ_t] [γ_s]
        with "Hinv") as "Hrec"; eauto.
    iApply (sim_expr'_bupd_mono with "[] [Hrec]"); last iApply "Hrec".

    (* Establish postcondition; trivial  *)
    { iIntros (??) "HΨ"; iDestruct "HΨ" as (????) "(%HΨ & HI)".
      iExists _, _; iFrame. done. }

    rewrite /context_rel; iModIntro.

    (* Preparing proof state *)
    iIntros (fn_t fn_s dτ_t dτ_s args_t args_s C) "Hev";
      destruct C as ((?&i_t)&i_s);
    rewrite /call_ev; cbn -[denote_function lookup_defn]; simp vir_call_ev;
    iDestruct "Hev" as
      "(#Hfn &%Hdt & %Hattr& #Hargs & HC & #HWF & Hst & Hss & %Hinterp)"; subst.

    (* Do a case analysis on whether the function is in the list of fundefs.

      Because the context applied to the expression results in a closed term,
      the function is always found in the context. *)

    iDestruct (dval_rel_lookup_defn_cons e_t e_s F with "Hfn Hdv Hfun_keys") as %Hlu.
    destruct Hlu as [ (->&->) | [ Hlu | Hlu ] ]; last admit. (* last case is absurd *)

    (* It is the hole *)
    { apply fundef_no_attr_eq in H_t, H_s; rewrite H_t H_s.
      assert (Heq : RelDec.rel_dec (T := list fn_attr) nil nil = true) by admit;
        rewrite Heq.
      admit. }

    (* It is a function in the context *)
    { destruct Hlu as (f_t & f_s & Hlu_t & Hlu_s & -> & ->).
      admit. } (* Should follow trivially. *)

  Admitted.

End mcfg_contextual.
