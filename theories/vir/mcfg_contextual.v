From iris.prelude Require Import options.

From velliris.program_logic Require Import program_logic.
From velliris.vir Require Import
  vir val_rel heapbij adequacy spec globalbij logical_relations fundamental.

From Vellvm Require Import Syntax.DynamicTypes Handlers Syntax.LLVMAst
  Semantics.InterpretationStack.

From ITree Require Import ITree Recursion.
From Equations Require Import Equations.

Import LLVMEvents.

Set Default Proof Using "Type*".

Section mcfg_contextual.

  Context `(sheapGS Σ, checkedoutGS Σ, heapbijGS Σ).

  (* Invariant for frame-related resources across a single function call that
     is satisfied by the fundamental theorem *)
  Definition frame_inv i_t i_s :=
    (frame_WF i_t i_s ∗ checkout ∅ ∗ stack_tgt i_t ∗ stack_src i_s ∗
       ⌜(length i_s > 0)%Z → (length i_t > 0)%Z⌝)%I.

  (* An obligation for each of the defined calls; it satisfies the external
      call specifications *)
  Definition context_rel
      (f : ∀ T : Type, CallE T → L0'expr T)
      (g : ∀ T : Type, CallE T → L0'expr T) :=
    (□ (∀ fn1 fn2 dt1 dt2 args1 args2 C,
          let call1 := ExternalCall dt1 fn1 args1 nil in
          let call2 := ExternalCall dt2 fn2 args2 nil in
          call_ev call1 call2 C -∗
          ⟅ f _ (Call dt1 fn1 args1 nil) ⟆ ⪯
          ⟅ g _ (Call dt2 fn2 args2 nil) ⟆
          [[ (fun v1 v2 => call_ans call1 v1 call2 v2 C) ⤉ ]]) )%I.


  Notation st_expr_rel' R1 R2 :=
    (@st_exprO' vir_lang R1 -d> @st_exprO' vir_lang R2 -d> iPropI Σ).

  (* Auxiliary definitions for [Proper_interp_mrec] *)
  (* Because [sim_expr] includes stateful interpretation, showing properness result
    for [interp_mrec] amounts to proving a simulation *)
  Local Definition interp_mrec_pred :=
    fun (Φ:st_expr_rel' _ _) (e_t:st_expr' vir_lang _) (e_s:st_expr' vir_lang _) =>
      (∃ f g t dv args attr σ_t σ_s,
          ⌜e_t = observe (⟦ interp_mrec f (f uvalue (Call t dv args attr)) ⟧ σ_t)⌝ ∗
          ⌜e_s = observe (⟦ interp_mrec g (g uvalue (Call t dv args attr)) ⟧ σ_s)⌝ ∗
          context_rel f g ∗
          sim_coindF Φ
              (observe (⟦ ⟅ (f uvalue (Call t dv args attr)) ⟆ ⟧ σ_t))
              (observe (⟦ ⟅ (g uvalue (Call t dv args attr)) ⟆ ⟧ σ_s)))%I.

  Local Definition interp_mrec_rec :=
    fun (Φ:st_expr_rel' _ _) (e_t:st_expr' vir_lang _) (e_s:st_expr' vir_lang _) =>
      ((∃ f g t dv args attr σ_t σ_s,
          ⌜e_t = observe (⟦ interp_mrec f (f uvalue (Call t dv args attr)) ⟧ σ_t)⌝ ∗
          ⌜e_s = observe (⟦ interp_mrec g (g uvalue (Call t dv args attr)) ⟧ σ_s)⌝ ∗
         context_rel f g ∗
         sim_coindF Φ
          (observe (⟦ ⟅ (f uvalue (Call t dv args attr)) ⟆ ⟧ σ_t))
          (observe (⟦ ⟅ (g uvalue (Call t dv args attr)) ⟆ ⟧ σ_s)))
        ∨ sim_coindF Φ e_t e_s)%I.

  Local Instance interp_mrec_pred_ne:
    NonExpansive (interp_mrec_pred: st_expr_rel' _ _ -d> st_expr_rel' _ _).
  Proof.
    intros x y *. solve_proper_prepare. do 18 f_equiv; try solve_proper.
  Qed.

  Local Instance interp_mrec_rec_ne:
    NonExpansive (interp_mrec_rec: st_expr_rel' _ _ -d> st_expr_rel' _ _).
  Proof.
    intros x y *. solve_proper_prepare. repeat f_equiv; try solve_proper.
  Qed.

  From Equations Require Import Equations.

  Lemma vir_call_ev_nil i_t i_s t dv args :
    frame_inv i_t i_s -∗
    dval_rel dv dv -∗
    vir_call_ev Σ (ExternalCall t dv args []) (ExternalCall t dv args []) (∅, i_t, i_s).
  Admitted.

  Theorem Proper_mrec
    (f g : ∀ T : Type, LLVMEvents.CallE T → L0'expr T)
    (Ψ : _ -d> _ -d> iPropI Σ) i_t i_s t dv args attr:
    dval_rel dv dv -∗
    frame_inv i_t i_s -∗
    context_rel f g -∗
    mrec f (Call t dv args attr) ⪯ mrec g (Call t dv args attr)
    [[ (fun x y => Ψ x y ∗ frame_inv i_t i_s) ⤉ ]].
  Proof.
    rewrite /mrec.
    iIntros "#Hdv Hinv #Hrel"; iIntros (??) "SI".

    iApply (sim_coindF_strong_coind interp_mrec_pred); cycle 1.
    { rewrite /interp_mrec_pred.
      iExists f, g, t, dv, args, attr, σ_t, σ_s.
      do 2 (iSplitL ""; first done); iFrame "Hrel".
      rewrite /call_ev; cbn -[state_interp].
      iSpecialize ("Hrel" $! dv dv t t args args (∅, i_t, i_s)).
      iPoseProof (vir_call_ev_nil with "Hinv Hdv") as "Hev".
      iSpecialize ("Hrel" with "Hev SI").
      iMod "Hrel". admit. }

    iModIntro.

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
