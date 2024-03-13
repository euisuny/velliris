From iris.prelude Require Import options.

From Equations Require Import Equations.

From ITree Require Import ITree Eq.Eqit Interp.InterpFacts Interp.TranslateFacts.
From simuliris.simulation Require Import slsls sim_properties reduction.
From Vellvm.Syntax Require Import LLVMAst DynamicTypes CFG.
From Vellvm.Semantics Require Import InterpretationStack.
From Vellvm.Theory Require Import DenotationTheory.
From simuliris.vir Require Import spec instr_laws bij_laws tactics fundamental_exp vir_util.

From Vellvm Require Import Handlers.Handlers.
Import DenoteTactics.
Import CFG.

Definition make_decl name: declaration dtyp :=
  {| dc_name := Name name;
    dc_type := DTYPE_Void;
    dc_param_attrs := (nil, nil);
    dc_linkage     := None ;
    dc_visibility  := None ;
    dc_dll_storage := None ;
    dc_cconv       := None ;
    dc_attrs       := nil ;
    dc_section     := None ;
    dc_align       := None ;
    dc_gc          := None |}.

Definition make_blk blk : LLVMAst.block dtyp :=
  {| blk_id := Name "main";
    blk_phis := nil;
    blk_code := blk;
    blk_term := TERM_Ret_void;
    blk_comments := None; |}.

Definition make_body blk : CFG.cfg dtyp :=
  {| init := Name "main";
     blks := make_blk blk :: nil;
     CFG.args := nil |}.

Definition make_fn name blk args : definition dtyp (CFG.cfg dtyp) :=
  {| df_prototype := make_decl name;
    df_args := args;
    df_instrs := make_body blk |}.

Ltac destruct_if_goal :=
  repeat match goal with
    | [ |- context[if ?x then _ else _] ] =>
        let Hx := fresh "H" in
      destruct x eqn: Hx; inversion H; subst
end.

Ltac instr_conv_normalize :=
  repeat match goal with
    | |- context[instr_conv (Monad.bind ?x _)] =>
        let Hx := fresh "Hx" in
          epose proof (instr_conv_bind x) as Hx;
          setoid_rewrite Hx; clear Hx
  end.

Section contextual_properties.

  Context {Σ : gFunctors} `{!sheapGS Σ, !checkedoutGS Σ, !heapbijGS Σ}.

  Theorem code_make_block_contextual c_t c_s Φ P:
    (P -∗ instr_conv (denote_code c_t) ⪯
    instr_conv (denote_code c_s) [{ (x, y), Φ }]) -∗
    P -∗
    ∀ bid_t bid_s,
      instr_conv (denote_block (make_blk c_t) bid_t) ⪯
      instr_conv (denote_block (make_blk c_s) bid_s)
      [{ (x, y),
          Φ ∗ ⌜x = inr UVALUE_None⌝ ∗ ⌜y = inr UVALUE_None⌝ }].
  Proof.
    iIntros "H HP".
    iIntros (bid_t bid_s).

    rewrite /denote_block.
    instr_conv_normalize.
    cbn -[denote_code].
    rewrite bind_ret_l. rewrite /Util.map_monad.
    rewrite bind_ret_l.
    rewrite instr_conv_ret.
    rewrite !bind_ret_l.
    iApply sim_expr_bind.
    iApply sim_expr_bupd_mono; last by iApply "H".
    cont. rewrite !translate_ret. rewrite !instr_conv_ret.
    iApply sim_expr_base.
    iExists _, _; iFrame; done.
  Qed.

  Opaque denote_block.
  Theorem code_to_fn_contextual name c_t c_s i_t i_s C:
    initial_frame_res [i_t] [i_s] C -∗
    □ (∀ j_t j_s, frame_WF j_t j_s ∗
                   frame_resources_own j_t j_s empty_frame empty_frame C -∗
        instr_conv (denote_code c_t) ⪯
        instr_conv (denote_code c_s)
      [{ (x, y), frame_WF j_t j_s ∗
                   frame_resources_own_exist j_t j_s C }]) -∗
    (<{{ (make_fn name c_t nil) (nil) }}> ) ⪯
    (<{{ (make_fn name c_s nil) (nil) }}> )
    [{ fun x y => initial_frame_res [i_t] [i_s] C }].
  Proof.
    iIntros "Hresources #Hcode".

    cbn -[instr_conv denote_code].
    rewrite !bind_ret_l.

    Opaque denote_code.

    process_push.

    rewrite /initial_frame_res.
    rewrite {1} frame_resources_eq.

    iDestruct "Hresources" as "(HC & Halloc & Hdom & Hst)".

    iApply (sim_expr_bupd_mono with "[HC Halloc Hdom]");
      [ | iApply (sim_push_frame' with "Hst") ].
    2, 3: constructor.
    cont.
    rewrite !bind_tau !bind_ret_l.

    iApply sim_expr_tau.

    rewrite !translate_bind !bind_bind !interp_bind.
    iApply sim_expr_bind.
    iDestruct "H" as (??) "H".

    rewrite !interp_translate.

    rewrite -!(eq_itree_interp _ _ eq_Handler_instrE_conv _ _ _
                (ltac:(cbn; reflexivity))).
    change
      (interp (λ (T : Type) (x0 : instr_E T),
            Vis (instrE_conv T x0)
              (@Monad.ret (itree L0) (@Monad_itree L0) T)) ?x)
      with (instr_conv x).
    iAssert (frame_resources_own
               [j_t; i_t] [j_s; i_s] empty_frame empty_frame C)
      with "[H HC]" as "Hi".
    { rewrite /frame_resources_exist; iFrame.
      iDestruct "H" as "(?&?&?&?&?&?&?&?)"; cbn; iFrame.
      iExists nil, nil; cbn; repeat iSplitL; try done;
        iPureIntro; constructor. }

    iPoseProof (code_make_block_contextual with "Hcode") as "Hblock".

    rewrite !denote_ocfg_unfold_eq_itree.
    cbn. destruct_if_goal; destruct_if; cycle 1.
    { exfalso. by apply n. }
    rewrite !instr_conv_bind; iApply sim_expr_bind.

    iApply (sim_expr_bupd_mono with "[Halloc Hdom]"); cycle 1.
    { iAssert (frame_WF [j_t; i_t] [j_s; i_s])%I as "HWF"; first auto.
      iCombine "HWF Hi" as "Hi"; iApply ("Hblock" with "Hi"). }

    iClear "Hblock Hcode".
    cont.
    iDestruct "H" as "((HC & Hbij) & %Hx & %Hy)"; subst.
    rewrite instr_conv_ret.
    iApply sim_expr_base.
    go.

    (* Pop the stack *)
    repeat setoid_rewrite interp_bind.
    setoid_rewrite interp_vis at 2.
    setoid_rewrite bind_bind.

    setoid_rewrite interp_vis at 3.
    setoid_rewrite bind_bind.
    rewrite -bind_bind.
    setoid_rewrite interp_ret.
    iApply sim_expr_bind.
    repeat setoid_rewrite interp_vis; cbn; go.
    repeat setoid_rewrite bind_vis; go.
    repeat setoid_rewrite bind_ret_l.
    setoid_rewrite interp_ret.
    iApply sim_expr_Φ_Proper; last first.
    { iApply (sim_expr_bupd_mono with "[HC Halloc Hdom]"); cycle 1.
      { iDestruct "Hbij" as (??) "Hbij".
        iDestruct "Hbij" as
          "(((Ha_t&Ha_s)&((Hl_t&Hl_s)&(Hs_t&Hs_s)))
            & (HC&H))".
        iDestruct "H" as (??????) "H".

        iPoseProof (sim_pop_frame_bij with
            "Hs_t Hs_s Ha_t Ha_s HC H") as "Hframe"; eauto. }
      iIntros (??) "H".
      iDestruct "H" as (????) "(HC' & Hs_t & Hs_s)".
      rewrite H2 H3 !bind_ret_l.
      rewrite !bind_tau !bind_ret_l.
      iApply sim_expr_tau; iApply sim_expr_base; iFrame.
      iDestruct "Halloc" as "(Ha_t & Ha_s)"; iFrame.
      iDestruct "Hdom" as "(Ha_t & Ha_s)"; by iFrame. }
    { tau_steps. eapply eqit_Vis; eauto.
      intros. destruct u. tau_steps. apply eqit_Tau.
      by setoid_rewrite bind_ret_l. }
    { tau_steps. eapply eqit_Vis; eauto.
      intros. destruct u. tau_steps. apply eqit_Tau.
      by setoid_rewrite bind_ret_l. }
  Qed.

  Definition new_frame args := {| alloca_dom := ∅; local_dom := (list_to_set args) |}.

  Definition local_args_own_target args_name args_val i :=
    ([∗ list] '(l, v) ∈ combine args_name args_val, [ l := v ]t i)%I.

  Definition local_args_own_source args_name args_val i :=
    ([∗ list] '(l, v) ∈ combine args_name args_val, [ l := v ]s i)%I.

  Theorem code_to_fn_contextual_args
    name args c_t c_s i_t i_s C args_t args_s:
    NoDup args ->
    length args = length args_t ->
    length args = length args_s ->
    initial_frame_res [i_t] [i_s] C -∗
    □ (∀ j_t j_s, (frame_WF j_t j_s ∗
          frame_resources_own j_t j_s (new_frame args) (new_frame args) C ∗
        local_args_own_target args args_t j_t ∗
        local_args_own_source args args_s j_s) -∗
        instr_conv (denote_code c_t) ⪯
        instr_conv (denote_code c_s)
      [{ (x, y), frame_WF j_t j_s ∗
                  frame_resources_own_exist j_t j_s C ∗
                  local_args_own_target args args_t j_t ∗
                  local_args_own_source args args_s j_s }]) -∗
    (<{{ (make_fn name c_t args) (args_t) }}> ) ⪯
    (<{{ (make_fn name c_s args) (args_s) }}> )
    [{ fun x y => initial_frame_res [i_t] [i_s] C }].
  Proof.
    iIntros (Hnd Hlen_t Hlen_s) "Hresources #Hcode".

    cbn -[instr_conv denote_code].
    rewrite Hlen_t in Hlen_s.
    rewrite Hlen_t Hlen_s Nat.eqb_refl.
    rewrite !bind_ret_l.

    Opaque denote_code.

    process_push.

    rewrite /initial_frame_res.
    rewrite {1} frame_resources_eq.

    iDestruct "Hresources" as "(HC & Halloc & Hdom & Hst)".

    iApply (sim_expr_bupd_mono with "[HC Halloc Hdom]");
      [ | iApply (sim_push_frame' with "Hst") ].
    2,3: rewrite combine_fst; eauto; by rewrite Hlen_t Hlen_s.
    cont.
    rewrite !bind_tau !bind_ret_l.

    iApply sim_expr_tau.

    rewrite !translate_bind !bind_bind !interp_bind.
    iApply sim_expr_bind.
    iDestruct "H" as (??) "H".

    rewrite !interp_translate.

    rewrite -!(eq_itree_interp _ _ eq_Handler_instrE_conv _ _ _
                (ltac:(cbn; reflexivity))).
    change
      (interp (λ (T : Type) (x0 : instr_E T),
            Vis (instrE_conv T x0)
              (@Monad.ret (itree L0) (@Monad_itree L0) T)) ?x)
      with (instr_conv x).
    iAssert (frame_resources_own
               [j_t; i_t] [j_s; i_s] (new_frame args) (new_frame args) C ∗
        local_args_own_target args args_t [j_t; i_t] ∗
        local_args_own_source args args_s [j_s; i_s])%I
      with "[H HC]" as "Hi".
    { rewrite /frame_resources_exist; iFrame.
      iDestruct "H" as "(?&?&?&?&?&?&?&?)"; cbn; iFrame.
      cbn. rewrite !combine_fst; eauto.
      2 : by rewrite Hlen_t Hlen_s. iFrame.

      iExists nil, nil; cbn; repeat iSplitL; try done;
        iPureIntro; constructor. }

    iPoseProof (code_make_block_contextual with "Hcode") as "Hblock".

    rewrite !denote_ocfg_unfold_eq_itree.
    cbn. destruct_if_goal; destruct_if; cycle 1.
    { exfalso. by apply n. }
    rewrite !instr_conv_bind; iApply sim_expr_bind.

    iApply (sim_expr_bupd_mono with "[Halloc Hdom]"); cycle 1.
    { iAssert (frame_WF [j_t; i_t] [j_s; i_s])%I as "HWF"; first auto.
      iCombine "HWF Hi" as "Hi"; iApply ("Hblock" with "Hi"). }

    iClear "Hblock Hcode".
    cont.
    iDestruct "H" as "((HC & Hbij) & %Hx & %Hy)"; subst.
    rewrite instr_conv_ret.
    iApply sim_expr_base.
    go.

    (* Pop the stack *)
    repeat setoid_rewrite interp_bind.
    setoid_rewrite interp_vis at 2.
    setoid_rewrite bind_bind.

    setoid_rewrite interp_vis at 3.
    setoid_rewrite bind_bind.
    rewrite -bind_bind.
    setoid_rewrite interp_ret.
    iApply sim_expr_bind.
    repeat setoid_rewrite interp_vis; cbn; go.
    repeat setoid_rewrite bind_vis; go.
    repeat setoid_rewrite bind_ret_l.
    setoid_rewrite interp_ret.
    iApply sim_expr_Φ_Proper; last first.
    { iApply (sim_expr_bupd_mono with "[HC Halloc Hdom]"); cycle 1.
      { iDestruct "Hbij" as "(Hbij & Hlv_t & Hlv_s)".
        iDestruct "Hbij" as (??) "Hbij".
        iDestruct "Hbij" as
          "(((Ha_t&Ha_s)&((Hl_t&Hl_s)&(Hs_t&Hs_s)))
            & (HC&H))".
        iDestruct "H" as (??????) "H".

        iPoseProof (sim_pop_frame_bij with
            "Hs_t Hs_s Ha_t Ha_s HC H") as "Hframe"; eauto. }
      iIntros (??) "H".
      iDestruct "H" as (????) "(HC' & Hs_t & Hs_s)".
      rewrite H2 H3 !bind_ret_l.
      rewrite !bind_tau !bind_ret_l.
      iApply sim_expr_tau; iApply sim_expr_base; iFrame.
      iDestruct "Halloc" as "(Ha_t & Ha_s)"; iFrame.
      iDestruct "Hdom" as "(Ha_t & Ha_s)"; by iFrame. }
    { tau_steps. eapply eqit_Vis; eauto.
      intros. destruct u. tau_steps. apply eqit_Tau.
      by setoid_rewrite bind_ret_l. }
    { tau_steps. eapply eqit_Vis; eauto.
      intros. destruct u. tau_steps. apply eqit_Tau.
      by setoid_rewrite bind_ret_l. }
  Qed.

End contextual_properties.

Ltac frame_res_exists :=
  repeat iExists _; repeat (iSplitL ""; first done);
  match goal with
  | [ |- context[environments.Esnoc _ (INamed _) (alloca_tgt _ ?LA)] ] =>
    match goal with
    | [ |- context[environments.Esnoc _ (INamed _) (ldomain_tgt _ ?LD)] ] =>
      iExists ({| alloca_dom := LA; local_dom := LD|})
    end
  end;
  match goal with
  | [ |- context[environments.Esnoc _ (INamed _) (alloca_src _ ?LA')] ] =>
    match goal with
    | [ |- context[environments.Esnoc _ (INamed _) (ldomain_src _ ?LD')] ] =>
      iExists ({| alloca_dom := LA'; local_dom := LD'|}); iFrame
    end
  end.
