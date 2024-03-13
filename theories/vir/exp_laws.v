

Section exp_laws.

  Lemma source_red_denote_exp_i32 x:
    ⊢ source_red (exp_conv (denote_exp (Some (i32)) (EXP_Integer x)))
      (lift_unary_post
        (λ uv : Handlers.LLVMEvents.DV.uvalue,
        ⌜Handlers.LLVMEvents.DV.is_concrete uv⌝ ∗
        ⌜(DVALUE_I32 (DynamicValues.Int32.repr x)) ̂ = uv⌝ ∗
        ⌜Handlers.LLVMEvents.DV.dvalue_has_dtyp
        (DVALUE_I32 (DynamicValues.Int32.repr x)) (i32)⌝))%I.
  Proof.
    cbn. rewrite source_red_eq_itree; last apply exp_conv_ret.
    iApply source_red_base. unary_post.
    cbn. repeat (iSplitL ""; first done). iPureIntro. constructor.
  Qed.

  Lemma target_red_denote_exp_i32 x:
    ⊢ target_red (exp_conv (denote_exp (Some (i32)) (EXP_Integer x)))
      (lift_unary_post
        (λ uv : Handlers.LLVMEvents.DV.uvalue,
        ⌜Handlers.LLVMEvents.DV.is_concrete uv⌝ ∗
        ⌜(DVALUE_I32 (DynamicValues.Int32.repr x)) ̂ = uv⌝ ∗
        ⌜Handlers.LLVMEvents.DV.dvalue_has_dtyp
        (DVALUE_I32 (DynamicValues.Int32.repr x)) (i32)⌝))%I.
  Proof.
    cbn. rewrite target_red_eq_itree; last apply exp_conv_ret.
    iApply target_red_base. unary_post.
    cbn. repeat (iSplitL ""; first done). iPureIntro. constructor.
  Qed.

  Lemma sim_local_read_exp_conv x_t x_s v_t v_s i_t i_s :
    stack_tgt i_t -∗
    stack_src i_s -∗
    [ x_t := v_t ]t i_t -∗
    [ x_s := v_s ]s i_s -∗
    exp_conv (translate LU_to_exp (trigger (LLVMEvents.LocalRead x_t)))
    ⪯
    exp_conv (translate LU_to_exp (trigger (LLVMEvents.LocalRead x_s)))
    [{ (r_t, r_s), ⌜r_t = v_t⌝ ∗ ⌜r_s = v_s⌝ ∗
        stack_tgt i_t ∗ stack_src i_s ∗
        [ x_t := v_t ]t i_t ∗ [ x_s := v_s ]s i_s  }].
  Proof.
    iIntros "Hs_t Hs_s Ht Hs".
    rewrite /exp_conv.
    rewrite !translate_vis.
    rewrite !interp_vis.
    iApply sim_expr_bind.
    rewrite {3 4} /exp_to_L0
      {3 4} /LU_to_exp /subevent; unfold_cat.
    iApply sim_expr_vis.

    iApply sim_expr_bupd_mono; cycle 1.
    { iPoseProof (sim_local_read with "Ht Hs Hs_t Hs_s") as "H".
      rewrite /ITree.trigger /subevent; unfold_cat.
      iApply "H". }

    cont.
    iDestruct "H" as (??) "(Ht & Hs & Hs_t & Hs_s)"; subst.
    iApply sim_expr_base.
    rewrite !bind_ret_l !translate_ret.
    rewrite !interp_ret.
    iApply sim_expr_tau.
    iApply sim_expr_base.
    iExists _, _; iFrame.
    iSplitL ""; done.
  Qed.

End exp_laws.
