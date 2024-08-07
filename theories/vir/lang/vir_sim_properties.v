From iris.prelude Require Import options.

From velliris Require Import vir.lang.spec.
From ITree Require Import Interp.TranslateFacts Events.StateFacts.

(* General properties about the simulation instantiated for [vir]. *)
Section vir_sim_properties.

  Context {Σ} `{!vellirisGS Σ}.

  Lemma sim_expr_exception {R} (e : _ R) s0 Φ:
    ⊢ e ⪯ trigger (Exception.Throw (print_msg s0)) [{ Φ }].
  Proof.
    rewrite sim_expr_eq /sim_expr_.
    iIntros (??) "SI". iModIntro.
    rewrite /interp_L2.
    rewrite StateFacts.interp_state_vis; cbn; rewrite /add_tau.
    cbn; rewrite /pure_state. rewrite bind_tau !bind_vis.
    iApply sim_coind_tauR.
    iApply sim_coind_exc.
  Qed.

  (* TODO: make less redundant with [sim_pick]/ do we need this at all? *)
  Lemma sim_expr_pick fn P:
    ⊢ trigger (pick fn P) ⪯ trigger (pick fn P) [{ (v_t, v_s), ⌜v_t = v_s⌝}].
  Proof.
    rewrite sim_expr_eq /sim_expr_.
    iIntros (??) "SI". iModIntro.
    rewrite /interp_L2.
    rewrite !interp_state_vis.
    rewrite /add_tau; cbn.
    rewrite /lift_undef_or_err.
    rewrite !bind_tau !bind_bind.

    iApply sim_coind_tau; cbn.
    rewrite /lift_undef_or_err.

    destruct (concretize_uvalue fn), unEitherT; [ | destruct s].
    { iApply sim_coind_ub. }
    { iApply sim_coind_exc. }

    rewrite !bind_ret_l !interp_state_ret.
    iApply sim_coind_tau.
    iApply sim_coind_base.
    iFrame.
    iExists _, _; eauto.
  Qed.

  Lemma sim_expr_exception_vis {R R2} (e : _ R) s0 (k : _ -> _ R2) Φ:
    ⊢ e ⪯ vis (Exception.Throw (print_msg s0)) k [{ Φ }].
  Proof.
    rewrite sim_expr_eq /sim_expr_.
    iIntros (??) "SI". iModIntro.
    rewrite /interp_L2.
    rewrite StateFacts.interp_state_vis; cbn; rewrite /add_tau.
    cbn; rewrite /pure_state. rewrite bind_tau !bind_vis.
    iApply sim_coind_tauR.
    iApply sim_coind_exc.
  Qed.

  Lemma sim_expr_UB {R R2} (e : _ R) s0 (k : _ -> _ R2) Φ:
    ⊢ e ⪯ vis (ThrowUB s0) k [{ Φ }].
  Proof.
    rewrite sim_expr_eq /sim_expr_.
    iIntros (??) "SI". iModIntro.
    rewrite /interp_L2.
    rewrite StateFacts.interp_state_vis; cbn; rewrite /add_tau.
    cbn; rewrite /pure_state. rewrite bind_tau !bind_vis.
    iApply sim_coind_tauR.
    iApply sim_coind_ub.
  Qed.

End vir_sim_properties.

Section conv_properties.

  Context {Σ} `{!vellirisGS Σ}.

  Notation st_expr_rel' R1 R2 :=
    (@st_exprO' vir_lang R1 -d> @st_exprO' vir_lang R2 -d> iPropI Σ).

  Lemma eq2_exp_to_L0 :
    eq2 (cat exp_to_instr instrE_conv) exp_to_L0.
  Proof.
    repeat intro.
    rewrite /cat /Cat_IFun.
    destruct a as [ | [ | [ | [ | [ |  ] ] ] ] ]; rewrite /exp_to_instr;
      simp instrE_conv; rewrite /exp_to_L0 /instr_to_L0; auto.
  Qed.

  Lemma exp_conv_to_instr :
    forall T e1 e2 Φ,
      exp_conv e1 ⪯ exp_conv e2 [{ Φ }] -∗
      instr_conv (translate (T := T) exp_to_instr e1) ⪯
      instr_conv (translate (T := T) exp_to_instr e2) [{ Φ }].
  Proof.
    intros.
    iIntros "H".
    rewrite /instr_conv /exp_conv.
    rewrite !interp_translate.
    rewrite (eq_itree_interp
               (λ (T0 : Type) (e : exp_E T0), Vis (instrE_conv T0 (exp_to_instr e)) Monad.ret));
      last done.
    1 : rewrite (eq_itree_interp (λ (T0 : Type) (e : exp_E T0), Vis (instrE_conv T0 (exp_to_instr e)) Monad.ret));
      last done.
    1 : done.
    all: repeat intro; by rewrite -eq2_exp_to_L0.
  Qed.

  Lemma instr_to_L0' {T} e_t e_s Φ :
    instr_conv e_t ⪯ instr_conv e_s ⦉ Φ ⦊ -∗
    L0'expr_conv (translate (T := T) instr_to_L0' e_t) ⪯
    L0'expr_conv (translate (T := T) instr_to_L0' e_s) ⦉ Φ ⦊.
  Proof.
    iIntros "H".
    rewrite /instr_conv /L0'expr_conv.
    rewrite !interp_translate.
    rewrite (eq_itree_interp (λ (T0 : Type) (e : instr_E T0), Vis (call_conv T0 (instr_to_L0' e)) Monad.ret)
               _ _ _ _ e_t);
      [ | | done].
    1 : rewrite (eq_itree_interp (λ (T0 : Type) (e : instr_E T0), Vis (call_conv T0 (instr_to_L0' e)) Monad.ret));
      [ | | done].
    1: done.
    all: repeat intro;
      destruct a; try done;
      destruct s; try done;
      simp call_conv; cbn;
      destruct e; eauto;
      try destruct s; eauto;
      simp call_conv; cbn; eauto;
      repeat destruct s; cbn; try reflexivity.
  Qed.

  Lemma exp_conv_raise {R1 R2} e s (Φ : _ R1 -> _ R2 -> _):
    (⊢ e ⪯ exp_conv (raise s) [{ Φ }])%I.
  Proof.
    rewrite /exp_conv.
    rewrite <- bind_ret_r.
    setoid_rewrite interp_bind. iApply sim_expr_bind.
    rewrite interp_vis.
    rewrite sim_expr_eq /sim_expr_. rewrite /interp_L2.
    iIntros (??) "SI".
    rewrite interp_state_bind.
    rewrite interp_state_vis bind_bind. cbn; rewrite /add_tau;
      cbn; rewrite bind_tau /pure_state; cbn; rewrite !bind_bind bind_vis.
    iApply sim_coind_tauR; iApply sim_coind_exc.
  Qed.

  Lemma exp_conv_raiseUB {R1 R2} e s (Φ : _ R1 -> _ R2 -> _):
    (⊢ e ⪯ exp_conv (raiseUB s) [{ Φ }])%I.
  Proof.
    setoid_rewrite interp_bind.
    rewrite interp_vis.
    rewrite sim_expr_eq /sim_expr_. rewrite /interp_L2.
    iIntros (??) "SI".
    rewrite bind_bind interp_state_bind interp_state_vis; cbn; rewrite /add_tau;
      cbn; rewrite bind_tau /pure_state; cbn; rewrite !bind_bind bind_tau !bind_vis.
    iApply sim_coind_tauR; iApply sim_coind_ub.
  Qed.

  Lemma instr_conv_raise {R1 R2} e s (Φ : _ R1 -> _ R2 -> _):
    (⊢ e ⪯ instr_conv (raise s) [{ Φ }])%I.
  Proof.
    rewrite /instr_conv.
    rewrite <- bind_ret_r.
    setoid_rewrite interp_bind. iApply sim_expr_bind.
    rewrite interp_vis.
    rewrite sim_expr_eq /sim_expr_. rewrite /interp_L2.
    iIntros (??) "SI".
    rewrite interp_state_bind interp_state_vis; cbn; rewrite /add_tau;
      cbn; rewrite bind_tau /pure_state; cbn;
      rewrite !bind_bind bind_vis bind_tau bind_vis.
    iApply sim_coind_tauR; iApply sim_coind_exc.
  Qed.

  Lemma instr_conv_raiseUB {R1 R2} e s (Φ : _ R1 -> _ R2 -> _):
    (⊢ e ⪯ instr_conv (raiseUB s) [{ Φ }])%I.
  Proof.
    rewrite /instr_conv.
    setoid_rewrite interp_bind.
    rewrite interp_vis.
    rewrite sim_expr_eq /sim_expr_. rewrite /interp_L2.
    iIntros (??) "SI".
    rewrite !interp_state_bind bind_bind interp_state_vis bind_bind.
    rewrite /add_tau;
      cbn; rewrite bind_tau /pure_state; cbn -[state_interp].
    rewrite !bind_bind !bind_vis.
    iApply sim_coind_tauR; iApply sim_coind_ub.
  Qed.

  Lemma sim_pick (v_t v_s : uvalue) f_t f_s
    (Φ : expr vir_lang dvalue -> expr vir_lang dvalue -> iPropI Σ):
    uval_rel v_t v_s -∗
    trigger (pick v_t f_t) ⪯ trigger (pick v_s f_s)
    [{ (dv_t, dv_s), dval_rel dv_t dv_s }].
  Proof.
    iIntros "Hv".

    rewrite sim_expr_eq /sim_expr_.
    iIntros (??) "SI".

    rewrite /interp_L2 /instr_conv /concretize_or_pick.
    rewrite !interp_state_vis; cbn.
    rewrite /add_tau; cbn.
    rewrite /lift_undef_or_err; cbn.
    rewrite !bind_tau !bind_bind.
    iApply sim_coind_tau.

    destruct (concretize_uvalue v_s) eqn: Hv_s.
    destruct unEitherT; [ | destruct s].

    { (* UB case*)
      setoid_rewrite bind_vis; iApply sim_coind_ub. }
    { (* Exc case*)
      setoid_rewrite bind_vis; iApply sim_coind_exc. }

    iSpecialize ("Hv" $! _ Hv_s).
    iDestruct "Hv" as (??) "Hv". rewrite H; cbn.

    rewrite !bind_ret_l !interp_state_ret.
    iApply sim_coind_tau; iApply sim_coind_base; iFrame;
      iExists _, _; do 2 (iSplitL ""; [ done | ]); done.
  Qed.

  Lemma exp_conv_concretize_or_pick v_t v_s P_t P_s:
    uval_rel v_t v_s -∗
    exp_conv (concretize_or_pick v_t P_t) ⪯ exp_conv (concretize_or_pick v_s P_s)
    [{ (dv_t, dv_s), dval_rel dv_t dv_s }].
  Proof.
    iIntros "Hv".
    rewrite sim_expr_eq /sim_expr_.
    iIntros (??) "SI".

    rewrite /interp_L2 /exp_conv /concretize_or_pick.
    (* If both are concrete, that's fine *)
    destruct (is_concrete v_s) eqn: Hvs.
    { apply Is_true_eq_left in Hvs.
      apply is_concrete_concretize_uvalue in Hvs.
      destruct Hvs as (?&?&?); subst.
      iSpecialize ("Hv" $! _ H).
      iDestruct "Hv" as (??) "Hv".
      rewrite uvalue_to_dvalue_of_dvalue_to_uvalue.

      destruct (is_concrete v_t) eqn: Hvt.
      { apply Is_true_eq_left in Hvt.
        apply is_concrete_concretize_uvalue in Hvt.
        destruct Hvt as (?&?&?); subst. rewrite H1 in H0.
        inversion H0. rewrite uvalue_to_dvalue_of_dvalue_to_uvalue.
        rewrite /lift_err.
        iApply sim_coind_Proper.
        { cbn; rewrite interp_ret interp_state_ret; reflexivity. }
        { cbn; rewrite interp_ret interp_state_ret; reflexivity. }
        iApply sim_coind_base; iFrame.
        iExists _, _; iFrame; cbn; iSplitL ""; done. }
      { iApply sim_coind_Proper.
        { cbn; rewrite interp_vis bind_trigger; cbn.
          rewrite interp_state_vis; cbn.
          rewrite /add_tau; cbn; rewrite /lift_undef_or_err.
          rewrite bind_tau bind_bind.
          setoid_rewrite bind_ret_l.
          setoid_rewrite interp_state_tau; cbn.
          setoid_rewrite interp_ret.
          setoid_rewrite interp_state_ret; cbn.
          reflexivity. }
        { cbn; rewrite interp_ret interp_state_ret; reflexivity. }
        rewrite H0; cbn -[state_interp].

        iApply sim_coind_Proper; [ | reflexivity | ].
        { rewrite bind_ret_l; reflexivity. }

        do 3 iApply sim_coind_tauL; iApply sim_coind_base; iFrame.
        iExists _, _; iFrame; cbn; iSplitL ""; done. } }

    (* [v_s] not concrete *)
    destruct (is_concrete v_t) eqn: Hvt.
    { (* Problem : v_s is not concrete, v_t is concrete *)
      apply Is_true_eq_left in Hvt.
      apply is_concrete_concretize_uvalue in Hvt.
      destruct Hvt as (?&?&?); subst.
      iApply sim_coind_Proper.
      { rewrite /lift_err; cbn.
        rewrite uvalue_to_dvalue_of_dvalue_to_uvalue.
        rewrite interp_ret interp_state_ret; reflexivity. }
      { cbn; rewrite interp_vis bind_vis interp_state_vis; cbn.
        rewrite /add_tau; cbn; rewrite /lift_undef_or_err.
        rewrite bind_tau bind_bind.
        setoid_rewrite bind_ret_l.
        setoid_rewrite interp_ret.
        cbn. setoid_rewrite interp_state_bind.
        setoid_rewrite interp_state_ret; cbn.
        setoid_rewrite bind_ret_l.
        setoid_rewrite interp_state_tau.
        setoid_rewrite interp_state_ret; cbn.
        reflexivity. }

      iApply sim_coind_tauR.
      destruct (concretize_uvalue v_s) eqn: Hconc_v_s; destruct unEitherT; [ | destruct s].
      { iApply sim_coind_Proper; [ reflexivity | | ].
        { do 2 setoid_rewrite bind_vis; reflexivity. }
        iApply sim_coind_ub. }
      { iApply sim_coind_Proper; [ reflexivity | | ].
        { do 2 setoid_rewrite bind_vis; reflexivity. }
        iApply sim_coind_exc. }
      iApply sim_coind_Proper; [ reflexivity | by rewrite bind_ret_l | ].
      do 2 iApply sim_coind_tauR.
      iApply sim_coind_base; iFrame.
      iSpecialize ("Hv" $! _ Hconc_v_s).
      iDestruct "Hv" as (??) "Hv".
      rewrite concretize_uvalue_dvalue_to_uvalue in H0; inversion H0; subst.
      iExists _, _; iFrame; eauto. }

    (* both not concrete *)
    iApply sim_coind_Proper.
    { cbn; rewrite interp_vis bind_vis interp_state_vis; cbn.
      rewrite /add_tau; cbn.
      rewrite /lift_undef_or_err; cbn.
      rewrite bind_tau bind_bind.
      reflexivity. }
    { cbn; rewrite interp_vis bind_vis interp_state_vis; cbn.
      rewrite /add_tau; cbn.
      rewrite /lift_undef_or_err; cbn.
      rewrite bind_tau bind_bind.
      reflexivity. }
    iApply sim_coind_tau.

    destruct (concretize_uvalue v_s) eqn: Hv_s.
    destruct unEitherT eqn: H; [  | destruct s].

    { (* UB case*)
      iApply sim_coind_Proper; [ reflexivity | | ].
      { setoid_rewrite bind_vis. reflexivity. }
      iApply sim_coind_ub. }
    { (* Exc case*)
      iApply sim_coind_Proper; [ reflexivity | | ].
      { setoid_rewrite bind_vis. reflexivity. }
      iApply sim_coind_exc. }

    iSpecialize ("Hv" $! _ Hv_s).
    iDestruct "Hv" as (??) "Hv"; rewrite H0; cbn -[state_interp].
    iApply sim_coind_Proper;
    [ repeat rewrite bind_ret_l; by rewrite interp_ret interp_state_tau interp_state_ret |
      repeat rewrite bind_ret_l; by rewrite interp_ret interp_state_tau interp_state_ret |].
    do 2 iApply sim_coind_tau; iApply sim_coind_base; iFrame;
      iExists _, _; do 2 (iSplitL ""; [ done | ]); done.
  Qed.

  Lemma determine_uvalue_dvalue_to_uvalue v:
    determine_uvalue (dvalue_to_uvalue v) v.
  Proof.
    rewrite /determine_uvalue.
    rewrite is_concrete_dvalue_to_uvalue.
    by rewrite uvalue_to_dvalue_of_dvalue_to_uvalue.
  Qed.

  Lemma L0_conv_concretize_or_pick_strong v_t v_s P_t P_s:
    uval_rel v_t v_s -∗
    L0'expr_conv (concretize_or_pick v_t P_t) ⪯ L0'expr_conv (concretize_or_pick v_s P_s)
    [{ (dv_t, dv_s), dval_rel dv_t dv_s ∗
          ⌜determine_uvalue v_t dv_t⌝ ∗ ⌜determine_uvalue v_s dv_s⌝}].
  Proof.
    iIntros "Hv".
    rewrite sim_expr_eq /sim_expr_.
    iIntros (??) "SI".

    rewrite /interp_L2 /L0'expr_conv /concretize_or_pick.
    (* If both are concrete, that's fine *)
    destruct (is_concrete v_s) eqn: Hvs.
    { apply Is_true_eq_left in Hvs.
      apply is_concrete_concretize_uvalue in Hvs.
      destruct Hvs as (?&?&?); subst.
      iSpecialize ("Hv" $! _ H).
      iDestruct "Hv" as (??) "Hv".
      rewrite uvalue_to_dvalue_of_dvalue_to_uvalue.

      destruct (is_concrete v_t) eqn: Hvt.
      { apply Is_true_eq_left in Hvt.
        apply is_concrete_concretize_uvalue in Hvt.
        destruct Hvt as (?&?&?); subst. rewrite H1 in H0.
        inversion H0. rewrite uvalue_to_dvalue_of_dvalue_to_uvalue.
        rewrite /lift_err.
        iApply sim_coind_Proper.
        { cbn; rewrite interp_ret interp_state_ret; reflexivity. }
        { cbn; rewrite interp_ret interp_state_ret; reflexivity. }
        iApply sim_coind_base; iFrame.
        iExists _, _; iFrame; cbn; subst; repeat iSplitL ""; try done;
          iPureIntro; apply determine_uvalue_dvalue_to_uvalue. }
      { iApply sim_coind_Proper.
        { cbn; rewrite interp_vis bind_trigger interp_state_vis; cbn.
          rewrite /add_tau; cbn; rewrite /lift_undef_or_err.
          rewrite bind_tau bind_bind.
          setoid_rewrite bind_ret_l.
          setoid_rewrite interp_ret.
          setoid_rewrite interp_state_tau.
          setoid_rewrite interp_state_ret; cbn.
          reflexivity. }
        { cbn; rewrite interp_ret interp_state_ret; reflexivity. }
        rewrite H0; cbn -[state_interp].

        iApply sim_coind_Proper; [ | reflexivity | ].
        { rewrite bind_ret_l ; reflexivity. }

        do 3 iApply sim_coind_tauL; iApply sim_coind_base; iFrame.
        iExists _, _; iFrame; cbn; repeat iSplitL ""; try done; subst;
          [ | iPureIntro; apply determine_uvalue_dvalue_to_uvalue ].
        iPureIntro. rewrite /determine_uvalue.
        by rewrite Hvt. } }
    (* [v_s] not concrete *)
    destruct (is_concrete v_t) eqn: Hvt.
    { (* Problem : v_s is not concrete, v_t is concrete *)
      apply Is_true_eq_left in Hvt.
      apply is_concrete_concretize_uvalue in Hvt.
      destruct Hvt as (?&?&?); subst.
      iApply sim_coind_Proper.
      { rewrite /lift_err; cbn.
        rewrite uvalue_to_dvalue_of_dvalue_to_uvalue.
        rewrite interp_ret interp_state_ret; reflexivity. }
      { cbn; rewrite interp_vis bind_trigger interp_state_vis; cbn.
        rewrite /add_tau; cbn; rewrite /lift_undef_or_err.
        rewrite bind_tau bind_bind.
        setoid_rewrite bind_ret_l.
        setoid_rewrite interp_ret.
        setoid_rewrite interp_state_tau; cbn.
        setoid_rewrite interp_state_ret; cbn.
        reflexivity. }

      iApply sim_coind_tauR.
      destruct (concretize_uvalue v_s) eqn: Hconc_v_s; destruct unEitherT; [ | destruct s].
      { iApply sim_coind_Proper; [ reflexivity | | ].
        { do 2 setoid_rewrite bind_vis; reflexivity. }
        iApply sim_coind_ub. }
      { iApply sim_coind_Proper; [ reflexivity | | ].
        { do 2 setoid_rewrite bind_vis; reflexivity. }
        iApply sim_coind_exc. }
      iApply sim_coind_Proper; [ reflexivity | by rewrite bind_ret_l | ].
      do 2 iApply sim_coind_tauR.
      iApply sim_coind_base; iFrame.
      iSpecialize ("Hv" $! _ Hconc_v_s).
      iDestruct "Hv" as (??) "Hv".
      rewrite concretize_uvalue_dvalue_to_uvalue in H0; inversion H0; subst.
      iExists _, _; iFrame; eauto.
      try repeat iSplitL""; try done;
          [ iPureIntro; apply determine_uvalue_dvalue_to_uvalue | ].
      iPureIntro. rewrite /determine_uvalue. by rewrite Hvs. }

    (* both not concrete *)
    iApply sim_coind_Proper.
    { cbn; rewrite interp_vis bind_vis interp_state_vis; cbn.
      rewrite /add_tau; cbn.
      rewrite /lift_undef_or_err; cbn.
      rewrite bind_tau bind_bind.
      rewrite /concretize_picks; cbn.
      rewrite /lift_undef_or_err; cbn.
      reflexivity. }
    { cbn; rewrite interp_vis bind_vis interp_state_vis; cbn.
      rewrite /add_tau; cbn.
      rewrite /lift_undef_or_err; cbn.
      rewrite bind_tau bind_bind.
      rewrite /concretize_picks; cbn.
      rewrite /lift_undef_or_err; cbn.
      reflexivity. }
    iApply sim_coind_tau.

    destruct (concretize_uvalue v_s) eqn: Hv_s.

    destruct unEitherT eqn: H; [  | destruct s].

    { (* UB case*)
      iApply sim_coind_Proper; [ reflexivity | | ].
      { setoid_rewrite bind_vis. reflexivity. }
      iApply sim_coind_ub. }
    { (* Exc case*)
      iApply sim_coind_Proper; [ reflexivity | | ].
      { setoid_rewrite bind_vis. reflexivity. }
      iApply sim_coind_exc. }

    iSpecialize ("Hv" $! _ Hv_s).
    iDestruct "Hv" as (??) "Hv"; rewrite H0; cbn -[state_interp].
    iApply sim_coind_Proper;
    [ repeat rewrite bind_ret_l;
        rewrite interp_ret interp_state_tau interp_state_ret; by cbn |
      repeat rewrite bind_ret_l;
        rewrite interp_ret interp_state_tau interp_state_ret; by cbn | ];
    do 2 iApply sim_coind_tau; iApply sim_coind_base; iFrame;
      iExists _, _; do 2 (iSplitL ""; [ done | ]); try done; iFrame.
    cbn.

    rewrite /determine_uvalue; rewrite Hvs Hvt. iSplitL ""; done.
  Qed.

  Lemma instr_conv_concretize_or_pick_strong v_t v_s P_t P_s:
    uval_rel v_t v_s -∗
    instr_conv (concretize_or_pick v_t P_t) ⪯ instr_conv (concretize_or_pick v_s P_s)
    [{ (dv_t, dv_s), dval_rel dv_t dv_s ∗
          ⌜determine_uvalue v_t dv_t⌝ ∗ ⌜determine_uvalue v_s dv_s⌝}].
  Proof.
    iIntros "Hv".
    rewrite sim_expr_eq /sim_expr_.
    iIntros (??) "SI".

    rewrite /interp_L2 /instr_conv /concretize_or_pick.
    (* If both are concrete, that's fine *)
    destruct (is_concrete v_s) eqn: Hvs.
    { apply Is_true_eq_left in Hvs.
      apply is_concrete_concretize_uvalue in Hvs.
      destruct Hvs as (?&?&?); subst.
      iSpecialize ("Hv" $! _ H).
      iDestruct "Hv" as (??) "Hv".
      rewrite uvalue_to_dvalue_of_dvalue_to_uvalue.

      destruct (is_concrete v_t) eqn: Hvt.
      { apply Is_true_eq_left in Hvt.
        apply is_concrete_concretize_uvalue in Hvt.
        destruct Hvt as (?&?&?); subst. rewrite H1 in H0.
        inversion H0. rewrite uvalue_to_dvalue_of_dvalue_to_uvalue.
        rewrite /lift_err.
        iApply sim_coind_Proper.
        { cbn; rewrite interp_ret interp_state_ret; reflexivity. }
        { cbn; rewrite interp_ret interp_state_ret; reflexivity. }
        iApply sim_coind_base; iFrame.
        iExists _, _; iFrame; cbn; subst; repeat iSplitL ""; try done;
          iPureIntro; apply determine_uvalue_dvalue_to_uvalue. }
      { iApply sim_coind_Proper.
        { cbn; rewrite interp_vis bind_trigger interp_state_vis; cbn.
          rewrite /add_tau; cbn; rewrite /lift_undef_or_err.
          rewrite bind_tau bind_bind.
          setoid_rewrite bind_ret_l.
          setoid_rewrite interp_ret.
          setoid_rewrite interp_state_tau.
          setoid_rewrite interp_state_ret; cbn.
          reflexivity. }
        { cbn; rewrite interp_ret interp_state_ret; reflexivity. }
        rewrite H0; cbn -[state_interp].

        iApply sim_coind_Proper; [ | reflexivity | ].
        { rewrite bind_ret_l ; reflexivity. }

        do 3 iApply sim_coind_tauL; iApply sim_coind_base; iFrame.
        iExists _, _; iFrame; cbn; repeat iSplitL ""; try done; subst;
          [ | iPureIntro; apply determine_uvalue_dvalue_to_uvalue ].
        iPureIntro. rewrite /determine_uvalue.
        by rewrite Hvt. } }
    (* [v_s] not concrete *)
    destruct (is_concrete v_t) eqn: Hvt.
    { (* Problem : v_s is not concrete, v_t is concrete *)
      apply Is_true_eq_left in Hvt.
      apply is_concrete_concretize_uvalue in Hvt.
      destruct Hvt as (?&?&?); subst.
      iApply sim_coind_Proper.
      { rewrite /lift_err; cbn.
        rewrite uvalue_to_dvalue_of_dvalue_to_uvalue.
        rewrite interp_ret interp_state_ret; reflexivity. }
      { cbn; rewrite interp_vis bind_trigger interp_state_vis; cbn.
        rewrite /add_tau; cbn; rewrite /lift_undef_or_err.
        rewrite bind_tau bind_bind.
        setoid_rewrite bind_ret_l.
        setoid_rewrite interp_ret.
        setoid_rewrite interp_state_tau; cbn.
        setoid_rewrite interp_state_ret; cbn.
        reflexivity. }

      iApply sim_coind_tauR.
      destruct (concretize_uvalue v_s) eqn: Hconc_v_s; destruct unEitherT; [ | destruct s].
      { iApply sim_coind_Proper; [ reflexivity | | ].
        { do 2 setoid_rewrite bind_vis; reflexivity. }
        iApply sim_coind_ub. }
      { iApply sim_coind_Proper; [ reflexivity | | ].
        { do 2 setoid_rewrite bind_vis; reflexivity. }
        iApply sim_coind_exc. }
      iApply sim_coind_Proper; [ reflexivity | by rewrite bind_ret_l | ].
      do 2 iApply sim_coind_tauR.
      iApply sim_coind_base; iFrame.
      iSpecialize ("Hv" $! _ Hconc_v_s).
      iDestruct "Hv" as (??) "Hv".
      rewrite concretize_uvalue_dvalue_to_uvalue in H0; inversion H0; subst.
      iExists _, _; iFrame; eauto.
      try repeat iSplitL""; try done;
          [ iPureIntro; apply determine_uvalue_dvalue_to_uvalue | ].
      iPureIntro. rewrite /determine_uvalue. by rewrite Hvs. }

    (* both not concrete *)
    iApply sim_coind_Proper.
    { cbn; rewrite interp_vis bind_vis interp_state_vis; cbn.
      rewrite /add_tau; cbn.
      rewrite /lift_undef_or_err; cbn.
      rewrite bind_tau bind_bind.
      rewrite /concretize_picks; cbn.
      rewrite /lift_undef_or_err; cbn.
      reflexivity. }
    { cbn; rewrite interp_vis bind_vis interp_state_vis; cbn.
      rewrite /add_tau; cbn.
      rewrite /lift_undef_or_err; cbn.
      rewrite bind_tau bind_bind.
      rewrite /concretize_picks; cbn.
      rewrite /lift_undef_or_err; cbn.
      reflexivity. }
    iApply sim_coind_tau.

    destruct (concretize_uvalue v_s) eqn: Hv_s.

    destruct unEitherT eqn: H; [  | destruct s].

    { (* UB case*)
      iApply sim_coind_Proper; [ reflexivity | | ].
      { setoid_rewrite bind_vis. reflexivity. }
      iApply sim_coind_ub. }
    { (* Exc case*)
      iApply sim_coind_Proper; [ reflexivity | | ].
      { setoid_rewrite bind_vis. reflexivity. }
      iApply sim_coind_exc. }

    iSpecialize ("Hv" $! _ Hv_s).
    iDestruct "Hv" as (??) "Hv"; rewrite H0; cbn -[state_interp].
    iApply sim_coind_Proper;
    [ repeat rewrite bind_ret_l;
        rewrite interp_ret interp_state_tau interp_state_ret; by cbn |
      repeat rewrite bind_ret_l;
        rewrite interp_ret interp_state_tau interp_state_ret; by cbn | ];
    do 2 iApply sim_coind_tau; iApply sim_coind_base; iFrame;
      iExists _, _; do 2 (iSplitL ""; [ done | ]); try done; iFrame.
    cbn.

    rewrite /determine_uvalue; rewrite Hvs Hvt. iSplitL ""; done.
  Qed.

  Lemma instr_conv_concretize_or_pick v_t v_s P_t P_s:
    uval_rel v_t v_s -∗
    instr_conv (concretize_or_pick v_t P_t) ⪯ instr_conv (concretize_or_pick v_s P_s)
    [{ (dv_t, dv_s), dval_rel dv_t dv_s }].
  Proof.
    iIntros "Hv".
    rewrite sim_expr_eq /sim_expr_.
    iIntros (??) "SI".

    rewrite /interp_L2 /instr_conv /concretize_or_pick.
    (* If both are concrete, that's fine *)
    destruct (is_concrete v_s) eqn: Hvs.
    { apply Is_true_eq_left in Hvs.
      apply is_concrete_concretize_uvalue in Hvs.
      destruct Hvs as (?&?&?); subst.
      iSpecialize ("Hv" $! _ H).
      iDestruct "Hv" as (??) "Hv".
      rewrite uvalue_to_dvalue_of_dvalue_to_uvalue.

      destruct (is_concrete v_t) eqn: Hvt.
      { apply Is_true_eq_left in Hvt.
        apply is_concrete_concretize_uvalue in Hvt.
        destruct Hvt as (?&?&?); subst. rewrite H1 in H0.
        inversion H0. rewrite uvalue_to_dvalue_of_dvalue_to_uvalue.
        rewrite /lift_err.
        iApply sim_coind_Proper.
        { cbn; rewrite interp_ret interp_state_ret; reflexivity. }
        { cbn; rewrite interp_ret interp_state_ret; reflexivity. }
        iApply sim_coind_base; iFrame.
        iExists _, _; iFrame; cbn; iSplitL ""; done. }
      { iApply sim_coind_Proper.
        { cbn; rewrite interp_vis bind_trigger interp_state_vis; cbn.
          rewrite /add_tau; cbn; rewrite /lift_undef_or_err.
          rewrite bind_tau bind_bind.
          setoid_rewrite bind_ret_l.
          setoid_rewrite interp_ret.
          setoid_rewrite interp_state_tau; cbn.
          setoid_rewrite interp_state_ret; cbn.
          reflexivity. }
        { cbn; rewrite interp_ret interp_state_ret; reflexivity. }
        rewrite H0; cbn -[state_interp].

        iApply sim_coind_Proper; [ | reflexivity | ].
        { rewrite bind_ret_l; reflexivity. }

        do 3 iApply sim_coind_tauL; iApply sim_coind_base; iFrame.
        iExists _, _; iFrame; cbn; iSplitL ""; done. } }

    (* [v_s] not concrete *)
    destruct (is_concrete v_t) eqn: Hvt.
    { (* Problem : v_s is not concrete, v_t is concrete *)
      apply Is_true_eq_left in Hvt.
      apply is_concrete_concretize_uvalue in Hvt.
      destruct Hvt as (?&?&?); subst.
      iApply sim_coind_Proper.
      { rewrite /lift_err; cbn.
        rewrite uvalue_to_dvalue_of_dvalue_to_uvalue.
        rewrite interp_ret interp_state_ret; reflexivity. }
      { cbn; rewrite interp_vis bind_trigger interp_state_vis; cbn.
        rewrite /add_tau; cbn; rewrite /lift_undef_or_err.
        rewrite bind_tau bind_bind.
        setoid_rewrite bind_ret_l.
        setoid_rewrite interp_ret.
        setoid_rewrite interp_state_tau; cbn.
        setoid_rewrite interp_state_ret; cbn.
        reflexivity. }

      iApply sim_coind_tauR.
      destruct (concretize_uvalue v_s) eqn: Hconc_v_s; destruct unEitherT; [ | destruct s].
      { iApply sim_coind_Proper; [ reflexivity | | ].
        { do 2 setoid_rewrite bind_vis; reflexivity. }
        iApply sim_coind_ub. }
      { iApply sim_coind_Proper; [ reflexivity | | ].
        { do 2 setoid_rewrite bind_vis; reflexivity. }
        iApply sim_coind_exc. }
      iApply sim_coind_Proper; [ reflexivity | by rewrite bind_ret_l | ].
      do 2 iApply sim_coind_tauR.
      iApply sim_coind_base; iFrame.
      iSpecialize ("Hv" $! _ Hconc_v_s).
      iDestruct "Hv" as (??) "Hv".
      rewrite concretize_uvalue_dvalue_to_uvalue in H0; inversion H0; subst.
      iExists _, _; iFrame; eauto. }

    (* both not concrete *)
    iApply sim_coind_Proper.
    { cbn; rewrite interp_vis bind_vis interp_state_vis; cbn.
      rewrite /add_tau; cbn.
      rewrite /lift_undef_or_err; cbn.
      rewrite bind_tau bind_bind.
      rewrite /concretize_picks; cbn.
      rewrite /lift_undef_or_err; cbn.
      reflexivity. }
    { cbn; rewrite interp_vis bind_vis interp_state_vis; cbn.
      rewrite /add_tau; cbn.
      rewrite /lift_undef_or_err; cbn.
      rewrite bind_tau bind_bind.
      rewrite /concretize_picks; cbn.
      rewrite /lift_undef_or_err; cbn.
      reflexivity. }
    iApply sim_coind_tau.

    destruct (concretize_uvalue v_s) eqn: Hv_s.

    destruct unEitherT eqn: H; [  | destruct s].

    { (* UB case*)
      iApply sim_coind_Proper; [ reflexivity | | ].
      { setoid_rewrite bind_vis. reflexivity. }
      iApply sim_coind_ub. }
    { (* Exc case*)
      iApply sim_coind_Proper; [ reflexivity | | ].
      { setoid_rewrite bind_vis. reflexivity. }
      iApply sim_coind_exc. }

    iSpecialize ("Hv" $! _ Hv_s).
    iDestruct "Hv" as (??) "Hv"; rewrite H0; cbn -[state_interp].
    iApply sim_coind_Proper;
    [ repeat rewrite bind_ret_l;
        rewrite interp_ret interp_state_tau interp_state_ret; by cbn |
      repeat rewrite bind_ret_l;
        rewrite interp_ret interp_state_tau interp_state_ret; by cbn | ];
    do 2 iApply sim_coind_tau; iApply sim_coind_base; iFrame;
      iExists _, _; do 2 (iSplitL ""; [ done | ]); done.
  Qed.

  Lemma state_interp_null_bij σ_t σ_s :
    state_interp σ_t σ_s -∗
      Addr.null ↔h Addr.null ∗ state_interp σ_t σ_s.
  Proof.
    iIntros "SI".
    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & %Hbij_WF & SI)".
    iDestruct "SI" as "(#N & SI)". iFrame.
    iSplitL ""; [done | ].
    repeat iExists _; iFrame; by iSplitL "".
  Qed.

  Lemma sim_null_bij {R1 R2} (e_t : _ R1) (e_s : _ R2) Φ:
    (Addr.null ↔h Addr.null -∗ e_t ⪯ e_s [{ Φ }]) -∗
    e_t ⪯ e_s [{ Φ }].
  Proof.
    iIntros "H".
    iApply sim_update_si.
    iIntros (??) "SI".
    iDestruct (state_interp_null_bij with "SI") as "(#Hnull&SI)".
    iSpecialize ("H" with "Hnull").
    by iFrame.
  Qed.

End conv_properties.
