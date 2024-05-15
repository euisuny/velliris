From iris.prelude Require Import options.

From velliris.vir.lang Require Import lang.
From velliris.vir.rules Require Import rules.
From velliris.vir.logrel Require Import logical_relations.

Set Default Proof Using "Type*".

Import ListNotations.
Import SemNotations.
Import LLVMAst.

(** *Reflexivity theorems for logical relations *)
Section fundamental_exp.

  Context {Σ : gFunctors} `{!vellirisGS Σ}.

  Ltac exp_logrel_pre d :=
    destruct d; try iApply exp_conv_raise.

  Ltac exp_logrel_ret :=
    setoid_rewrite interp_ret; iApply sim_expr_base; iExists _, _; iFrame;
    iSplitL ""; [ | iSplitL ""]; try (iPureIntro; reflexivity);
      iApply uval_rel_lift; eauto;
      rewrite unfold_dval_rel; auto.

  Ltac exp_logrel_num dt d :=
    exp_logrel_pre dt; exp_logrel_pre d; exp_logrel_ret;
    iExists _, _; do 2 (iSplitL ""; [ by iPureIntro | ]);
      cbn; eauto.

  (* ------------------------------------------------------------------------ *)

  Lemma expr_logrel_EXP_Ident :
    forall (id : LLVMAst.ident) (dt : option dtyp) i_t i_s L_t L_s,
      local_bij_at_exp (EXP_Ident id) (EXP_Ident id : exp uvalue) i_t i_s L_t L_s
      -∗
      exp_conv (denote_exp dt (EXP_Ident id)) ⪯
      exp_conv (denote_exp dt (EXP_Ident id))
      [{ (v_t, v_s),
          uval_rel v_t v_s ∗
      local_bij_at_exp (EXP_Ident id) (EXP_Ident id : exp uvalue) i_t i_s L_t L_s }].
  Proof with vsimp.
    iIntros (id dt i_t i_s L_t L_s) "HC"; cbn.
    rewrite /lookup_id; destruct id; cbn.
    { (* Global *)
      rewrite /exp_conv interp_translate interp_bind interp_vis.
      vsimp. Cut...
      iApply sim_expr_vis.
      mono: iApply sim_global_read with "[HC]"...
      final...
      iApply sim_expr_base... vsimp.
      rewrite !bind_tau. Tau...
      do 2 (rewrite !interp_ret; vsimp).
      vfinal.
      iApply (dval_rel_lift with "HΦ"). }
    { (* Local *)
      rewrite /exp_conv.

      rewrite interp_translate interp_vis.
      setoid_rewrite InterpFacts.interp_ret.
      rewrite bind_trigger.
      iApply sim_expr_vis; rewrite !subevent_subevent.

   (*    iDestruct (expr_inv_local_env_includes id with "HC") as %(Ht & Hs); *)
   (*    [ set_solver | set_solver | ]. *)

   (*    iApply sim_expr_bupd_mono ; *)
   (*      [ | iApply (expr_local_read_refl with "HC")]; eauto; cycle 1. *)
   (*    { cbn; case_decide; set_solver. } *)
   (*    iIntros (??) "H". *)
   (*    iDestruct "H" as (????) "H". *)
   (*    rewrite H H0. rewrite !bind_ret_l. *)
   (*    iApply sim_expr_tau; iApply sim_expr_base. *)
   (*    iExists _, _; by iFrame. } *)
   (* Qed. *)
  Admitted.

  Lemma expr_logrel_EXP_Integer:
    ∀ (x : int) (dt : option dtyp),
      ⊢ exp_conv (denote_exp dt (EXP_Integer x))
        ⪯ exp_conv (denote_exp dt (EXP_Integer x))
      [{ (v_t, v_s), uval_rel v_t v_s }].
  Proof.
    iIntros (x dt).
    exp_logrel_pre dt. exp_logrel_pre d.
    rewrite /denote_exp /lift_undef_or_err.
    destruct (Functor.fmap dvalue_to_uvalue (coerce_integer_to_int sz x)) eqn: Hx;
      destruct unEitherT, s;
      [iApply exp_conv_raiseUB
      | iApply exp_conv_raiseUB
      | iApply exp_conv_raise | ].
    setoid_rewrite interp_ret. iApply sim_expr_base; iExists _, _; iFrame.
    iSplitL ""; [ | iSplitL ""]; try (iPureIntro; reflexivity).
    inversion Hx.
    destruct (EitherMonad.unEitherT (coerce_integer_to_int sz x));
      destruct s; inversion H0; clear H0; subst.

    assert (sz = 1%N \/ sz = 8%N \/ sz = 32%N \/ sz = 64%N).
    { destruct sz; inversion Hx; destruct p; cbn in H0; inversion H0.
      - repeat (destruct p; inversion H1); tauto.
      - tauto. }
    destruct H as [H | [H | [H | H ] ] ]; subst; cbn in Hx; inversion Hx;
      iApply uval_rel_lift; eauto;
      rewrite unfold_dval_rel; cbn; subst; eauto.
    Unshelve. all : try eauto.
  Qed.

  Lemma expr_logrel_EXP_Float:
    ∀ x (dt : option dtyp),
      ⊢ exp_conv (denote_exp dt (EXP_Float x))
        ⪯ exp_conv (denote_exp dt (EXP_Float x))
      [{ (v_t, v_s),uval_rel v_t v_s }].
  Proof.
    iIntros (??); exp_logrel_num dt d.
  Qed.

  Lemma expr_logrel_EXP_Hex:
    ∀ x (dt : option dtyp),
      ⊢ exp_conv (denote_exp dt (EXP_Hex x))
        ⪯ exp_conv (denote_exp dt (EXP_Hex x))
      [{ (v_t, v_s), uval_rel v_t v_s }].
  Proof.
    iIntros (??); exp_logrel_num dt d.
  Qed.

  Lemma expr_logrel_EXP_Double:
    ∀ x (dt : option dtyp),
      ⊢ exp_conv (denote_exp dt (EXP_Double x))
        ⪯ exp_conv (denote_exp dt (EXP_Double x))
      [{ (v_t, v_s),uval_rel v_t v_s }].
  Proof.
    iIntros (??); exp_logrel_num dt d.
  Qed.

  Lemma expr_logrel_EXP_Bool:
    ∀ x (dt : option dtyp),
      ⊢ exp_conv (denote_exp dt (EXP_Bool x))
        ⪯ exp_conv (denote_exp dt (EXP_Bool x))
      [{ (v_t, v_s),uval_rel v_t v_s }].
  Proof.
    iIntros (b?).
    exp_logrel_pre b; exp_logrel_ret.
  Qed.

  (* [Binop]-y operations *)

  (* [OP_IBinop] *)
  Lemma expr_logrel_OP_IBinop:
    ∀ I (iop : ibinop) (t : dtyp) (e1 e2 : exp dtyp) (dt : option dtyp)
      i_t i_s L_t L_s,
      □ (∀ (a : option dtyp),
           I i_t i_s L_t L_s e1 e1 -∗
          exp_conv (denote_exp a e1) ⪯
          exp_conv (denote_exp a e1)
          [{ (v_t, v_s),
              uval_rel v_t v_s ∗
              code_inv I i_t i_s L_t L_s e1 e1 }]) -∗
        (∀ (a : option dtyp),
          code_inv I i_t i_s L_t L_s e2 e2 -∗
          exp_conv (denote_exp a e2) ⪯
          exp_conv (denote_exp a e2)
          [{ (v_t, v_s),
              uval_rel v_t v_s ∗
              code_inv I i_t i_s L_t L_s e2 e2  }]) -∗
        code_inv I i_t i_s L_t L_s
          (OP_IBinop iop t e1 e2)
          (OP_IBinop iop t e1 e2)  -∗
        exp_conv (denote_exp dt (OP_IBinop iop t e1 e2)) ⪯
        exp_conv (denote_exp dt (OP_IBinop iop t e1 e2))
      [{ (v_t, v_s),
          uval_rel v_t v_s ∗
          expr_inv i_t i_s L_t L_s
            (OP_IBinop iop t e1 e2)
            (OP_IBinop iop t e1 e2) }].
  Proof.
    iIntros (iop t e1 e2 dt ????) "#IH IH1 HI".

    iDestruct (expr_inv_binop_invert with "HI") as "(HI&H2)".

    iSpecialize ("IH" $! (Some t) with "HI").
    cbn; setoid_rewrite interp_bind.
    iApply sim_expr_bind.
    iApply (sim_expr_bupd_mono with "[IH1 H2]"); [ | iApply "IH"].
    iIntros (e_t e_s) "H".
    iDestruct "H" as (?? Ht Hs) "(Hv & HI)".
    rename v_t into v1', v_s into v1.
    rewrite Ht Hs; clear Ht Hs.
    do 2 rewrite bind_ret_l interp_bind.

    iDestruct (expr_local_env_inv_commute with "HI H2") as "(HI & H1)".

    iSpecialize ("IH1" $! (Some t) with "HI").
    iApply sim_expr_bind.
    iApply (sim_expr_bupd_mono with "[H1 Hv]"); [ | iApply "IH1"].
    clear e_t e_s.
    iIntros (e_t e_s) "H".
    iDestruct "H" as (?? Ht Hs) "(Hv0 & HI)".
    rewrite Ht Hs; clear Ht Hs.
    do 2 rewrite bind_ret_l. subst.
    rename v_t into v2', v_s into v2.

    do 2 rewrite interp_ret. iApply sim_expr_base.
    do 2 iExists _. do 2 (iSplitL ""; [ done | ]).
    iSplitL "Hv Hv0"; first iApply (uval_rel_binop with "Hv Hv0").
    iApply expr_inv_binop; iFrame.
    iApply (expr_local_env_inv_commute with "HI H1").
  Qed.

  (* [OP_ICmp]*)
  Lemma expr_logrel_OP_ICmp:
    ∀ iop (t : dtyp) (e1 e2 : exp dtyp) (dt : option dtyp)
      i_t i_s L_t L_s,
      □ (∀ (a : option dtyp),
          expr_inv i_t i_s L_t L_s e1 e1 -∗
          exp_conv (denote_exp a e1) ⪯
          exp_conv (denote_exp a e1)
          [{ (v_t, v_s),
              uval_rel v_t v_s ∗
              expr_inv i_t i_s L_t L_s e1 e1 }]) -∗
        (∀ (a : option dtyp),
          expr_inv i_t i_s L_t L_s e2 e2 -∗
          exp_conv (denote_exp a e2) ⪯
          exp_conv (denote_exp a e2)
          [{ (v_t, v_s),
              uval_rel v_t v_s ∗
              expr_inv i_t i_s L_t L_s e2 e2  }]) -∗
        expr_inv i_t i_s L_t L_s
          (OP_ICmp iop t e1 e2)
          (OP_ICmp iop t e1 e2)  -∗
        exp_conv (denote_exp dt (OP_ICmp iop t e1 e2)) ⪯
        exp_conv (denote_exp dt (OP_ICmp iop t e1 e2))
      [{ (v_t, v_s),
          uval_rel v_t v_s ∗
          expr_inv i_t i_s L_t L_s
            (OP_ICmp iop t e1 e2)
            (OP_ICmp iop t e1 e2) }].
  Proof.
    iIntros (iop t e1 e2 dt ????) "#IH IH1 HI".

    iDestruct (expr_inv_icmp_invert with "HI") as "(HI&H2)".

    iSpecialize ("IH" $! (Some t) with "HI").
    cbn; setoid_rewrite interp_bind.
    iApply sim_expr_bind.
    iApply (sim_expr_bupd_mono with "[IH1 H2]"); [ | iApply "IH"].
    iIntros (e_t e_s) "H".
    iDestruct "H" as (?? Ht Hs) "(Hv & HI)".
    rename v_t into v1', v_s into v1.
    rewrite Ht Hs; clear Ht Hs.
    do 2 rewrite bind_ret_l interp_bind.

    iDestruct (expr_local_env_inv_commute with "HI H2") as "(HI & H1)".

    iSpecialize ("IH1" $! (Some t) with "HI").
    iApply sim_expr_bind.
    iApply (sim_expr_bupd_mono with "[H1 Hv]"); [ | iApply "IH1"].
    clear e_t e_s.
    iIntros (e_t e_s) "H".
    iDestruct "H" as (?? Ht Hs) "(Hv0 & HI)".
    rewrite Ht Hs; clear Ht Hs.
    do 2 rewrite bind_ret_l. subst.
    rename v_t into v2', v_s into v2.

    do 2 rewrite interp_ret. iApply sim_expr_base.
    do 2 iExists _. do 2 (iSplitL ""; [ done | ]).
    iSplitL "Hv Hv0"; first iApply (uval_rel_icmp with "Hv Hv0").
    iApply expr_inv_icmp; iFrame.
    iApply (expr_local_env_inv_commute with "HI H1").
  Qed.

  Tactic Notation "expr_case" constr(lem) :=
    iApply (sim_expr_mono with "[HI]"); last iApply lem;
        eauto;
      iIntros (??) "H"; iDestruct "H" as (????) "Hv";
      iExists _, _; by iFrame.

  (* Inductive cases *)

  (* TODO: Factor out the [expr_inv] into an arbitrary invariant *)
   Lemma expr_logrel_ind_case :
     forall (elts : list (dtyp * exp dtyp)) i_t i_s L_t L_s Vexp (Exp : _ -> exp dtyp),
    (* [uval_rel] nil case *)
    □ (uval_rel (Vexp []) (Vexp [])) -∗
    (* [uval_rel] cons case *)
    □ (∀ v_t v_s l_t l_s,
      uval_rel v_t v_s -∗
      uval_rel (Vexp l_t) (Vexp l_s) -∗
      uval_rel (Vexp (v_t :: l_t)) (Vexp (v_s :: l_s))) -∗
    (* [expr_inv] cons over the struct values *)
    □ (∀ i_t i_s L_t L_s d e elts,
        expr_inv i_t i_s L_t L_s e e ∗
        expr_local_env_inv i_t i_s (exp_local_ids (Exp elts)) L_t L_s
        ∗-∗
        expr_inv i_t i_s L_t L_s (Exp ((d, e) :: elts)) (Exp ((d, e) :: elts))) -∗
    (* [expr_inv] introduction over the struct values *)
    □ (∀ i_t i_s L_t L_s elts,
      expr_inv i_t i_s L_t L_s (Exp elts) (Exp elts) -∗
       expr_frame_inv i_t i_s L_t L_s ∗
        (∀ x, ⌜In x elts⌝ -∗
          expr_local_env_inv i_t i_s (exp_local_ids x.2) L_t L_s)) -∗
    □ (∀ x : dtyp * exp dtyp,
      ⌜In x elts⌝
      → ∀ (a : option dtyp) i_t i_s L_t L_s,
          expr_inv i_t i_s L_t L_s x.2 x.2 -∗
            exp_conv (denote_exp a x.2) ⪯
            exp_conv (denote_exp a x.2)
            [{ (v_t, v_s),
                uval_rel v_t v_s ∗ expr_inv i_t i_s L_t L_s x.2 x.2 }]) -∗
      expr_inv i_t i_s L_t L_s (Exp elts) (Exp elts) -∗
      r <- exp_conv
            (map_monad (λ '(dt0, ex), (denote_exp (Some dt0) ex)) elts);;
      Ret (Vexp r)
      ⪯
      r <-  exp_conv (map_monad (λ '(dt0, ex), (denote_exp (Some dt0) ex)) elts);;
      Ret (Vexp r)
    [{ (v_t, v_s),
        uval_rel v_t v_s ∗
          expr_inv i_t i_s L_t L_s (Exp elts) (Exp elts) }].
  Proof.
    iIntros (elts i_t i_s L_t L_s Vexp Exp) "#Hbase #Hind #Hinv #Hinvp #IH HI".
    rewrite /exp_conv.
    (* We follow by induction on the structure elements. *)
    iInduction elts as [] "IHl".
    (* nil case *)
    { cbn; rewrite interp_ret bind_ret_l.
      iApply sim_expr_base; iExists _, _; iFrame;
      iSplitL ""; [ | iSplitL ""]; try (iPureIntro; reflexivity); done. }
    (* cons case *)
    { cbn. destruct a. rewrite /exp_conv.
      rewrite interp_bind bind_bind.
      iApply sim_expr_bind.

      iDestruct ("Hinv" with "HI") as "(He & Helts)".

      iSpecialize ("IHl" with "[]").
      { iModIntro. iIntros (x Hin dt' i_t' i_s' L_t' L_s') "Hinv'".
        assert ((d, e) = x \/ In x elts) by (by right).
        by iSpecialize ("IH" $! _ H dt' i_t' i_s' L_t' L_s' with "Hinv'"). }

      assert (EQ: (d, e) = (d, e) ∨ In (d, e) elts) by (left; auto).
      iSpecialize ("IH" $! (d, e) EQ _ _); clear EQ; cbn.
      iSpecialize ("IH" with "He").
      iApply (sim_expr_bupd_mono with "[Helts]"); [ | done].
      iIntros (??) "Hr".
      iDestruct "Hr" as (????) "[Hv Hinv']".
      rewrite H H0. do 2 rewrite bind_ret_l.
      iDestruct (expr_local_env_inv_commute with "Hinv' Helts") as "(Helts & Hinv')".
      iSpecialize ("IHl" with "Helts"). iModIntro.
      do 2 rewrite interp_bind bind_bind.
      setoid_rewrite interp_ret.
      setoid_rewrite bind_ret_l.
      iPoseProof sim_expr_fmap_inv as "Hfmap".
      iSpecialize ("Hfmap" with "IHl").
      iApply sim_expr_bind.
      iApply (sim_expr_bupd_mono with "[Hinv' Hv]"); [ | done].
      iIntros (??) "Hp". rewrite /lift_post.
      iDestruct "Hp" as (????????) "[Hp CI]".
      apply eqit_inv_Ret in H3, H4; subst. rewrite H1 H2. do 2 rewrite bind_ret_l.
      iApply sim_expr_base. iModIntro; do 2 iExists _. eauto.
      iSplitL ""; [| iSplitL ""]; auto; iFrame.
      iSplitL "Hv Hp"; first iApply ("Hind" with "Hv Hp").
      iApply "Hinv"; iFrame.
      iApply (expr_local_env_inv_commute with "CI Hinv'"). }
  Qed.

  Lemma expr_logrel_EXP_Cstring:
    ∀ (elts : list (dtyp * exp dtyp))
      (τ : option dtyp) (i_t i_s : list frame_names) (L_t L_s : local_env),
    expr_inv i_t i_s L_t L_s (EXP_Cstring elts) (EXP_Cstring elts) -∗
    □ (∀ x : dtyp * exp dtyp,
        ⌜In x elts⌝
        → ∀ (τ0 : option dtyp) (i_t0 i_s0 : list frame_names) (L_t0 L_s0 : local_env),
            expr_inv i_t0 i_s0 L_t0 L_s0 x.2 x.2 -∗
            exp_conv (denote_exp τ0 x.2)
            ⪯
            exp_conv (denote_exp τ0 x.2)
            [{ (v_t, v_s),uval_rel v_t v_s ∗ expr_inv i_t0 i_s0 L_t0 L_s0 x.2 x.2}]) -∗
    exp_conv (denote_exp τ (EXP_Cstring elts))
    ⪯
    exp_conv (denote_exp τ (EXP_Cstring elts))
    [{ (v_t, v_s),
        uval_rel v_t v_s ∗
          expr_inv i_t i_s L_t L_s (EXP_Cstring elts) (EXP_Cstring elts)}].
  Proof.
    intros elts dt ? ? ? ?. iIntros "Hi #IH".
    cbn; setoid_rewrite interp_bind; setoid_rewrite interp_ret.
    iApply expr_logrel_ind_case; auto.
    { iModIntro; cbn; iApply uval_rel_lift; eauto;
        rewrite unfold_dval_rel; auto. cbn; done. }
    { iModIntro.
      iIntros (v_t v_s l_t l_s) "Hv Hl".
      iApply (uval_rel_array_cons with "Hv Hl"); cbn; iFrame. }
    { iModIntro. iIntros. iApply expr_inv_cstring_cons. }
    { iModIntro. iIntros. by iApply expr_inv_cstring_invert. }
  Qed.

  Lemma expr_logrel_EXP_Struct:
    ∀ (fields : list (dtyp * exp dtyp))
      (τ : option dtyp)
      (i_t i_s : list frame_names) (L_t L_s : local_env),
      expr_inv i_t i_s L_t L_s
        (EXP_Struct fields) (EXP_Struct fields) -∗
      □ (∀ x : dtyp * exp dtyp,
          ⌜In x fields⌝
          → ∀ (τ0 : option dtyp) (i_t0 i_s0 : list frame_names) (L_t0 L_s0 : local_env),
              expr_inv i_t0 i_s0 L_t0 L_s0 x.2 x.2 -∗
              exp_conv (denote_exp τ0 x.2)
              ⪯
              exp_conv (denote_exp τ0 x.2)
              [{ (v_t, v_s), uval_rel v_t v_s ∗ expr_inv i_t0 i_s0 L_t0 L_s0 x.2 x.2}]) -∗
      exp_conv (denote_exp τ (EXP_Struct fields))
      ⪯
      exp_conv (denote_exp τ (EXP_Struct fields))
      [{ (v_t, v_s), uval_rel v_t v_s ∗
            expr_inv i_t i_s L_t L_s (EXP_Struct fields) (EXP_Struct fields)}].
  Proof.
    intros elts dt ? ? ? ?. iIntros "Hi #IH".
    cbn; setoid_rewrite interp_bind; setoid_rewrite interp_ret.
    iApply expr_logrel_ind_case; auto.
    { iModIntro; cbn; iApply uval_rel_lift; eauto;
        rewrite unfold_dval_rel; auto. cbn; done. }
    { iModIntro.
      iIntros (v_t v_s l_t l_s) "Hv Hl".
      iApply (uval_rel_struct_cons with "Hv Hl"); cbn; iFrame. }
    { iModIntro. iIntros. iApply expr_inv_struct_cons. }
    { iModIntro. iIntros. by iApply expr_inv_struct_invert. }
  Qed.

  Lemma expr_logrel_OP_Conversion:
    ∀ (conv : conversion_type)
      (t_from t_to : dtyp)
      (e : exp dtyp)
      (τ : option dtyp)
      (i_t i_s : list frame_names)
      (L_t L_s : local_env),
      expr_inv i_t i_s L_t L_s
        (OP_Conversion conv t_from e t_to)
        (OP_Conversion conv t_from e t_to) -∗
      □ (∀ (τ0 : option dtyp) (i_t0 i_s0 : list frame_names) (L_t0 L_s0 : local_env),
          expr_inv i_t0 i_s0 L_t0 L_s0 e e -∗
          exp_conv (denote_exp τ0 e)
          ⪯
          exp_conv (denote_exp τ0 e)
          [{ (v_t, v_s),
              uval_rel v_t v_s ∗
              expr_inv i_t0 i_s0 L_t0 L_s0 e e}]) -∗
      exp_conv (denote_exp τ (OP_Conversion conv t_from e t_to))
      ⪯
      exp_conv (denote_exp τ (OP_Conversion conv t_from e t_to))
      [{ (v_t, v_s),uval_rel v_t v_s ∗
          expr_inv i_t i_s L_t L_s
          (OP_Conversion conv t_from e t_to) (OP_Conversion conv t_from e t_to)}].
  Proof.
    iIntros (?????????) "Hi #IH".
    iPoseProof (expr_inv_op_conversion with "Hi") as "Hi".

    cbn.
    cbn; setoid_rewrite interp_bind.
    iApply sim_expr_bind.
    iApply sim_expr_bupd_mono; [ | iApply "IH"]; try done.
    cbn.
    iIntros (e_t e_s) "H".
    iDestruct "H" as (?? Ht Hs) "(Hv & HI)".
    subst.
    rewrite Ht Hs; clear Ht Hs.
    do 2 rewrite bind_ret_l.
    do 2 rewrite interp_ret. iApply sim_expr_base.
    do 2 iExists _. do 2 (iSplitL ""; [ done | ]).
    rewrite /uval_rel. iFrame.
    iModIntro; iIntros (??). inversion H.
  Qed.

  Lemma expr_logrel_EXP_GEP :
    ∀ (t : dtyp)
      (ptrval : dtyp * exp dtyp)
      (idxs : list (dtyp * exp dtyp))
      (τ : option dtyp)
      (i_t i_s : list frame_names)
      (L_t L_s : local_env),
    □ (∀ x : dtyp * exp dtyp,
         ⌜In x idxs⌝ →
        ∀ τ0 i_t0 i_s0 L_t0 L_s0,
          expr_inv i_t0 i_s0 L_t0 L_s0 x.2 x.2 -∗
          exp_conv (denote_exp τ0 x.2) ⪯
          exp_conv (denote_exp τ0 x.2)
        [{ (v_t, v_s), uval_rel v_t v_s ∗
          expr_inv i_t0 i_s0 L_t0 L_s0 x.2 x.2}]) -∗
    □ (∀ τ0 i_t0 i_s0 L_t0 L_s0,
         expr_inv i_t0 i_s0 L_t0 L_s0 ptrval.2 ptrval.2 -∗
         exp_conv (denote_exp τ0 ptrval.2) ⪯
         exp_conv (denote_exp τ0 ptrval.2)
        [{ (v_t, v_s), uval_rel v_t v_s ∗
            expr_inv i_t0 i_s0 L_t0 L_s0 ptrval.2 ptrval.2}]) -∗
      expr_inv i_t i_s L_t L_s
        (OP_GetElementPtr t ptrval idxs)
        (OP_GetElementPtr t ptrval idxs) -∗
      exp_conv (denote_exp τ (OP_GetElementPtr t ptrval idxs))
      ⪯
      exp_conv (denote_exp τ (OP_GetElementPtr t ptrval idxs))
      [{ (v_t, v_s), uval_rel v_t v_s ∗
          expr_inv i_t i_s L_t L_s
            (OP_GetElementPtr t ptrval idxs)
            (OP_GetElementPtr t ptrval idxs) }].
  Proof.
    iIntros (t (ptr_t &e1) dt idxs ? ? ? ? ) "#IH1 #IH2 HI".

    iDestruct (expr_inv_op_gep_invert with "HI") as "(He & HI)".
    cbn. setoid_rewrite interp_bind.
    iSpecialize ("IH2" with "He").
    iApply sim_expr_bind.
    iApply (sim_expr_bupd_mono with "[HI IH1]"); [ | iApply "IH2"].
    iIntros (e_t e_s) "H".

    iDestruct "H" as (?? Ht Hs) "(Hv & HI')".
    rename v_t into v1', v_s into v1.
    rewrite Ht Hs; clear Ht Hs.
    do 2 rewrite bind_ret_l interp_bind.
    setoid_rewrite interp_ret.

    iInduction dt as [] "IHl".
    - cbn. rewrite interp_ret bind_ret_l.
      rewrite bind_ret_l. iApply sim_expr_base.
      iExists (UVALUE_GetElementPtr t v1' []), (UVALUE_GetElementPtr t v1 []).
      iModIntro. do 2 (iSplitL ""; [ done | ]).
      iSplitL "Hv".
      { rewrite /uval_rel; cbn.
        iIntros (??). inversion H. }

      iDestruct "HI'" as "(Hf & HI')".
      rewrite /expr_inv; iFrame.
      rewrite !intersection_local_ids_eq; cbn.
      rewrite app_nil_r; done.

    - cbn. destruct a. rewrite interp_bind; do 2 rewrite bind_bind.
      iApply sim_expr_bind.
      iSpecialize ("IHl" with "[]").
      { iModIntro. iIntros (x Hin dt' i_t' i_s' L_t' L_s') "Hinv".
        assert ((d, e) = x \/ In x dt) by (by right).
        by iSpecialize ("IH1" $! _ H with "Hinv"). }
      assert (EQ : ((d, e) = (d, e) \/ In (d, e) dt)). { by left. }
      iSpecialize ("IH1" $! _ EQ).
      iDestruct "HI" as "(He & HI)".
      iDestruct (expr_local_env_inv_commute with "HI' He") as "(He & Heq)".
      iSpecialize ("IH1" $! _ i_t i_s L_t L_s with "He").
      iApply (sim_expr_bupd_mono with "[HI Heq Hv]"); [ | done].

      iIntros (??) "Hr".
      iDestruct "Hr" as (????) "[Hv' Hinv]".
      rewrite H H0. do 2 rewrite bind_ret_l.

      iDestruct (expr_local_env_inv_commute with "Hinv Heq") as "(He & Heq)".
      iSpecialize ("IHl" with "HI Hv He").

      do 2 rewrite interp_bind bind_bind.
      setoid_rewrite interp_ret.
      setoid_rewrite bind_ret_l.
      iPoseProof sim_expr_fmap_inv as "Hfmap".
      iMod "IHl". iSpecialize ("Hfmap" with "IHl").
      iApply sim_expr_bind.
      iApply (sim_expr_bupd_mono with "[Heq Hv']"); [ | done].
      iIntros (??) "Hp". rewrite /lift_post.
      iDestruct "Hp" as (????????) "[Hp CI]".
      apply eqit_inv_Ret in H3, H4; subst. rewrite H1 H2. do 2 rewrite bind_ret_l.
      iApply sim_expr_base. iModIntro; do 2 iExists _.
      do 2 (iSplitL ""; first done).
      iSplitL "Hv' Hp".
      { rewrite /uval_rel; eauto. }

      iDestruct (expr_inv_op_gep_invert with "CI") as "((Hf & He) & HI)";
      rewrite /expr_inv; iFrame.
      rewrite !intersection_local_ids_eq. cbn -[expr_local_env_inv].
      iApply (expr_local_env_inv_app with "He"). rewrite app_nil_r.
      iApply (expr_local_env_inv_app with "Heq").
      by iApply expr_local_env_inv_big_opL.
  Qed.

  Lemma expr_logrel_EXP_Array:
    ∀ (fields : list (dtyp * exp dtyp))
      (τ : option dtyp)
      (i_t i_s : list frame_names) (L_t L_s : local_env),
      expr_inv i_t i_s L_t L_s
        (EXP_Array fields) (EXP_Array fields) -∗
      □ (∀ x : dtyp * exp dtyp,
          ⌜In x fields⌝
          → ∀ (τ0 : option dtyp) (i_t0 i_s0 : list frame_names) (L_t0 L_s0 : local_env),
              expr_inv i_t0 i_s0 L_t0 L_s0 x.2 x.2 -∗
              exp_conv (denote_exp τ0 x.2)
              ⪯
              exp_conv (denote_exp τ0 x.2)
              [{ (v_t, v_s), uval_rel v_t v_s ∗ expr_inv i_t0 i_s0 L_t0 L_s0 x.2 x.2}]) -∗
      exp_conv (denote_exp τ (EXP_Array fields))
      ⪯
      exp_conv (denote_exp τ (EXP_Array fields))
      [{ (v_t, v_s), uval_rel v_t v_s ∗
            expr_inv i_t i_s L_t L_s (EXP_Array fields) (EXP_Array fields)}].
  Proof.
    intros elts dt ? ? ? ?. iIntros "Hi #IH".
    cbn; setoid_rewrite interp_bind; setoid_rewrite interp_ret.
    iApply expr_logrel_ind_case; auto.
    { iModIntro; cbn; iApply uval_rel_lift; eauto;
        rewrite unfold_dval_rel; auto. cbn; done. }
    { iModIntro.
      iIntros (v_t v_s l_t l_s) "Hv Hl".
      iApply (uval_rel_array_cons with "Hv Hl"); cbn; iFrame. }
    { iModIntro. iIntros. iApply expr_inv_array_cons. }
    { iModIntro. iIntros. by iApply expr_inv_array_invert. }
  Qed.

  (* Reflexivity theorems *)
  Theorem expr_logrel_relaxed_refl e:
    (⊢ expr_logrel_relaxed e e)%I.
  Proof.
    iIntros. rewrite /expr_logrel_relaxed.
    iInduction e as [] "IH" using AstLib.exp_ind;
    iIntros (τ ? ? L_t L_s) "HI".
    { (* EXP_Ident *)
      by iApply expr_logrel_EXP_Ident. }
    (* Numeric cases *)
    { iApply (sim_expr_mono with "[HI]"); last iApply expr_logrel_EXP_Integer;
        eauto.
      iIntros (??) "H". iDestruct "H" as (????) "Hv".
      iExists _, _; by iFrame. }
    { expr_case expr_logrel_EXP_Float. }
    { expr_case expr_logrel_EXP_Double. }
    { expr_case expr_logrel_EXP_Hex. }
    { expr_case expr_logrel_EXP_Bool. }

    { (* EXP_Null *)
      iApply sim_null_bij. iIntros "#Hn".
      setoid_rewrite interp_ret; iApply sim_expr_base; iExists _ , _;
        iFrame; iSplitL ""; [  | iSplitL "" ]; try (iPureIntro; reflexivity).
      iApply uval_rel_lift; eauto.
      by rewrite unfold_dval_rel. }

    { (* EXP_Zero_initializer *)
      iApply sim_null_bij. iIntros "#Hn".
      exp_logrel_pre τ. rewrite /exp_conv /denote_exp /lift_err; cbn.
      destruct (dv_zero_initializer d) eqn: Hzi.
      - iApply exp_conv_raise.
      - setoid_rewrite interp_ret; iApply sim_expr_base; iExists _, _; iFrame;
        iSplitL ""; [ | iSplitL ""]; try (iPureIntro; reflexivity).
        iApply dval_rel_lift.
        iApply (@zero_initializer_uval_refl _ _ _ _ Hzi with "Hn"). }

    { (* EXP_CString *)
      by iApply (expr_logrel_EXP_Cstring with "HI"). }

    { (* EXP_Undef *)
      destruct τ; cbn; [ | iApply exp_conv_raise ].
      iApply sim_null_bij. iIntros "#Hnull".
      setoid_rewrite interp_ret; iApply sim_expr_base; iExists _ , _;
        iFrame; iSplitL ""; [  | iSplitL "" ]; try (iPureIntro; reflexivity).
      by iApply uval_rel_undef. }

    { by iApply (expr_logrel_EXP_Struct with "HI"). }

    (* EXP_Array *)
    { by iApply (expr_logrel_EXP_Array with "HI"). }

    { iApply expr_logrel_OP_IBinop; eauto.
      - iModIntro; iIntros; iApply "IH"; done.
      - iIntros; iApply "IH1"; done. }

    { iApply expr_logrel_OP_ICmp; eauto.
      - iModIntro; iIntros; iApply "IH"; done.
      - iIntros; iApply "IH1"; done. }

    { by iApply (expr_logrel_OP_Conversion with "HI"). }

    { iApply expr_logrel_EXP_GEP; eauto. }
  Qed.

End fundamental_exp.
