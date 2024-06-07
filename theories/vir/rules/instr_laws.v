From iris.prelude Require Import options.

From velliris.program_logic Require Import program_logic.
From velliris.vir.lang Require Export lang.
From velliris.vir.rules Require Export event_laws frame_laws.

Import DenoteTactics.

Set Default Proof Using "Type*".
(* ------------------------------------------------------------------------ *)
  (* Utilities later useful for proving properties about [map_monad] over
    expressions and instructions *)

Section instr_properties.

  Context {Σ} `{!vellirisGS Σ}.

  Lemma lift_exp_conv_map_monad {A B}
    (f : A -> _ B) (e : list A) P Q :
    □ (∀ x, P x x -∗
          exp_conv (f x) ⪯ exp_conv (f x)
          [{ (x_t, x_s), Q x_t x_s }]) -∗
    □ ([∗ list] _ ↦x ∈ e, P x x) -∗
    exp_conv (map_monad f e) ⪯
    exp_conv (map_monad f e)
    [{ (r_t, r_s),
      ([∗ list] _ ↦x_t;x_s ∈ r_t;r_s, Q x_t x_s)}].
  Proof.
    iIntros "#H #CI".
    iInduction e as [] "IHl".
    { cbn. vsimp. final.
      iExists _,_; do 2 (iSplitL ""; [done |]); done. }
    { cbn. vsimp.
      iDestruct "CI" as "[HP CI]".
      iSpecialize ("H" with "HP").
      Cut.
      iApply sim_expr_bupd_mono; [ | iApply "H"].
      iIntros (??) "HI".
      iDestruct "HI" as (??->->) "HQ".
      vsimp. Cut.
      iSpecialize ("IHl" with "CI").
      iApply (sim_expr_bupd_mono with "[HQ]"); [ | iApply "IHl"].
      iIntros (??) "HI".
      iDestruct "HI" as (??->->) "HQL".
      vsimp. final.
      do 2 iExists _; do 2 (iSplitL ""; [ done | ]).
      iApply big_sepL2_cons; iFrame. }
  Qed.

  Lemma lift_instr_conv_map_monad {A B}
    (f : A -> _ B) (e1 e2 : list A) P Q :
    □ (∀ x y, P x y -∗
          instr_conv (f x) ⪯ instr_conv (f y)
          [{ (x_t, x_s), Q x_t x_s }]) -∗
    □ ([∗ list] x;y ∈ e1;e2, P x y) -∗
    instr_conv (map_monad f e1) ⪯
    instr_conv (map_monad f e2)
    [{ (r_t, r_s),
      ([∗ list] x_t;x_s ∈ r_t;r_s, Q x_t x_s)}].
  Proof.
    iIntros "#H #CI".
    iInduction e2 as [] "IHl" forall (e1).
    { iDestruct (big_sepL2_nil_inv_r with "CI") as %Hx; subst; cbn.
      cbn. vsimp. final.
      iExists _,_; do 2 (iSplitL ""; [done |]); done. }
    { cbn.
      iDestruct (big_sepL2_cons_inv_r with "CI") as (???) "(CI1 & CI2)";
        subst; cbn.
      vsimp.
      iDestruct "CI" as "[HP CI]".
      iSpecialize ("H" with "HP"). Cut.
      iApply sim_expr_bupd_mono; [ | iApply "H"].
      iIntros (??) "HI".
      iDestruct "HI" as (??->->) "HQ".
      vsimp. Cut.
      iSpecialize ("IHl" with "CI").
      iApply (sim_expr_bupd_mono with "[HQ]"); [ | iApply "IHl"].
      iIntros (??) "HI".
      iDestruct "HI" as (??->->) "HQL".
      final.
      do 2 iExists _; do 2 (iSplitL ""; [ done | ]).
      iApply big_sepL2_cons; iFrame. }
  Qed.

(* ------------------------------------------------------------------------ *)

  Lemma target_local_id {i_t id v Φ}:
    stack_tgt i_t -∗
    [ id := v ]t i_t -∗
    (stack_tgt i_t -∗ [id := v]t i_t -∗ Φ (Ret v)) -∗
    (target_red (exp_conv (denote_op (EXP_Ident (ID_Local id)))) Φ).
  Proof.
    iIntros "Hs_t Ht HΦ"; cbn.
    iApply target_red_eq_itree.
    { rewrite translate_vis. rewrite /exp_conv interp_vis; cbn.
      setoid_rewrite translate_ret; setoid_rewrite interp_ret. done. }
    iApply target_red_bind.
    iApply (target_local_read with "Ht Hs_t").
    iIntros "Ht Hs_t".
    iApply target_red_eq_itree; first by rewrite bind_ret_l.
    iApply target_red_tau; iApply target_red_base.
    iApply ("HΦ" with "Hs_t Ht").
  Qed.

  Lemma target_instr_local_write (x : LLVMAst.raw_id) (v : uvalue) e i L Ψ:
    x ∉ L ->
    match e with
    | INSTR_Comment _ | INSTR_Call _ _ _ | INSTR_Store _ _ _ _ => False
    | _ => True
    end ->
    ⊢ stack_tgt i -∗
      ldomain_tgt i L -∗
      (ldomain_tgt i L -∗
        stack_tgt i -∗
        target_red (η := vir_handler) (instr_conv (denote_instr_exp e))
        (lift_unary_post (fun y => ⌜y = v⌝ ∗
        ldomain_tgt i L ∗
        stack_tgt i))) -∗
      ([ x := v ]t i -∗
        ldomain_tgt i ({[x]} ∪ L) -∗
        stack_tgt i -∗
        Ψ (Ret ())) -∗
      target_red (η := vir_handler) (<{ %(IId x) = e }>) Ψ.
  Proof.
    iIntros (Hnin He) "Hf Hd H HΨ".
    cbn. rewrite /instr_conv.
    iApply target_red_eq_itree.
    { rewrite interp_bind. reflexivity. }
    iApply target_red_bind.
    iApply (target_red_mono with "[HΨ]");
      last iApply ("H" with "Hd Hf").
    iIntros (?) "HΦ".
    iDestruct "HΦ" as (???) "HΦ"; subst.
    iApply target_red_eq_itree; first by rewrite H bind_ret_l.
    iDestruct "HΦ" as "(Hd & Hs)".
    destruct e; eauto; try inv He.
    all: iApply target_red_eq_itree; [ by rewrite interp_vis | ];
      iApply target_red_bind;
      iApply (target_local_write_alloc with "Hd Hs [HΨ]"); auto;
      iIntros "Hi Hd Hs";
      iApply target_red_eq_itree; [ by rewrite bind_ret_l interp_ret | ];
      iApply target_red_tau; iApply target_red_base;
      iApply ("HΨ" with "Hi Hd Hs").
  Qed.

  Lemma target_instr_local_write1 (x : LLVMAst.raw_id) (v v' : uvalue) e i L Ψ:
    match e with
    | INSTR_Comment _ | INSTR_Call _ _ _ | INSTR_Store _ _ _ _ => False
    | _ => True
    end ->
    ⊢ stack_tgt i -∗
      ldomain_tgt i L -∗
      [ x := v' ]t i -∗
      ([ x := v' ]t i -∗
        ldomain_tgt i L -∗
        stack_tgt i -∗
        target_red (η := vir_handler) (instr_conv (denote_instr_exp e))
        (lift_unary_post (fun y => ⌜y = v⌝ ∗
       [x := v']t i ∗
        ldomain_tgt i L ∗
        stack_tgt i))) -∗
      ([ x := v ]t i -∗
        ldomain_tgt i L -∗
        stack_tgt i -∗
        Ψ (Ret ())) -∗
      target_red (η := vir_handler) (<{ %(IId x) = e }>) Ψ.
  Proof.
    iIntros (He) "Hf Hd Hv H HΨ".
    cbn. rewrite /instr_conv.
    iApply target_red_eq_itree.
    { rewrite interp_bind. reflexivity. }
    iApply target_red_bind.
    iApply (target_red_mono with "[HΨ]");
      last iApply ("H" with "Hv Hd Hf").
    iIntros (?) "HΦ".
    iDestruct "HΦ" as (???) "HΦ"; subst.
    iApply target_red_eq_itree; first by rewrite H bind_ret_l.
    iDestruct "HΦ" as "(Hv & Hd & Hs)".
    destruct e; eauto; try inv He.
    all: iApply target_red_eq_itree; [ by rewrite interp_vis | ];
      iApply target_red_bind;
      iApply (target_local_write with "Hv Hs [Hd HΨ]"); auto;
      iIntros "Hi Hs";
      iApply target_red_eq_itree; [ by rewrite bind_ret_l interp_ret | ];
      iApply target_red_tau; iApply target_red_base;
      iApply ("HΨ" with "Hi Hd Hs").
  Qed.

  Lemma target_instr_pure (x : LLVMAst.raw_id) (v : uvalue) o i L Ψ:
    x ∉ L ->
    ⊢ stack_tgt i -∗
      ldomain_tgt i L -∗
      (ldomain_tgt i L -∗
        stack_tgt i -∗
        target_red (η := vir_handler) (exp_conv (denote_op o))
        (lift_unary_post (fun y => ⌜y = v⌝ ∗
        ldomain_tgt i L ∗
        stack_tgt i))) -∗
      ([ x := v ]t i -∗
        ldomain_tgt i ({[x]} ∪ L) -∗
        stack_tgt i -∗
        Ψ (Ret ())) -∗
      target_red (η := vir_handler) (<{ %(IId x) = (INSTR_Op o) }>) Ψ.
  Proof.
    iIntros (?) "Hf Hd H HΨ".
    iApply (target_instr_local_write with "Hf Hd [H] [HΨ]"); eauto.
    iIntros "Hd Hs".
    cbn. iApply target_red_eq_itree.
    { by rewrite eq_itree_exp_conv_to_instr. }
    iApply ("H" with "Hd Hs").
  Qed.

  Lemma source_local_id {i_s id v Φ}:
    stack_src i_s -∗
    [ id := v ]s i_s -∗
    (stack_src i_s -∗ [id := v]s i_s -∗ Φ (Ret v)) -∗
    (source_red (exp_conv (denote_op (EXP_Ident (ID_Local id)))) Φ).
  Proof.
    iIntros "Hs_t Ht HΦ".
    cbn.
    iApply source_red_eq_itree.
    { rewrite translate_vis. rewrite /exp_conv interp_vis; cbn.
      setoid_rewrite translate_ret; setoid_rewrite interp_ret. done. }
    iApply source_red_bind.
    iApply (source_local_read with "Ht Hs_t").
    iIntros "Ht Hs_t".
    iApply source_red_eq_itree; first by rewrite bind_ret_l.
    iApply source_red_tau; iApply source_red_base.
    iApply ("HΦ" with "Hs_t Ht").
  Qed.

  Lemma source_instr_local_write (x : LLVMAst.raw_id) (v : uvalue) e i L Ψ:
    x ∉ L ->
    match e with
    | INSTR_Comment _ | INSTR_Call _ _ _ | INSTR_Store _ _ _ _ => False
    | _ => True
    end ->
    ⊢ stack_src i -∗
      ldomain_src i L -∗
      (ldomain_src i L -∗
        stack_src i -∗
        source_red (η := vir_handler) (instr_conv (denote_instr_exp e))
        (lift_unary_post (fun y => ⌜y = v⌝ ∗
        ldomain_src i L ∗
        stack_src i))) -∗
      ([ x := v ]s i -∗
        ldomain_src i ({[x]} ∪ L) -∗
        stack_src i -∗
        Ψ (Ret ())) -∗
      source_red (η := vir_handler) (<{ %(IId x) = e }>) Ψ.
  Proof.
    iIntros (Hnin He) "Hf Hd H HΨ".
    cbn. rewrite /instr_conv.
    iApply source_red_eq_itree.
    { rewrite interp_bind. reflexivity. }
    iApply source_red_bind.
    iApply (source_red_mono with "[HΨ]");
      last iApply ("H" with "Hd Hf").
    iIntros (?) "HΦ".
    iDestruct "HΦ" as (???) "HΦ"; subst.
    iApply source_red_eq_itree; first by rewrite H bind_ret_l.
    iDestruct "HΦ" as "(Hd & Hs)".
    destruct e; eauto; try inv He.
    all: iApply source_red_eq_itree; [ by rewrite interp_vis | ];
      iApply source_red_bind;
      iApply (source_local_write_alloc with "Hd Hs [HΨ]"); auto;
      iIntros "Hi Hd Hs";
      iApply source_red_eq_itree; [ by rewrite bind_ret_l interp_ret | ];
      iApply source_red_tau; iApply source_red_base;
      iApply ("HΨ" with "Hi Hd Hs").
  Qed.

  Lemma source_instr_local_write1 (x : LLVMAst.raw_id) (v v' : uvalue) e i L Ψ:
    match e with
    | INSTR_Comment _ | INSTR_Call _ _ _ | INSTR_Store _ _ _ _ => False
    | _ => True
    end ->
    ⊢ stack_src i -∗
      ldomain_src i L -∗
      [ x := v' ]s i -∗
      ([ x := v' ]s i -∗
        ldomain_src i L -∗
        stack_src i -∗
        source_red (η := vir_handler) (instr_conv (denote_instr_exp e))
        (lift_unary_post (fun y => ⌜y = v⌝ ∗
       [x := v']s i ∗
        ldomain_src i L ∗
        stack_src i))) -∗
      ([ x := v ]s i -∗
        ldomain_src i L -∗
        stack_src i -∗
        Ψ (Ret ())) -∗
      source_red (η := vir_handler) (<{ %(IId x) = e }>) Ψ.
  Proof.
    iIntros (He) "Hf Hd Hv H HΨ".
    cbn. rewrite /instr_conv.
    iApply source_red_eq_itree.
    { rewrite interp_bind. reflexivity. }
    iApply source_red_bind.
    iApply (source_red_mono with "[HΨ]");
      last iApply ("H" with "Hv Hd Hf").
    iIntros (?) "HΦ".
    iDestruct "HΦ" as (???) "HΦ"; subst.
    iApply source_red_eq_itree; first by rewrite H bind_ret_l.
    iDestruct "HΦ" as "(Hv & Hd & Hs)".
    destruct e; eauto; try inv He.
    all: iApply source_red_eq_itree; [ by rewrite interp_vis | ];
      iApply source_red_bind;
      iApply (source_local_write with "Hv Hs [Hd HΨ]"); auto;
      iIntros "Hi Hs";
      iApply source_red_eq_itree; [ by rewrite bind_ret_l interp_ret | ];
      iApply source_red_tau; iApply source_red_base;
      iApply ("HΨ" with "Hi Hd Hs").
  Qed.

  Lemma sim_instr_pure1
    (x_t x_s : LLVMAst.raw_id) (v_t v_s v_t' v_s' : uvalue) o_t o_s i_t i_s:
    ⊢ stack_tgt i_t -∗ stack_src i_s -∗
      [ x_t := v_t ]t i_t -∗ [ x_s := v_s ]s i_s -∗
      exp_conv (denote_op o_t)
      ⪯
      exp_conv (denote_op o_s)
      [{ (v_t'', v_s''), ⌜v_t' = v_t''⌝ ∗ ⌜v_s' = v_s''⌝ }] -∗
      <{ %(IId x_t) = (INSTR_Op o_t) }> ⪯
      <{ %(IId x_s) = (INSTR_Op o_s) }>
      [{ (v1, v2),
          [ x_t := v_t' ]t i_t ∗ [ x_s := v_s' ]s i_s ∗
          stack_tgt i_t ∗ stack_src i_s }].
  Proof.
    iIntros "Hf_t Hf_s Hp_t Hp_s H".
    setoid_rewrite interp_bind.
    iApply sim_expr_bind.
    iApply exp_conv_to_instr.

    iApply (sim_expr_bupd_mono with "[Hf_t Hf_s Hp_t Hp_s]");
      [ | iApply "H"].
    cbn. iIntros (??) "H".
    iDestruct "H" as (?????) "%Hv_s'".
    rewrite H H0 !bind_ret_l; subst.

    setoid_rewrite instr_conv_localwrite.

    iApply sim_expr_vis.
    rewrite !subevent_subevent.
    iApply sim_expr_bupd_mono;
      [ | iApply (sim_local_write with "Hf_t Hf_s Hp_t Hp_s")].

    clear H H0.

    cbn. iIntros (??) "H".
    iDestruct "H" as (????) "(?&?&?&?)".
    rewrite H H0 !bind_ret_l; subst.
    iApply sim_expr_tau.
    iApply sim_expr_base. iFrame.
    iExists _, _; done.
  Qed.

  Lemma target_instr_pure1 (x : LLVMAst.raw_id) (v : uvalue) o i L Ψ:
    ⊢ stack_tgt i -∗
      ldomain_tgt i L -∗
      [ x := v ]t i -∗
      ([ x := v ]t i -∗
        ldomain_tgt i L -∗
        stack_tgt i -∗
        Ψ (Ret tt)) -∗
      target_red (η := vir_handler) (exp_conv (denote_op o)) (lift_unary_post (fun x => ⌜x = v⌝)) -∗
      target_red (η := vir_handler) (<{ %(IId x) = (INSTR_Op o) }>) Ψ.
  Proof.
    iIntros "Hf Hd Hl Ht He".
    iApply (target_instr_local_write1 with "Hf Hd Hl [He] [Ht]"); eauto.
    iIntros "Ht Hd Hs".
    iApply target_red_eq_itree.
    { by rewrite eq_itree_exp_conv_to_instr. }
    iApply (target_red_mono with "[Ht Hd Hs]"); last iApply "He".
    iIntros (??). destruct H as (?&?&?); subst; sfinal.
  Qed.

  Lemma source_instr_pure1 (x : LLVMAst.raw_id) (v : uvalue) o i L Φ:
    ⊢ stack_src i -∗
      ldomain_src i L -∗
      [ x := v ]s i -∗
      ([ x := v ]s i -∗
        ldomain_src i L -∗
        stack_src i -∗
        Φ (Ret tt)) -∗
      source_red (η := vir_handler) (exp_conv (denote_op o)) (lift_unary_post (fun x => ⌜x = v⌝)) -∗
      source_red (η := vir_handler) (<{ %(IId x) = (INSTR_Op o) }>) Φ.
  Proof.
    iIntros "Hf Hd Hl Ht He".
    iApply (source_instr_local_write1 with "Hf Hd Hl [He] [Ht]"); eauto.
    iIntros "Ht Hd Hs".
    iApply source_red_eq_itree.
    { by rewrite eq_itree_exp_conv_to_instr. }
    iApply (source_red_mono with "[Ht Hd Hs]"); last iApply "He".
    iIntros (??). destruct H as (?&?&?); subst; sfinal.
  Qed.

  Lemma source_instr_pure (x : LLVMAst.raw_id) (v : uvalue) o i L Φ:
    x ∉ L ->
    ⊢ stack_src i -∗
      ldomain_src i L -∗
      source_red (η := vir_handler) (exp_conv (denote_op o)) (lift_unary_post (fun x => ⌜x = v⌝)) -∗
      ([ x := v ]s i -∗
        ldomain_src i ({[x]} ∪ L) -∗
        stack_src i -∗
        Φ (Ret tt)) -∗
      source_red (η := vir_handler) (<{ %(IId x) = (INSTR_Op o) }>) Φ.
  Proof.
    iIntros (Hn) "Hf Hd Ht He".
    iApply (source_instr_local_write with "Hf Hd [Ht] [He]"); eauto.
    iIntros "Hd Hs".
    iApply source_red_eq_itree.
    { by rewrite eq_itree_exp_conv_to_instr. }
    iApply (source_red_mono with "[Hd Hs]"); last iApply "Ht".
    iIntros (??). destruct H as (?&?&?); subst; sfinal.
  Qed.

  Lemma sim_instr_pure
    (x_t x_s : LLVMAst.raw_id)
    (v_t v_s v_t' v_s' : uvalue) o_t o_s i_t i_s L_t L_s:
    (* SSA should ensure that this would hold *)
    x_t ∉ L_t ->
    x_s ∉ L_s ->
    ⊢ stack_tgt i_t -∗
      stack_src i_s -∗
      ldomain_tgt i_t L_t -∗
      ldomain_src i_s L_s -∗
      exp_conv (denote_op o_t)
      ⪯
      exp_conv (denote_op o_s)
      [{ (v_t'', v_s''),
              ⌜v_t' = v_t''⌝ ∗ ⌜v_s' = v_s''⌝ }] -∗
      <{ %(IId x_t) = (INSTR_Op o_t) }> ⪯
      <{ %(IId x_s) = (INSTR_Op o_s) }>
      [{ (v1, v2),
          [ x_t := v_t' ]t i_t ∗ [ x_s := v_s' ]s i_s ∗
          ldomain_tgt i_t ({[x_t]} ∪ L_t) ∗ ldomain_src i_s ({[x_s]} ∪ L_s) ∗
          stack_tgt i_t ∗ stack_src i_s }].
  Proof with vsimp.
    iIntros (Ht Hs) "Hf_t Hf_s Hp_t Hp_s H"...
    setoid_rewrite interp_bind.
    iApply sim_expr_bind; iApply exp_conv_to_instr.

    mono: iApply "H" with "[Hf_t Hf_s Hp_t Hp_s]"...
    iDestruct "HΦ" as "(%Hv_t & %Hv_s)"; subst.

    setoid_rewrite instr_conv_localwrite.
    iApply sim_expr_vis.

    mono: iApply (sim_local_write_alloc _ _ _ _ _ _ _ _ Ht Hs with
             "Hp_t Hp_s Hf_t Hf_s")...
    vfinal.
  Qed.

  Lemma sim_instr_alloca
    l_t l_s dt t o i_t S_t i_s S_s `{non_void dt} L_t L_s:
    l_t ∉ L_t ->
    l_s ∉ L_s ->
    ⊢ alloca_tgt i_t S_t -∗
      alloca_src i_s S_s -∗
      ldomain_tgt i_t L_t -∗
      ldomain_src i_s L_s -∗
      stack_tgt i_t -∗
      stack_src i_s -∗
      <{ %(IId l_t) = (INSTR_Alloca dt t o) }> ⪯
      <{ %(IId l_s) = (INSTR_Alloca dt t o) }>
      [{ (v_t, v_s), ∃ l_t0 l_s0,
          ⌜l_t0 ∉ S_t⌝ ∗
          ⌜l_s0 ∉ S_s⌝ ∗
          l_t0 ↦t [make_empty_logical_block dt] ∗
          l_s0 ↦s [make_empty_logical_block dt] ∗
          alloca_tgt i_t ({[l_t0]} ∪ S_t) ∗
          alloca_src i_s ({[l_s0]} ∪ S_s) ∗
          ldomain_tgt i_t ({[ l_t ]} ∪ L_t) ∗
          ldomain_src i_s ({[ l_s ]} ∪ L_s) ∗
          [ l_t := UVALUE_Addr (l_t0, 0%Z) ]t i_t ∗
          [ l_s := UVALUE_Addr (l_s0, 0%Z) ]s i_s ∗
          stack_tgt i_t ∗
          stack_src i_s ∗
          target_block_size l_t0 (Some (N.to_nat (sizeof_dtyp dt))) ∗
          source_block_size l_s0 (Some (N.to_nat (sizeof_dtyp dt))) }].
  Proof with vsimp.
    iIntros (Hnt Hns) "Ha_t Ha_s Hd_t Hd_s Hf_t Hf_s".
    setoid_rewrite interp_bind.
    iApply sim_expr_bind. rewrite /denote_instr_exp; cbn.
    vsimp. Cut... rewrite !interp_vis. Cut...

    mono: iApply (sim_alloca with "Ha_t Ha_s Hf_t Hf_s")
             with "[Hd_t Hd_s] [Hf_t Hf_s Ha_t Ha_s]"...
    vfinal...
    iDestruct "HΦ" as (??????)
      "(Ht & Hs & Ha_t & Ha_s & Hf_t & Hf_s & Hb_t & Hb_s)"; subst...
    Tau. vsimp. rewrite !interp_ret. Base. vsimp.
    rewrite !interp_ret. Base. vsimp.

    setoid_rewrite instr_conv_localwrite. cbn.

    iApply sim_expr_vis.

    mono: iApply (sim_local_write_alloc with "Hd_t Hd_s Hf_t Hf_s")
        with "[Ht Hs Ha_t Ha_s Hb_t Hb_s] [Hf_t Hf_s Hd_t Hd_s]"...
    iDestruct "HΦ" as "(Hl_t & Hl_s & Hd_t & Hd_s & Hs_t & Hs_s)".
    vfinal. sfinal.
  Qed.

  Lemma exp_conv_translate_local_read {id}:
    exp_conv (translate LU_to_exp (trigger (LocalRead id))) ≅
      x <- trigger (LocalRead id) ;; Tau (Ret x).
  Proof.
      rewrite translate_vis. setoid_rewrite interp_vis.
      tau_steps. apply eqit_Vis; intros. tau_steps.
      apply eqit_Tau. by tau_steps.
  Qed.

  Lemma instr_conv_load {dt l} :
    instr_conv (trigger (Load dt l)) ≅
      x <- trigger (Load dt l) ;; Tau (Ret x).
  Proof.
    setoid_rewrite interp_vis; tau_steps.
    apply eqit_Vis; intros. tau_steps.
    apply eqit_Tau. by tau_steps.
  Qed.

  Lemma instr_conv_store {k v} :
    instr_conv (trigger (Store k v)) ≅
      x <- trigger (Store k v) ;; Tau (Ret x).
  Proof.
    setoid_rewrite interp_vis; tau_steps.
    apply eqit_Vis; intros. tau_steps.
    apply eqit_Tau. by tau_steps.
  Qed.

  Lemma instr_conv_localwrite {k v} :
    instr_conv (trigger (LocalWrite k v)) ≅
      x <- trigger (LocalWrite k v) ;; Tau (Ret x).
  Proof.
    setoid_rewrite interp_vis; tau_steps.
    apply eqit_Vis; intros. tau_steps.
    apply eqit_Tau. by tau_steps.
  Qed.

  Ltac normalize_instr_tree e :=
    lazymatch e with
      | ITree.bind (ITree.bind _ _) _ => rewrite bind_bind
      | ITree.bind (Ret _) _ => rewrite bind_ret_l
      | ITree.bind (ret _) _ => rewrite bind_ret_l
      | ITree.bind (Tau _) _ => rewrite bind_tau
      | instr_conv (Ret _) => rewrite instr_conv_ret
      | instr_conv (ITree.bind _ _) => rewrite instr_conv_bind
      | instr_conv (bind _ _) => rewrite instr_conv_bind
      (* Trigger *)
      | instr_conv (trigger (Load _ _)) => rewrite instr_conv_load
      | instr_conv (trigger (Store _ _)) => rewrite instr_conv_store
      | instr_conv (trigger (LocalWrite _ _)) => rewrite instr_conv_localwrite
      | instr_conv (translate exp_to_instr _) =>
          rewrite eq_itree_exp_conv_to_instr
      | exp_conv (translate LU_to_exp _) =>
          rewrite exp_conv_translate_local_read
      | ITree.bind ?e' _ => progress normalize_instr_tree e'
    end.

  Ltac normalize_instr :=
    repeat
      match goal with
        | |- ?e ≅ _ => repeat normalize_instr_tree e
      end.

  Ltac target_simp :=
    do 2 (
    iApply target_red_eq_itree; [ by normalize_instr | ];
    try match goal with
    | |- environments.envs_entails _
        (target_red (ITree.bind _ _) _) => iApply target_red_bind
    | |- environments.envs_entails _
        (target_red (bind _ _) _) => iApply target_red_bind
    | |- environments.envs_entails _
        (target_red (Tau _) _) => iApply target_red_tau
    | |- environments.envs_entails _
        (target_red (Ret _) _) => iApply target_red_base
    end).

  Ltac source_simp :=
    do 2 (
    iApply source_red_eq_itree; [ by normalize_instr | ];
    try match goal with
    | |- environments.envs_entails _
        (source_red (ITree.bind _ _) _) => iApply source_red_bind
    | |- environments.envs_entails _
        (source_red (bind _ _) _) => iApply source_red_bind
    | |- environments.envs_entails _
        (source_red (Tau _) _) => iApply source_red_tau
    | |- environments.envs_entails _
        (source_red (Ret _) _) => iApply source_red_base
    end).

   Lemma target_instr_load1 l dt du b o L i pid id q Ψ size bytes cid:
    is_supported dt ->
    pid ∉ L ->
    ⊢ l ↦{q}t [ LBlock size bytes cid ] -∗
      [ id := UVALUE_Addr (l, 0%Z) ]t i -∗
      ldomain_tgt i L -∗
      stack_tgt i -∗
      ([ id := UVALUE_Addr (l, 0%Z) ]t i -∗
        [ pid := (read_in_mem_block bytes 0%Z dt)]t i -∗
        l ↦{q}t [ LBlock size bytes cid ] -∗
        ldomain_tgt i ({[ pid ]} ∪ L) -∗
        stack_tgt i -∗
        Ψ (Ret ())) -∗
      target_red (η := vir_handler)
        (<{ %(IId pid) = (INSTR_Load b dt (du, EXP_Ident (ID_Local id)) o) }>)
        Ψ.
  Proof with target_simp.
    iIntros (WF Ht) "Hp Hl Hd Hf H"; cbn...

    iApply (target_red_mono with "[Hp Hd H] [Hf Hl]");
      [ | iApply (target_local_read with "Hl Hf"); auto]; cycle 1.
    { iIntros "Hl Hf".
      Unshelve.
      2 : exact (lift_unary_post (fun x => ⌜x = UVALUE_Addr (l, 0%Z)⌝
       ∗ stack_tgt i ∗ [id := UVALUE_Addr (l, 0%Z)]t i)%I).
      iExists _. do 2 (iSplitL ""; [ done | ]). iFrame. }

    iIntros (?) "HP".
    iDestruct "HP" as (???) "(Hf & Hl)".
    iApply target_red_eq_itree.
    { by rewrite H bind_ret_l. }

    target_simp. rewrite H0; cbn...

    destruct (dvalue_eq_dec (d1:=DVALUE_Addr (l, 0%Z)) (d2:=DVALUE_Poison)) eqn: Heq ; [ done | ]...

    change l with ((l, 0%Z).1) at 1.
    iApply (target_load_block with "Hp").

    iIntros "H'"... target_simp.

    iApply (target_local_write_alloc _ _ _ _ _ Ht with "Hd Hf").
    iIntros "Hi H_t H_s"...

    by iSpecialize ("H" with "Hl Hi H' H_t H_s").
  Qed.

   Lemma target_instr_load l dt du b o L i pid v id q Ψ:
    is_supported dt ->
    dvalue_has_dtyp v dt  ->
    pid ∉ L ->
    ⊢ l ↦{q}t v -∗
      [ id := UVALUE_Addr (l, 0%Z) ]t i -∗
      ldomain_tgt i L -∗
      stack_tgt i -∗
      ([ id := UVALUE_Addr (l, 0%Z) ]t i -∗
        [ pid := dvalue_to_uvalue v ]t i -∗
        l ↦{q}t v -∗
        ldomain_tgt i ({[ pid ]} ∪ L) -∗
        stack_tgt i -∗
        Ψ (Ret ())) -∗
      target_red (η := vir_handler)
        (<{ %(IId pid) = (INSTR_Load b dt (du, EXP_Ident (ID_Local id)) o) }>)
        Ψ.
  Proof with target_simp.
    iIntros (WF Hdt Ht) "Hp Hl Hd Hf H"; cbn...
    iApply (target_red_mono with "[Hp Hd H] [Hf Hl]");
      [ | iApply (target_local_read with "Hl Hf"); auto]; cycle 1.
    { iIntros "Hl Hf".
      Unshelve.
      2 : exact (lift_unary_post (fun x => ⌜x = UVALUE_Addr (l, 0%Z)⌝
       ∗ stack_tgt i ∗ [id := UVALUE_Addr (l, 0%Z)]t i)%I).
      iExists _. do 2 (iSplitL ""; [ done | ]). iFrame. }

    iIntros (?) "HP".
    iDestruct "HP" as (???) "(Hf & Hl)".
    iApply target_red_eq_itree; first by rewrite H bind_ret_l.

    target_simp... rewrite H0; cbn...

    destruct (dvalue_eq_dec (d1:=DVALUE_Addr (l, 0%Z)) (d2:=DVALUE_Poison)) eqn: Heq ; [ done | ]...

    iApply (target_red_mono with "[Hd Hf H Hl] [Hp]");
      [ | iApply (target_load _ _ _ _ _ WF Hdt with "Hp")]; cycle 1.

    Unshelve.
    3 : exact (lift_unary_post
          (fun x : uvalue => ⌜x = dvalue_to_uvalue v⌝ ∗ l ↦{q}t v)%I).
    { iIntros.
      iExists _; eauto. }

    iIntros (?) "H'".
    iDestruct "H'" as (???) "H'"; subst... target_simp.

    iApply target_red_eq_itree ; first by rewrite H1... target_simp.

    iApply (target_red_mono with "[H Hl H'] [Hd Hf]");
      [ | iApply (target_local_write_alloc _ _ _ _ _ Ht with "Hd Hf")]; cycle 1.

    Unshelve.
    3 : exact (lift_unary_post
          (fun (_ : ()) => [ pid := dvalue_to_uvalue v ]t i ∗
            ldomain_tgt i ({[pid]} ∪ L) ∗ stack_tgt i))%I.
    { iIntros; iExists _; by iFrame. }

    iIntros (?) "HP".
    iDestruct "HP" as (??)"(Hpl&Hd&Hf)".
    iSpecialize ("H" with "Hl Hpl H' Hd Hf").
    apply EqAxiom.bisimulation_is_eq in H0; rewrite H0...
    by destruct v0.
  Qed.

   Lemma source_instr_load1 l dt du b o L i pid id q Ψ size bytes cid:
    is_supported dt ->
    pid ∉ L ->
    ⊢ l ↦{q}s [ LBlock size bytes cid ] -∗
      [ id := UVALUE_Addr (l, 0%Z) ]s i -∗
      ldomain_src i L -∗
      stack_src i -∗
      ([ id := UVALUE_Addr (l, 0%Z) ]s i -∗
        [ pid := (read_in_mem_block bytes 0%Z dt)]s i -∗
        l ↦{q}s [ LBlock size bytes cid ] -∗
        ldomain_src i ({[ pid ]} ∪ L) -∗
        stack_src i -∗
        Ψ (Ret ())) -∗
      source_red (η := vir_handler)
        (<{ %(IId pid) = (INSTR_Load b dt (du, EXP_Ident (ID_Local id)) o) }>)
        Ψ.
  Proof with source_simp.
    iIntros (WF Ht) "Hp Hl Hd Hf H"; cbn...

    iApply (source_red_mono with "[Hp Hd H] [Hf Hl]");
      [ | iApply (source_local_read with "Hl Hf"); auto]; cycle 1.
    { iIntros "Hl Hf".
      Unshelve.
      2 : exact (lift_unary_post (fun x => ⌜x = UVALUE_Addr (l, 0%Z)⌝
       ∗ stack_src i ∗ [id := UVALUE_Addr (l, 0%Z)]s i)%I).
      iExists _. do 2 (iSplitL ""; [ done | ]). iFrame. }

    iIntros (?) "HP".
    iDestruct "HP" as (???) "(Hf & Hl)".
    iApply source_red_eq_itree.
    { by rewrite H bind_ret_l. }

    source_simp; rewrite H0; cbn...

    destruct (dvalue_eq_dec (d1:=DVALUE_Addr (l, 0%Z)) (d2:=DVALUE_Poison)) eqn: Heq ; [ done | ]...

    change l with ((l, 0%Z).1) at 1.
    iApply (source_load_block with "Hp").

    iIntros "H'"... source_simp.

    iApply (source_local_write_alloc _ _ _ _ _ Ht with "Hd Hf").
    iIntros "Hi H_t H_s"...

    by iSpecialize ("H" with "Hl Hi H' H_t H_s").
  Qed.

  Lemma source_instr_load l dt du b o L i pid v id q Ψ:
    is_supported dt ->
    dvalue_has_dtyp v dt  ->
    pid ∉ L ->
    ⊢ l ↦{q}s v -∗
      [ id := UVALUE_Addr (l, 0%Z) ]s i -∗
      ldomain_src i L -∗
      stack_src i -∗
      ([ id := UVALUE_Addr (l, 0%Z) ]s i -∗
        [ pid := dvalue_to_uvalue v ]s i -∗
        l ↦{q}s v -∗
        ldomain_src i ({[ pid ]} ∪ L) -∗
        stack_src i -∗
        Ψ (Ret ())) -∗
      source_red (η := vir_handler)
        (<{ %(IId pid) = (INSTR_Load b dt (du, EXP_Ident (ID_Local id)) o) }>)
        Ψ.
  Proof with source_simp.
    iIntros (WF Hdt Ht) "Hp Hl Hd Hf H"; cbn...
    iApply (source_red_mono with "[Hp Hd H] [Hf Hl]");
      [ | iApply (source_local_read with "Hl Hf"); auto]; cycle 1.
    { iIntros "Hl Hf".
      Unshelve.
      2 : exact (lift_unary_post (fun x => ⌜x = UVALUE_Addr (l, 0%Z)⌝
       ∗ stack_src i ∗ [id := UVALUE_Addr (l, 0%Z)]s i)%I).
      iExists _. do 2 (iSplitL ""; [ done | ]). iFrame. }

    iIntros (?) "HP".
    iDestruct "HP" as (???) "(Hf & Hl)".
    iApply source_red_eq_itree; first by rewrite H bind_ret_l.

    source_simp... rewrite H0; cbn...

    destruct (dvalue_eq_dec (d1:=DVALUE_Addr (l, 0%Z)) (d2:=DVALUE_Poison)) eqn: Heq ; [ done | ]...

    iApply (source_red_mono with "[Hd Hf H Hl] [Hp]");
      [ | iApply (source_load _ _ _ _ _ WF Hdt with "Hp")]; cycle 1.

    Unshelve.
    3 : exact (lift_unary_post
          (fun x : uvalue => ⌜x = dvalue_to_uvalue v⌝ ∗ l ↦{q}s v)%I).
    { iIntros; iExists _; eauto. }

    iIntros (?) "H'".
    iDestruct "H'" as (???) "H'"; subst.

    iApply source_red_eq_itree; first by rewrite H1... source_simp.

    iApply (source_red_mono with "[H Hl H'] [Hd Hf]");
      [ | iApply (source_local_write_alloc _ _ _ _ _ Ht with "Hd Hf")]; cycle 1.

    Unshelve.
    3 : exact (lift_unary_post
          (fun (_ : ()) => [ pid := dvalue_to_uvalue v ]s i ∗
            ldomain_src i ({[pid]} ∪ L) ∗ stack_src i))%I.
    { iIntros; iExists _; by iFrame. }

    iIntros (?) "HP".
    iDestruct "HP" as (??)"(Hpl&Hd&Hf)".
    iSpecialize ("H" with "Hl Hpl H' Hd Hf").
    apply EqAxiom.bisimulation_is_eq in H0; rewrite H0...
    by destruct v0.
  Qed.

  Lemma target_instr_store b dt val o ptr i n id' v L Ψ dv:
    dvalue_has_dtyp_fun v dt ->
    ⊢ ptr ↦t v -∗
      ldomain_tgt i L -∗
      stack_tgt i -∗
      [ id' := UVALUE_Addr (ptr, 0%Z) ]t i -∗
      target_red (η := vir_handler)
        (exp_conv (denote_exp (Some dt) val))
        (lift_unary_post
           (fun x =>
              ⌜is_concrete x⌝ ∗ ⌜dvalue_to_uvalue dv = x⌝ ∗
              ⌜dvalue_has_dtyp_fun dv dt⌝)) -∗
      (ldomain_tgt i L -∗
        stack_tgt i -∗
        [ id' := UVALUE_Addr (ptr, 0%Z) ]t i -∗
        ptr ↦t dv -∗
        Ψ (Ret ())) -∗
      target_red (η := vir_handler)
        (<{ %(IVoid n) =
            (INSTR_Store b (dt, val) (DTYPE_Pointer, EXP_Ident (ID_Local id')) o) }>)
        Ψ.
  Proof with target_simp.
    iIntros (Htyp) "Hp Hd Hf Hl H HP"; cbn...
    iApply (target_red_mono with "[Hp Hd Hf Hl HP]"); [ |  iApply "H"].

    iIntros (?) "H"; iDestruct "H" as (????) "%Ht"... target_simp.

    rewrite /concretize_or_pick.
    destruct (is_concrete v0); inversion H0; cbn.
    rewrite -H1 uvalue_to_dvalue_of_dvalue_to_uvalue /lift_err...
    destruct (dvalue_has_dtyp_fun dv dt) eqn: Ht'; try inversion Ht...

    iApply (target_red_mono with "[Hp Hd HP] [Hf Hl]");
      [ | iApply (target_local_read with "Hl Hf"); auto]; cycle 1.
    { iIntros "Hl Hf".
      Unshelve.
      2 : exact (lift_unary_post (fun x => ⌜x = UVALUE_Addr (ptr, 0%Z)⌝
       ∗ stack_tgt i ∗ [id' := UVALUE_Addr (ptr, 0%Z)]t i)%I).
      iExists _. do 2 (iSplitL ""; [ done | ]). iFrame. }

    iIntros (?) "HΦ".
    iDestruct "HΦ" as (???) "(Hf & Hl)"... target_simp. subst; cbn...

    destruct (dvalue_eq_dec (d1:=DVALUE_Addr (ptr, 0%Z)) (d2:=DVALUE_Poison)) eqn: Heq ; [ done | ]...

    destruct (dvalue_has_dtyp_fun v dt) eqn: Hdt; subst; try done.
    destruct (dvalue_has_dtyp_fun dv dt) eqn: Hdt'; subst; try done.
    apply dvalue_has_dtyp_fun_sound in Hdt, Hdt'.

    pose proof (dvalue_has_dtyp_serialize _ _ _ Hdt Hdt').
    iApply (target_red_mono with "[Hd Hf Hl HP]");
      last iApply (target_store _ _ _ _ H1 with "Hp").
    { Unshelve.
      2 : exact (lift_unary_post (fun x => ptr ↦t dv))%I.
    iIntros (?) "(%x & %eq & H)"... destruct x...
    iApply target_red_eq_itree; first by rewrite eq...
    target_simp.
    iApply target_red_eq_itree; first by rewrite eq...

    iApply ("HP" with "Hd Hf Hl H"). }
    iIntros "H". iExists _; by iFrame.
  Qed.

  Lemma source_instr_store b dt val o Ψ ptr i n id' v L dv:
    dvalue_has_dtyp_fun v dt ->
    ⊢ ptr ↦s v -∗
      ldomain_src i L -∗
      stack_src i -∗
      [ id' := UVALUE_Addr (ptr, 0%Z) ]s i -∗
      source_red (η := vir_handler)
        (exp_conv (denote_exp (Some dt) val))
        (lift_unary_post
           (fun x =>
              ⌜is_concrete x⌝ ∗ ⌜dvalue_to_uvalue dv = x⌝ ∗
                ⌜dvalue_has_dtyp_fun dv dt⌝)) -∗
      (ldomain_src i L -∗
        stack_src i -∗
        [ id' := UVALUE_Addr (ptr, 0%Z) ]s i -∗
        ptr ↦s dv -∗
        Ψ (Ret ())) -∗
      source_red (η := vir_handler)
        (<{ %(IVoid n) =
            (INSTR_Store b (dt, val)
               (DTYPE_Pointer, EXP_Ident (ID_Local id')) o) }>)
        Ψ.
  Proof with source_simp.
    iIntros (Htyp) "Hp Hd Hf Hl H HP"; cbn...
    iApply (source_red_mono with "[Hp Hd Hf Hl HP]"); [ |  iApply "H"].

    iIntros (?) "H"; iDestruct "H" as (????) "%Ht"... source_simp.

    rewrite /concretize_or_pick; destruct (is_concrete v0); inversion H0; cbn.
    rewrite -H1 uvalue_to_dvalue_of_dvalue_to_uvalue /lift_err...
    destruct (dvalue_has_dtyp_fun dv dt) eqn: Ht'; try done...

    iApply (source_red_mono with "[Hp Hd HP] [Hf Hl]");
      [ | iApply (source_local_read with "Hl Hf"); auto]; cycle 1.
    { iIntros "Hl Hf".
      Unshelve.
      2 : exact (lift_unary_post (fun x => ⌜x = UVALUE_Addr (ptr, 0%Z)⌝
       ∗ stack_src i ∗ [id' := UVALUE_Addr (ptr, 0%Z)]s i)%I).
      iExists _. do 2 (iSplitL ""; [ done | ]). iFrame. }

    iIntros (?) "HΦ"; iDestruct "HΦ" as (???) "(Hf & Hl)"...
    source_simp; subst; cbn...

    destruct (dvalue_eq_dec (d1:=DVALUE_Addr (ptr, 0%Z)) (d2:=DVALUE_Poison)) eqn: Heq ; [ done | ]...

    destruct (dvalue_has_dtyp_fun v dt) eqn: Hdt; subst; try done.
    destruct (dvalue_has_dtyp_fun dv dt) eqn: Hdt'; subst; try done.
    apply dvalue_has_dtyp_fun_sound in Hdt, Hdt'.

    pose proof (dvalue_has_dtyp_serialize _ _ _ Hdt Hdt')...
    iApply (source_red_mono with "[Hd Hf Hl HP]");
      last iApply (source_store _ _ _ _ H1 with "Hp").
    { Unshelve.
      2 : exact (lift_unary_post (fun x => ptr ↦s dv))%I.
    iIntros (?) "(%x & %eq & H)"... destruct x...
    iApply source_red_eq_itree; first by rewrite eq...
    source_simp.
    iApply source_red_eq_itree; first by rewrite eq...

    iApply ("HP" with "Hd Hf Hl H"). }
    iIntros "H". iExists _; by iFrame.
  Qed.

  Lemma source_instr_store1 b dt val o ptr i n id' dv Ψ L size bytes idx:
    ⊢ ptr ↦s [ LBlock size bytes idx ] -∗
      ldomain_src i L -∗
      stack_src i -∗
      [ id' := UVALUE_Addr (ptr, 0%Z) ]s i -∗
      source_red (η := vir_handler)
        (exp_conv (denote_exp (Some dt) val))
        (lift_unary_post
           (fun x =>
              ⌜is_concrete x⌝ ∗ ⌜dvalue_to_uvalue dv = x⌝ ∗
                    ⌜dvalue_has_dtyp_fun dv dt⌝)) -∗
      (ldomain_src i L -∗
        stack_src i -∗
        [ id' := UVALUE_Addr (ptr, 0%Z) ]s i -∗
        ptr ↦s [ LBlock size (add_all_index (serialize_dvalue dv) 0%Z bytes) idx ] -∗
        Ψ (Ret ())) -∗
      source_red (η := vir_handler)
        (<{ %(IVoid n) =
            (INSTR_Store b (dt, val)
               (DTYPE_Pointer, EXP_Ident (ID_Local id')) o) }>)
        Ψ.
  Proof with source_simp. Admitted.
  (*   iIntros "Hp Hd Hf Hl H HP". *)

  (*   cbn. *)
  (*   rewrite /instr_conv. *)
  (*   iApply source_red_eq_itree. *)
  (*   { rewrite interp_bind. *)
  (*     Unshelve. *)
  (*     2 : exact *)
  (*       (x <- exp_conv (denote_exp (Some dt) val) ;; *)
  (*           instr_conv *)
  (*             (dv <- concretize_or_pick x True;; *)
  (*             (if dvalue_has_dtyp_fun dv dt *)
  (*               then *)
  (*               ua <- trigger (LocalRead id');; *)
  (*               da <- pickUnique ua;; *)
  (*               (if dvalue_eq_dec (d1:=da) (d2:=DVALUE_Poison) *)
  (*                 then raiseUB "Store to poisoned address." *)
  (*                 else trigger (Store da dv)) *)
  (*               else raise "Ill-typed store instruction"))). *)
  (*     eapply eq_itree_clo_bind. *)
  (*     { rewrite interp_translate. cbn. *)
  (*       apply eq_itree_interp; first apply eq_handler_instrE_conv. *)
  (*       done. } *)

  (*     intros; subst. *)
  (*     setoid_rewrite interp_bind. *)

  (*     eapply eq_itree_clo_bind; first done. *)
  (*     intros; subst. *)
  (*     destruct (dvalue_has_dtyp_fun u0 dt) eqn: H; eauto; [ | done]. *)
  (*     setoid_rewrite <- translate_cmpE. *)
  (*     setoid_rewrite translate_vis. *)
  (*     setoid_rewrite interp_bind. *)
  (*     rewrite !interp_vis !bind_bind. *)

  (*     eapply eq_itree_clo_bind; first done. *)
  (*     intros; subst. *)
  (*     setoid_rewrite interp_bind. *)
  (*     eapply eq_itree_clo_bind. *)
  (*     { rewrite translate_ret !interp_ret. *)
  (*       apply eqit_Tau. *)
  (*       apply eqit_Ret. reflexivity. } *)
  (*     intros; subst; done. } *)

  (*   iApply source_red_bind. *)
  (*   iApply (source_red_mono with "[Hp Hd Hf Hl HP]"); [ |  iApply "H"]. *)

  (*   iIntros (?) "H". *)
  (*   iDestruct "H" as (????) "%Ht". *)

  (*   iApply source_red_eq_itree. *)
  (*   { rewrite H. rewrite /instr_conv. *)
  (*     rewrite bind_ret_l interp_bind. *)
  (*     rewrite /concretize_or_pick. *)
  (*     destruct (is_concrete v); inversion H0. *)
  (*     cbn. rewrite -H1. *)
  (*     rewrite uvalue_to_dvalue_of_dvalue_to_uvalue. *)
  (*     rewrite /lift_err interp_ret bind_ret_l. *)
  (*     Unshelve. *)
  (*     2 : exact *)
  (*           (x <- trigger (LocalRead id');; *)
  (*            Tau ( *)
  (*             instr_conv *)
  (*               (da <- pickUnique x;; *)
  (*               (if dvalue_eq_dec (d1:=da) (d2:=DVALUE_Poison) *)
  (*                 then raiseUB "Store to poisoned address." *)
  (*                 else trigger (Store da dv))))). *)
  (*     cbn. *)
  (*     destruct (dvalue_has_dtyp_fun dv dt) eqn : Htyp ; [ | done]. *)
  (*     rewrite interp_bind. *)
  (*     rewrite interp_vis; setoid_rewrite interp_ret; cbn. *)
  (*     setoid_rewrite bind_vis. setoid_rewrite bind_ret_l. *)
  (*     cbn. *)
  (*     rewrite bind_vis. *)
  (*     apply eqit_Vis. intros. *)
  (*     rewrite bind_tau. *)
  (*     apply eqit_Tau; rewrite bind_ret_l. reflexivity. } *)

  (*   iApply source_red_bind. *)
  (*   iApply (source_red_mono with "[Hp Hd HP] [Hf Hl]"); *)
  (*     [ | iApply (source_local_read with "Hl Hf"); auto]; cycle 1. *)

  (*   { iIntros "Hl Hf". *)
  (*     Unshelve. *)
  (*     2 : exact (lift_unary_post (fun x => ⌜x = UVALUE_Addr (ptr, 0%Z)⌝ *)
  (*      ∗ stack_src i ∗ [id' := UVALUE_Addr (ptr, 0%Z)]s i)%I). *)
  (*     iExists _. do 2 (iSplitL ""; [ done | ]). iFrame. } *)

  (*   iIntros (?) "HΦ". *)
  (*   iDestruct "HΦ" as (???) "(Hf & Hl)". *)

  (*   destruct (dvalue_eq_dec (d1:=DVALUE_Addr (ptr, 0%Z)) (d2:=DVALUE_Poison)) eqn: Heq ; [ done | ]. *)
  (*   iApply source_red_eq_itree. *)
  (*   { rewrite H2; subst. rewrite bind_ret_l; cbn. *)
  (*     rewrite /instr_conv. *)
  (*     setoid_rewrite bind_ret_l. *)
  (*     rewrite Heq. *)
  (*     rewrite interp_vis. *)
  (*     setoid_rewrite interp_ret. *)
  (*     apply eqit_Tau. *)
  (*     setoid_rewrite bind_vis. *)
  (*     setoid_rewrite bind_ret_l. *)
  (*     Unshelve. *)
  (*     2 : exact (x <- trigger (Store (DVALUE_Addr (ptr, 0%Z)) dv) ;; *)
  (*                Tau (Ret x))%I. *)
  (*     tau_steps. setoid_rewrite bind_ret_l. *)
  (*     reflexivity. } *)

  (*   subst. *)
  (*   iApply source_red_tau. *)
  (*   iApply source_red_bind. *)

  (*   change (ptr) with ((ptr, 0%Z).1) at 1. *)
  (*   iApply (source_store_block with "Hp"). *)
  (*   iIntros "Hp". *)
  (*   iApply source_red_eq_itree. *)
  (*   { by rewrite bind_ret_l. } *)

  (*   iApply source_red_tau; iApply source_red_base. *)

  (*   cbn. *)
  (*   by iSpecialize ("HP" with "Hd Hf Hl Hp"). *)
  (* Qed. *)

  Lemma target_instr_store1 b dt val o ptr i n id' dv Ψ L size bytes idx:
    ⊢ ptr ↦t [ LBlock size bytes idx ] -∗
      ldomain_tgt i L -∗
      stack_tgt i -∗
      [ id' := UVALUE_Addr (ptr, 0%Z) ]t i -∗
      target_red (η := vir_handler)
        (exp_conv (denote_exp (Some dt) val))
        (lift_unary_post
           (fun x =>
              ⌜is_concrete x⌝ ∗ ⌜dvalue_to_uvalue dv = x⌝ ∗
                    ⌜dvalue_has_dtyp_fun dv dt⌝)) -∗
      (ldomain_tgt i L -∗
        stack_tgt i -∗
        [ id' := UVALUE_Addr (ptr, 0%Z) ]t i -∗
        ptr ↦t [ LBlock size (add_all_index (serialize_dvalue dv) 0%Z bytes) idx ] -∗
        Ψ (Ret ())) -∗
      target_red (η := vir_handler)
        (<{ %(IVoid n) =
            (INSTR_Store b (dt, val)
               (DTYPE_Pointer, EXP_Ident (ID_Local id')) o) }>)
        Ψ.
  Proof. Admitted.
  (*   iIntros "Hp Hd Hf Hl H HP". *)

  (*   cbn. *)
  (*   rewrite /instr_conv. *)
  (*   iApply target_red_eq_itree. *)
  (*   { rewrite interp_bind. *)
  (*     Unshelve. *)
  (*     2 : exact *)
  (*       (x <- exp_conv (denote_exp (Some dt) val) ;; *)
  (*           instr_conv *)
  (*             (dv <- concretize_or_pick x True;; *)
  (*             (if dvalue_has_dtyp_fun dv dt *)
  (*               then *)
  (*               ua <- trigger (LocalRead id');; *)
  (*               da <- pickUnique ua;; *)
  (*               (if dvalue_eq_dec (d1:=da) (d2:=DVALUE_Poison) *)
  (*                 then raiseUB "Store to poisoned address." *)
  (*                 else trigger (Store da dv)) *)
  (*               else raise "Ill-typed store instruction"))). *)
  (*     eapply eq_itree_clo_bind. *)
  (*     { rewrite interp_translate. cbn. *)
  (*       apply eq_itree_interp; first apply eq_handler_instrE_conv. *)
  (*       done. } *)

  (*     intros; subst. *)
  (*     setoid_rewrite interp_bind. *)

  (*     eapply eq_itree_clo_bind; first done. *)
  (*     intros; subst. *)
  (*     destruct (dvalue_has_dtyp_fun u0 dt) eqn: H; eauto; [ | done]. *)
  (*     setoid_rewrite <- translate_cmpE. *)
  (*     setoid_rewrite translate_vis. *)
  (*     setoid_rewrite interp_bind. *)
  (*     rewrite !interp_vis !bind_bind. *)

  (*     eapply eq_itree_clo_bind; first done. *)
  (*     intros; subst. *)
  (*     setoid_rewrite interp_bind. *)
  (*     eapply eq_itree_clo_bind. *)
  (*     { rewrite translate_ret !interp_ret. *)
  (*       apply eqit_Tau. *)
  (*       apply eqit_Ret. reflexivity. } *)
  (*     intros; subst; done. } *)

  (*   iApply target_red_bind. *)
  (*   iApply (target_red_mono with "[Hp Hd Hf Hl HP]"); [ |  iApply "H"]. *)

  (*   iIntros (?) "H". *)
  (*   iDestruct "H" as (????) "%Ht". *)

  (*   iApply target_red_eq_itree. *)
  (*   { rewrite H. rewrite /instr_conv. *)
  (*     rewrite bind_ret_l interp_bind. *)
  (*     rewrite /concretize_or_pick. *)
  (*     destruct (is_concrete v); inversion H0. *)
  (*     cbn. rewrite -H1. *)
  (*     rewrite uvalue_to_dvalue_of_dvalue_to_uvalue. *)
  (*     rewrite /lift_err interp_ret bind_ret_l. *)
  (*     Unshelve. *)
  (*     2 : exact *)
  (*           (x <- trigger (LocalRead id');; *)
  (*            Tau ( *)
  (*             instr_conv *)
  (*               (da <- pickUnique x;; *)
  (*               (if dvalue_eq_dec (d1:=da) (d2:=DVALUE_Poison) *)
  (*                 then raiseUB "Store to poisoned address." *)
  (*                 else trigger (Store da dv))))). *)
  (*     cbn. *)
  (*     destruct (dvalue_has_dtyp_fun dv dt) eqn : Htyp ; [ | done]. *)
  (*     rewrite interp_bind. *)
  (*     rewrite interp_vis; setoid_rewrite interp_ret; cbn. *)
  (*     setoid_rewrite bind_vis. setoid_rewrite bind_ret_l. *)
  (*     cbn. *)
  (*     rewrite bind_vis. *)
  (*     apply eqit_Vis. intros. *)
  (*     rewrite bind_tau. *)
  (*     apply eqit_Tau; rewrite bind_ret_l. reflexivity. } *)

  (*   iApply target_red_bind. *)
  (*   iApply (target_red_mono with "[Hp Hd HP] [Hf Hl]"); *)
  (*     [ | iApply (target_local_read with "Hl Hf"); auto]; cycle 1. *)

  (*   { iIntros "Hl Hf". *)
  (*     Unshelve. *)
  (*     2 : exact (lift_unary_post (fun x => ⌜x = UVALUE_Addr (ptr, 0%Z)⌝ *)
  (*      ∗ stack_tgt i ∗ [id' := UVALUE_Addr (ptr, 0%Z)]t i)%I). *)
  (*     iExists _. do 2 (iSplitL ""; [ done | ]). iFrame. } *)

  (*   iIntros (?) "HΦ". *)
  (*   iDestruct "HΦ" as (???) "(Hf & Hl)". *)

  (*   destruct (dvalue_eq_dec (d1:=DVALUE_Addr (ptr, 0%Z)) (d2:=DVALUE_Poison)) eqn: Heq ; [ done | ]. *)
  (*   iApply target_red_eq_itree. *)
  (*   { rewrite H2; subst. rewrite bind_ret_l; cbn. *)
  (*     rewrite /instr_conv. *)
  (*     setoid_rewrite bind_ret_l. *)
  (*     rewrite Heq. *)
  (*     rewrite interp_vis. *)
  (*     setoid_rewrite interp_ret. *)
  (*     apply eqit_Tau. *)
  (*     setoid_rewrite bind_vis. *)
  (*     setoid_rewrite bind_ret_l. *)
  (*     Unshelve. *)
  (*     2 : exact (x <- trigger (Store (DVALUE_Addr (ptr, 0%Z)) dv) ;; *)
  (*                Tau (Ret x))%I. *)
  (*     tau_steps. setoid_rewrite bind_ret_l. *)
  (*     reflexivity. } *)

  (*   subst. *)
  (*   iApply target_red_tau. *)
  (*   iApply target_red_bind. *)

  (*   change (ptr) with ((ptr, 0%Z).1) at 1. *)
  (*   iApply (target_store_block with "Hp"). *)
  (*   iIntros "Hp". *)
  (*   iApply target_red_eq_itree. *)
  (*   { by rewrite bind_ret_l. } *)

  (*   iApply target_red_tau; iApply target_red_base. *)

  (*   cbn. *)
  (*   by iSpecialize ("HP" with "Hd Hf Hl Hp"). *)
  (* Qed. *)

End instr_properties.


Ltac resolve_l := repeat (iSplitL ""; first done).

Ltac process_push :=
  setoid_rewrite interp_bind;
  rewrite !interp_vis !bind_bind; cbn -[denote_cfg denote_code];
  setoid_rewrite interp_ret;
  setoid_rewrite interp_bind;
  setoid_rewrite interp_vis;
  setoid_rewrite bind_bind;
  setoid_rewrite interp_ret;
  do 2 rewrite -bind_bind;
  rewrite -(bind_bind (Vis (call_conv () (subevent () MemPush)) (λ x : (), Ret x)));
  rewrite -(bind_bind (r <- (Vis (call_conv () (subevent () MemPush)) (λ x : (), Ret x)) ;; Tau (Ret r)));
  iApply sim_expr_bind;
  rewrite !bind_bind.

Lemma eq_Handler_instrE_conv:
  eq_Handler
    (λ (T : Type) (x : (λ H : Type, instr_E H) T),
      Vis (instrE_conv T x) Monad.ret)
    (λ (T : Type) (e : instr_E T),
            Vis (call_conv T (LLVMEvents.instr_to_L0' e)) (λ x0 : T, Ret x0)).
Proof.
  repeat intro.
  rewrite /instr_to_L0'.
  destruct a; try destruct e;
    try destruct s; simp call_conv;
    simp instrE_conv;
    try destruct e;
    try destruct s;
    try reflexivity.
Qed.

Section frame_resources.

  Context {Σ : gFunctors} `{!vellirisGS Σ}.

  Definition frame_res γ i A D :=
    (vir_state.stack γ i
        ∗ allocaS γ (current_frame i) A
        ∗ ldomain γ (current_frame i) D)%I.

  Notation source_frame i A D := (frame_res sheapG_heap_source i A D).
  Notation target_frame i A D := (frame_res sheapG_heap_target i A D).

  Record frame := Frame {
    alloca_dom : gset Z;
    local_dom : gset local_loc;
  }.

  Definition empty_frame := Frame ∅ ∅.

  Definition frame_resources_sep i_t i_s (t s : frame) :=
    (target_frame i_t (alloca_dom t) (local_dom t) ∗
        source_frame i_s (alloca_dom s) (local_dom s))%I.

  Definition frame_resources_bij i_t i_s (t s : frame) :=
    ((alloca_tgt i_t (alloca_dom t) ∗ alloca_src i_s (alloca_dom s)) ∗
      (ldomain_tgt i_t (local_dom t) ∗ ldomain_src i_s (local_dom s)) ∗
      (stack_tgt i_t ∗ stack_src i_s))%I.

  Definition frame_resources_exist i_t i_s :=
    (∃ t s, frame_resources_bij i_t i_s t s)%I.

  Definition alloca_own_domain (C : gmap (loc * loc) Qp) (t s : frame) :=
    (checkout C ∗
      ∃ FA_t FA_s,
        ⌜list_to_set FA_t = alloca_dom t⌝ ∗
        ⌜list_to_set FA_s = alloca_dom s⌝ ∗
        ⌜NoDup FA_t⌝ ∗ ⌜NoDup FA_s⌝ ∗
        ([∗ list] k ↦ l_t; l_s ∈ FA_t; FA_s,
          (l_t, 0%Z) ↔h (l_s, 0%Z) ∗ ⌜C !! (l_t, l_s) = None⌝))%I.

  Definition frame_resources_own i_t i_s (t s : frame) C :=
    (frame_resources_bij i_t i_s t s ∗ alloca_own_domain C t s)%I.

  Definition frame_resources_own_exist i_t i_s C :=
    (∃ t s, frame_resources_own i_t i_s t s C)%I.

  Lemma frame_resources_to_exist i_t i_s t s:
    frame_resources_bij i_t i_s t s -∗
    frame_resources_exist i_t i_s.
  Proof.
    iIntros "H"; by iExists _, _.
  Qed.

  Definition initial_frame_res i_t i_s C : iPropI Σ :=
    checkout C ∗ frame_resources_sep i_t i_s empty_frame empty_frame.

  Lemma frame_resources_eq i_t i_s t s:
    frame_resources_sep i_t i_s t s⊣⊢ frame_resources_bij i_t i_s t s.
  Proof.
    iSplitL; iIntros "Hf"; destruct t, s.
    { iDestruct "Hf" as "(Ht&Hs)"; cbn.
      iDestruct "Ht" as "(Hs_t&Ha_t&Hd_t)".
      iDestruct "Hs" as "(Hs_s&Ha_s&Hd_s)"; iFrame. }
    { iDestruct "Hf" as
        "((Ha_t&Ha_s)&(Hd_t&Hd_s)&(?&?)&?)"; iFrame. }
  Qed.

End frame_resources.

Ltac destruct_frame_resources :=
  match goal with
  | [ |- context[environments.Esnoc _
          (INamed ?H)
          (frame_resources_sep _ _ _ _)] ] =>
      iDestruct H as "((Hf_t & Ha_t & Hd_t) & (Hf_s & Ha_s & Hd_s))"
  end.

Section exp_laws.

  Context {Σ : gFunctors} `{!vellirisGS Σ}.


  Lemma interp_L2_bind {X R} (e : _ X) (k : _ -> _ R) σ:
    ⟦ ITree.bind e k ⟧ σ ≅
      ITree.bind (⟦ e ⟧ σ) (fun '(a, b) => ⟦ k b ⟧ a).
  Proof.
    setoid_rewrite StateFacts.interp_state_bind.
    eapply eq_itree_clo_bind; first done.
    intros; destruct u1; by subst.
  Qed.

  Lemma interp_L2_tau {X} (e : _ X) σ:
    ⟦ Tau e ⟧ σ ≅ Tau (⟦ e ⟧ σ).
  Proof.
    by setoid_rewrite StateFacts.interp_state_tau.
  Qed.

  Lemma source_red_denote_exp_i32 x:
    ⊢ source_red (exp_conv (denote_exp (Some (i32)) (EXP_Integer x)))
      (lift_unary_post
        (λ uv : Handlers.LLVMEvents.DV.uvalue,
        ⌜Handlers.LLVMEvents.DV.is_concrete uv⌝ ∗
        ⌜(DVALUE_I32 (DynamicValues.Int32.repr x)) ̂ = uv⌝ ∗
        ⌜Handlers.LLVMEvents.DV.dvalue_has_dtyp_fun
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
        ⌜Handlers.LLVMEvents.DV.dvalue_has_dtyp_fun
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

  Lemma sim_instr_alloca1
    l_t l_s dt t o i_t i_s `{non_void dt} F_t F_s:
    let S_t := alloca_dom F_t in
    let S_s := alloca_dom F_s in
    let L_t := local_dom F_t in
    let L_s := local_dom F_s in
    l_t ∉ L_t ->
    l_s ∉ L_s ->
    ⊢ frame_resources_sep i_t i_s
        (Frame S_t L_t) (Frame S_s L_s) -∗
      <{ %(IId l_t) = (INSTR_Alloca dt t o) }> ⪯
      <{ %(IId l_s) = (INSTR_Alloca dt t o) }>
      [{ (v_t, v_s), ∃ l_t0 l_s0,
          ⌜l_t0 ∉ S_t⌝ ∗
          ⌜l_s0 ∉ S_s⌝ ∗
          frame_resources_sep i_t i_s
              (Frame ({[l_t0]} ∪ S_t) ({[l_t]} ∪ L_t))
              (Frame ({[l_s0]} ∪ S_s) ({[l_s]} ∪ L_s)) ∗
          l_t0 ↦t [make_empty_logical_block dt] ∗
          l_s0 ↦s [make_empty_logical_block dt] ∗
          [ l_t := UVALUE_Addr (l_t0, 0%Z) ]t i_t ∗
          [ l_s := UVALUE_Addr (l_s0, 0%Z) ]s i_s ∗
          target_block_size l_t0 (Some (N.to_nat (sizeof_dtyp dt))) ∗
          source_block_size l_s0 (Some (N.to_nat (sizeof_dtyp dt))) }].
  Proof.
    cbn.
    iIntros (Ht Hs) "HF".
    destruct_frame_resources.
    iApply sim_expr_bupd_mono;
      last iApply (sim_instr_alloca with "Ha_t Ha_s Hd_t Hd_s Hf_t Hf_s"); eauto.
    cbn.
    iIntros (??) "H".
    iDestruct "H" as (??????) "H".
    iDestruct "H" as "(?&?&?&?&?&?&?&?&?&?&?&?)".
    iExists _, _; do 2 (iSplitL ""; first done).
    iExists _, _; by iFrame.
    Unshelve. all : eauto.
  Qed.

  Lemma sim_instr_alloca_checkout
    l_t l_s dt t o i_t S_t i_s S_s `{non_void dt} L_t L_s C:
    l_t ∉ L_t ->
    l_s ∉ L_s ->
    ⊢ alloca_tgt i_t S_t -∗
      alloca_src i_s S_s -∗
      ldomain_tgt i_t L_t -∗
      ldomain_src i_s L_s -∗
      stack_tgt i_t -∗
      stack_src i_s -∗
      checkout C -∗
      <{ %(IId l_t) = (INSTR_Alloca dt t o) }> ⪯
      <{ %(IId l_s) = (INSTR_Alloca dt t o) }>
      [{ (v_t, v_s), ∃ l_t0 l_s0,
          ⌜l_t0 ∉ S_t⌝ ∗
          ⌜l_s0 ∉ S_s⌝ ∗
          l_t0 ↦t [make_empty_logical_block dt] ∗
          l_s0 ↦s [make_empty_logical_block dt] ∗
          alloca_tgt i_t ({[l_t0]} ∪ S_t) ∗
          alloca_src i_s ({[l_s0]} ∪ S_s) ∗
          ldomain_tgt i_t ({[ l_t ]} ∪ L_t) ∗
          ldomain_src i_s ({[ l_s ]} ∪ L_s) ∗
          [ l_t := UVALUE_Addr (l_t0, 0%Z) ]t i_t ∗
          [ l_s := UVALUE_Addr (l_s0, 0%Z) ]s i_s ∗
          stack_tgt i_t ∗
          stack_src i_s ∗
          target_block_size l_t0 (Some (N.to_nat (sizeof_dtyp dt))) ∗
          source_block_size l_s0 (Some (N.to_nat (sizeof_dtyp dt))) ∗
          checkout C ∗
          ⌜C !! (l_t0, l_s0) = None⌝
      }].
  Proof.
  (*   iIntros (Hnt Hns) "Ha_t Ha_s Hd_t Hd_s Hf_t Hf_s HC". *)
  (*   setoid_rewrite interp_bind. *)
  (*   iApply sim_expr_bind. *)

  (*   assert (Heq : forall dt, *)
  (*       instr_conv (trigger (Alloca dt)) ≅ *)
  (*         x <- trigger (Alloca dt) ;; Tau (Ret x)). *)
  (*   { intros. rewrite /instr_conv. *)
  (*     rewrite interp_vis. setoid_rewrite interp_ret. *)

  (*     rewrite /subevent /resum /ReSum_inr /cat /Cat_IFun /inr_ /Inr_sum1. *)
  (*     simp instrE_conv. rewrite bind_trigger. *)
  (*     reflexivity. } *)
  (*   setoid_rewrite Heq. *)

  (*   iApply sim_expr_bind. *)

  (*   iApply (sim_expr_bupd_mono with *)
  (*            "[HC Hd_t Hd_s] [Hf_t Hf_s Ha_t Ha_s]"); *)
  (*     [ | iApply (sim_alloca with "Ha_t Ha_s Hf_t Hf_s") ; eauto ]. *)
  (*   cbn. iIntros (??) "H". *)
  (*   iDestruct "H" as (??????????) *)
  (*     "(Ht & Hs & Ha_t & Ha_s & Hf_t & Hf_s & Hb_t & Hb_s)"; subst. *)

  (*   rewrite H H0 !bind_ret_l; subst. *)
  (*   iApply sim_expr_tau. *)
  (*   iApply sim_expr_base. *)
  (*   rewrite !bind_ret_l. *)

  (*   iApply sim_update_si. *)
  (*   iModIntro; iIntros (??) "SI". *)
  (*   iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & %WF_SI & SI)". *)

  (*   iAssert ((¬ ⌜set_Exists (λ '(b_t', b_s'), l_t0 = b_t') S⌝)%I) as "%Hext_t". *)
  (*   { iIntros (([b_t' b_s'] & Hin & <-)). *)
  (*     iDestruct "Hbij" as "(Hbij & Hheap)". *)
  (*     iPoseProof (big_sepS_elem_of with "Hheap") as "Hr"; first by apply Hin. *)
  (*     iDestruct "Hr" as (? v_t' v_s') "(Hr_t & Ha_t' & Ha_s')". *)
  (*     by iApply (heap_block_size_excl with "Hb_t Ha_t'"). } *)

  (*   iPoseProof (lb_rel_empty_blocks dt) as "Hrel". *)

  (*   destruct_HC "Hh_s". *)
  (*   iDestruct (ghost_var_agree with "Hf_s HCF") as %Hd_s; subst. *)
  (*   iDestruct (ghost_var_agree with "HC H_c") as %Hc_s; subst. *)
  (*   rewrite allocaS_eq. *)
  (*   iDestruct (ghost_var_agree with "Ha_s HA") as %Hd_s; subst. *)

  (*   iDestruct "Hh_t" as (cft hFt) *)
  (*       "(Hσ_t&HB_t&HCF_t&HA_t&HL_t&HD_t&HSA_t&HG_t&%Hdup_t&%Hbs_t&%Hwf_t)". *)
  (*   iDestruct (ghost_var_agree with "Hf_t HCF_t") as %Hd_t; subst. *)
  (*   iDestruct (ghost_var_agree with "Ha_t HA_t") as %Hd_t; subst. *)
  (*   iFrame. *)

  (*   iSplitR "Hd_t Hd_s HC Ha_t Ha_s Ht Hs Hb_t Hb_s Hf_t Hf_s". *)
  (*   { iExists _, S, G; iFrame. *)
  (*     iSplitR "HB_t HCF_t HA_t HL_t HD_t HSA_t". *)
  (*     { iModIntro; iExists _, _; iFrame. done. } *)
  (*     iSplitR "". *)
  (*     { iModIntro; iExists _, _; iFrame. done. } *)
  (*     iModIntro. iPureIntro. set_solver. } *)

  (*   setoid_rewrite instr_conv_localwrite. cbn. *)

  (*   iApply sim_expr_vis. *)

  (*   iApply (sim_expr_bupd_mono with *)
  (*            "[HC Ht Hs Ha_t Ha_s Hb_t Hb_s] [Hf_t Hf_s Hd_t Hd_s]"); *)
  (*     [ | iApply (sim_local_write_alloc with "Hd_t Hd_s Hf_t Hf_s") ; eauto ]. *)
  (*   cbn. *)
  (*   iIntros (??) "H". *)
  (*   iDestruct "H" as (????) "(Hp_t & Hp_s & Hf_t & Hf_s)". *)
  (*   rewrite H1 H2 !bind_ret_l. *)

  (*   iApply sim_expr_tau; iApply sim_expr_base. *)
  (*   iExists tt, tt; destruct v1, v2. *)
  (*   do 2 (iSplitL ""; [ done |]). *)
  (*   iExists l_t0, l_s0. base. iFrame. *)
  (*   iDestruct "Hf_s" as "(?&?&?)"; iFrame. *)
  (*   iPureIntro. clear -WF_SI Hext_t. *)
  (*   apply not_elem_of_dom_1. *)
  (*   set_solver. *)
  (* Qed. *)
    Admitted.
  
  Lemma source_instr_bij_load {R} l dt b du o L i pid id Ψ l_t C (e_t : _ R) (k : _ R):
    pid ∉ L ->
    ⊢ l_t ↔h l -∗
      checkout C -∗
      [ id := UVALUE_Addr l ]s i -∗
      ldomain_src i L -∗
      stack_src i -∗
      (∀ v, [ id := UVALUE_Addr l ]s i -∗
        [ pid := v ]s i -∗
        checkout C -∗
        ldomain_src i ({[ pid ]} ∪ L) -∗
        stack_src i -∗
        e_t ⪯ k [{ Ψ }]) -∗
      e_t ⪯ (IId pid) :== (INSTR_Load b dt (du, EXP_Ident (ID_Local id)) o) ;;; k
      [{ Ψ }].
  Proof.
  Admitted.
  (*   iIntros (Ht) "#Hbij HC Hl Hd Hf H". *)

  (*   cbn. rewrite !instr_conv_bind bind_bind. *)
  (*   rewrite !translate_vis. setoid_rewrite interp_vis. *)
  (*   rewrite bind_bind. do 2 setoid_rewrite translate_ret. *)
  (*   setoid_rewrite interp_ret. setoid_rewrite bind_tau. *)
  (*   setoid_rewrite bind_ret_l. *)
  (*   iApply source_red_sim_expr; iApply source_red_bind. *)

  (*   iApply (source_red_mono with "[H Hd HC] [Hl Hf]"); cycle 1. *)
  (*   { iPoseProof (source_local_read with "Hl Hf") as "H'". *)
  (*     match goal with *)
  (*       | |- context[ environments.envs_entails _ (source_red ?x _) ] => *)
  (*           replace x with (ITree.trigger (subevent (F := language.L0 vir_lang) _ (LocalRead id))) *)
  (*     end. *)
  (*     2 : done. iApply "H'". *)
  (*     iIntros "Hl Hst". *)
  (*     Unshelve. *)
  (*     2 : exact (fun x => ⌜x = Ret (UVALUE_Addr l)⌝ ∗ [ id := UVALUE_Addr l ]s i ∗ stack_src i)%I. *)
  (*     by iFrame. } *)
  (*   cbn. *)
  (*   iIntros (?) "(%Hs & Hid & Hs)" ;subst. *)
  (*   iApply source_red_base. *)
  (*   setoid_rewrite bind_ret_l. *)
  (*   iApply sim_expr_tauL. *)
  (*   setoid_rewrite instr_conv_bind. cbn. *)
  (*   setoid_rewrite instr_conv_ret. *)
  (*   rewrite bind_ret_l. *)

  (*   destruct (dvalue_eq_dec (d1:=DVALUE_Addr l) (d2:=DVALUE_Poison)) *)
  (*     eqn: Heq ; [ done | ]. *)

  (*   setoid_rewrite instr_conv_bind. *)
  (*   rewrite bind_bind; setoid_rewrite interp_vis. *)
  (*   rewrite bind_bind. *)
  (*   rewrite sim_expr_eq. *)

  (*   iIntros (??) "SI". *)
  (*   rewrite interp_L2_bind. *)
  (*   rewrite bij_laws.interp_L2_load. *)
  (*   destruct (vmem σ_s); cbn -[state_interp]. *)

  (*   destruct (read (p, f) l dt) eqn : Hread. *)
  (*   (* UB case *) *)
  (*   { rewrite bind_tau. iApply sim_coind_tauR. *)
  (*     rewrite !bind_bind bind_vis. *)
  (*     iApply sim_coind_ub. } *)
  (*   rewrite bind_ret_l. do 2 setoid_rewrite bind_tau. *)
  (*   rewrite bind_ret_l. *)
  (*   setoid_rewrite StateFacts.interp_state_bind. *)
  (*   repeat iApply sim_coind_tauR. *)
  (*   setoid_rewrite StateFacts.interp_state_tau. *)
  (*   rewrite !bind_tau. *)
  (*   repeat iApply sim_coind_tauR. *)
  (*   rewrite interp_ret. *)
  (*   setoid_rewrite StateFacts.interp_state_ret. *)
  (*   rewrite bind_ret_l. *)

  (*   cbn. *)
  (*   rewrite !bind_bind. rewrite StateFacts.interp_state_bind. *)

  (*   iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij' & SI)". *)

  (*   unfold interp_L2. rewrite StateFacts.interp_state_vis. *)
  (*   simp instrE_conv. rewrite /instr_to_L0 bind_tau; cbn; rewrite bind_bind. *)
  (*   rewrite bind_tau. *)
  (*   iApply sim_coind_tauR. *)
  (*   rewrite /handle_local_stack; cbn. destruct p. *)
  (*   rewrite bind_bind. *)
  (*   destruct (vlocal σ_s); cbn. *)
  (*   rewrite /ITree.map !bind_bind !bind_ret_l bind_tau. *)
  (*   iApply sim_coind_tauR. rewrite StateFacts.interp_state_ret. *)
  (*   rewrite bind_ret_l. rewrite StateFacts.interp_state_bind. *)
  (*   rewrite StateFacts.interp_state_tau. rewrite bind_tau. *)
  (*   iApply sim_coind_tauR. rewrite interp_ret StateFacts.interp_state_ret. *)
  (*   rewrite bind_ret_l. cbn. *)

  (*   iSpecialize ("H" with "Hid"). *)

  (*   iMod ((lheap_domain_alloc _ _ u) *)
  (*          with "Hd Hs Hh_s") as "(Hh_s & Hp_s & Hf_s & Hd_s)"; [done | ]. *)

  (*   iDestruct (lheap_lookup with "Hh_s Hf_s Hp_s") as %Hl_s; cbn. *)

  (*   iSpecialize ("H" with "Hp_s HC Hd_s Hf_s"). *)
  (*   iApply "H". *)
  (*   iExists C0, S, G; iFrame. *)
  (* Qed. *)

End exp_laws.


Section more_properties.

  Context {Σ : gFunctors} `{!vellirisGS Σ}.


   Lemma target_instr_load_in l dt du b o i pid id q Ψ u v:
    is_supported dt ->
    dvalue_has_dtyp v dt ->
    ⊢ l ↦{q}t v -∗
      [ id := UVALUE_Addr (l, 0%Z) ]t i -∗
      [ pid := u ]t i -∗
      stack_tgt i -∗
      ([ id := UVALUE_Addr (l, 0%Z) ]t i -∗
        [ pid := dvalue_to_uvalue v]t i -∗
        l ↦{q}t v -∗
        stack_tgt i -∗
        Ψ (Ret ())) -∗
      target_red (η := vir_handler)
        (<{ %(IId pid) = (INSTR_Load b dt (du, EXP_Ident (ID_Local id)) o) }>)
        Ψ.
  Proof.
    iIntros (WF Hτ) "Hp Hl Hid Hf H".

    cbn. rewrite /instr_conv.
    iApply target_red_eq_itree.
  (*   { rewrite interp_bind interp_translate; cbn. *)
  (*     rewrite translate_vis interp_vis bind_bind. *)
  (*     setoid_rewrite translate_ret. *)
  (*     setoid_rewrite interp_ret. *)
  (*     setoid_rewrite bind_tau. *)
  (*     setoid_rewrite bind_ret_l. *)
  (*     rewrite /LU_to_exp; cbn; rewrite /exp_to_instr. *)
  (*     simp instrE_conv. reflexivity. } *)

  (*   iApply target_red_bind. *)
  (*   iApply (target_red_mono with "[Hp Hid H] [Hf Hl]"); *)
  (*     [ | iApply (target_local_read with "Hl Hf"); auto]; cycle 1. *)
  (*   { iIntros "Hl Hf". *)
  (*     Unshelve. *)
  (*     2 : exact (lift_unary_post (fun x => ⌜x = UVALUE_Addr (l, 0%Z)⌝ *)
  (*      ∗ stack_tgt i ∗ [id := UVALUE_Addr (l, 0%Z)]t i)%I). *)
  (*     iExists _. do 2 (iSplitL ""; [ done | ]). iFrame. } *)

  (*   iIntros (?) "HP". *)
  (*   iDestruct "HP" as (???) "(Hf & Hl)". *)
  (*   iApply target_red_eq_itree. *)
  (*   { by rewrite H bind_ret_l. } *)

  (*   iApply target_red_tau. *)

  (*   rewrite H0; cbn. *)

  (*   iApply target_red_eq_itree. *)
  (*   { setoid_rewrite interp_bind. *)
  (*     setoid_rewrite interp_ret. *)
  (*     rewrite bind_ret_l. reflexivity. } *)

  (*   destruct (dvalue_eq_dec (d1:=DVALUE_Addr (l, 0%Z)) (d2:=DVALUE_Poison)) eqn: Heq ; [ done | ]. *)
  (*   iApply target_red_eq_itree. *)
  (*   { rewrite interp_bind. *)

  (*     cbn. *)
  (*     setoid_rewrite interp_vis. *)
  (*     setoid_rewrite interp_ret. *)
  (*     Unshelve. *)
  (*     2 : exact (x <- trigger (Load dt (DVALUE_Addr (l, 0%Z))) ;; *)
  (*                x <- Tau (trigger (LocalWrite pid x)) ;; Tau (Ret x)). *)
  (*     rewrite bind_bind. *)
  (*     setoid_rewrite bind_tau. *)
  (*     setoid_rewrite bind_ret_l. *)
  (*     repeat setoid_rewrite bind_vis. *)
  (*     repeat setoid_rewrite bind_ret_l. *)
  (*     eapply eqit_Vis; intros. *)
  (*     apply eqit_Tau. *)
  (*     eapply eqit_Vis; intros. reflexivity. } *)

  (*   iApply target_red_bind. *)

  (*   change l with ((l, 0%Z).1) at 1. *)
  (*   iApply (target_load with "Hp"); auto. *)

  (*   iIntros "H'". *)
  (*   iApply target_red_eq_itree. *)
  (*   { by rewrite bind_ret_l !bind_tau. } *)

  (*   iApply target_red_tau; iApply target_red_bind. *)

  (*   iApply (target_local_write with "Hid Hf"). *)
  (*   iIntros "Hi H_t". *)

  (*   iApply target_red_eq_itree. *)
  (*   { by rewrite bind_ret_l. } *)

  (*   iApply target_red_tau; iApply target_red_base. *)

  (*   cbn. *)
  (*   by iSpecialize ("H" with "Hl Hi H' H_t"). *)
  (* Qed. *)
  Admitted.

   Lemma source_instr_load_in l dt du b o i pid id q Ψ u v:
    is_supported dt ->
    dvalue_has_dtyp v dt  ->
    ⊢ l ↦{q}s v -∗
      [ id := UVALUE_Addr (l, 0%Z) ]s i -∗
      [ pid := u ]s i -∗
      stack_src i -∗
      ([ id := UVALUE_Addr (l, 0%Z) ]s i -∗
        [ pid := dvalue_to_uvalue v ]s i -∗
        l ↦{q}s v -∗
        stack_src i -∗
        Ψ (Ret ())) -∗
      source_red (η := vir_handler)
        (<{ %(IId pid) = (INSTR_Load b dt (du, EXP_Ident (ID_Local id)) o) }>)
        Ψ.
  Proof.
    Admitted.
  (*   iIntros (WF Hdt) "Hp Hl Hid Hf H". *)

  (*   cbn. rewrite /instr_conv. *)
  (*   iApply source_red_eq_itree. *)
  (*   { rewrite interp_bind interp_translate; cbn. *)
  (*     rewrite translate_vis interp_vis bind_bind. *)
  (*     setoid_rewrite translate_ret. *)
  (*     setoid_rewrite interp_ret. *)
  (*     setoid_rewrite bind_tau. *)
  (*     setoid_rewrite bind_ret_l. *)
  (*     rewrite /LU_to_exp; cbn; rewrite /exp_to_instr. *)
  (*     simp instrE_conv. reflexivity. } *)

  (*   iApply source_red_bind. *)
  (*   iApply (source_red_mono with "[Hp Hid H] [Hf Hl]"); *)
  (*     [ | iApply (source_local_read with "Hl Hf"); auto]; cycle 1. *)
  (*   { iIntros "Hl Hf". *)
  (*     Unshelve. *)
  (*     2 : exact (lift_unary_post (fun x => ⌜x = UVALUE_Addr (l, 0%Z)⌝ *)
  (*      ∗ stack_src i ∗ [id := UVALUE_Addr (l, 0%Z)]s i)%I). *)
  (*     iExists _. do 2 (iSplitL ""; [ done | ]). iFrame. } *)

  (*   iIntros (?) "HP". *)
  (*   iDestruct "HP" as (???) "(Hf & Hl)". *)
  (*   iApply source_red_eq_itree. *)
  (*   { by rewrite H bind_ret_l. } *)

  (*   iApply source_red_tau. *)

  (*   rewrite H0; cbn. *)

  (*   iApply source_red_eq_itree. *)
  (*   { setoid_rewrite interp_bind. *)
  (*     setoid_rewrite interp_ret. *)
  (*     rewrite bind_ret_l. reflexivity. } *)

  (*   destruct (dvalue_eq_dec (d1:=DVALUE_Addr (l, 0%Z)) (d2:=DVALUE_Poison)) eqn: Heq ; [ done | ]. *)
  (*   iApply source_red_eq_itree. *)
  (*   { rewrite interp_bind. *)

  (*     cbn. *)
  (*     setoid_rewrite interp_vis. *)
  (*     setoid_rewrite interp_ret. *)
  (*     Unshelve. *)
  (*     2 : exact (x <- trigger (Load dt (DVALUE_Addr (l, 0%Z))) ;; *)
  (*                x <- Tau (trigger (LocalWrite pid x)) ;; Tau (Ret x)). *)
  (*     rewrite bind_bind. *)
  (*     setoid_rewrite bind_tau. *)
  (*     setoid_rewrite bind_ret_l. *)
  (*     repeat setoid_rewrite bind_vis. *)
  (*     repeat setoid_rewrite bind_ret_l. *)
  (*     eapply eqit_Vis; intros. *)
  (*     apply eqit_Tau. *)
  (*     eapply eqit_Vis; intros. reflexivity. } *)

  (*   iApply source_red_bind. *)

  (*   change l with ((l, 0%Z).1) at 1. *)
  (*   iApply (source_load with "Hp"); auto. *)

  (*   iIntros "H'". *)

  (*   iApply source_red_eq_itree. *)
  (*   { by rewrite bind_ret_l !bind_tau. } *)

  (*   iApply source_red_tau; iApply source_red_bind. *)

  (*   iApply (source_local_write with "Hid Hf"). *)
  (*   iIntros "Hi H_t". *)

  (*   iApply source_red_eq_itree. *)
  (*   { by rewrite bind_ret_l. } *)

  (*   iApply source_red_tau; iApply source_red_base. *)
  (*   cbn. *)
  (*   by iSpecialize ("H" with "Hl Hi H' H_t"). *)
  (* Qed. *)

  Lemma sim_instr_load_bij_Some
    l_t l_s dt o i_t i_s `{non_void dt} L_t L_s C id_t id_s b du l_t0 l_s0 q:
    l_t0 ∉ L_t ->
    l_s0 ∉ L_s ->
    dtyp_WF dt ->
    (q < 1)%Qp ->
    C !! (l_t.1, l_s.1) = Some q ->
    ⊢ l_t ↔h l_s -∗
      checkout C -∗
      ldomain_tgt i_t L_t -∗
      ldomain_src i_s L_s -∗
      stack_tgt i_t -∗
      stack_src i_s -∗
      [ id_t := UVALUE_Addr l_t ]t i_t -∗
      [ id_s := UVALUE_Addr l_s ]s i_s -∗
      <{ %(IId l_t0) =
          (INSTR_Load b dt (du, EXP_Ident (ID_Local id_t)) o) }> ⪯
      <{ %(IId l_s0) =
          (INSTR_Load b dt (du, EXP_Ident (ID_Local id_s)) o)}>
      [{ (v_t, v_s),
          checkout C ∗
          ldomain_tgt i_t ({[ l_t0 ]} ∪ L_t) ∗
          ldomain_src i_s ({[ l_s0 ]} ∪ L_s) ∗
          stack_tgt i_t ∗
          stack_src i_s ∗
          [ id_t := UVALUE_Addr l_t ]t i_t ∗
          [ id_s := UVALUE_Addr l_s ]s i_s ∗
          ∃ v_t v_s,
          [ l_t0 := v_t ]t i_t ∗ [ l_s0 := v_s ]s i_s ∗
          uval_rel v_t v_s
      }].
  Proof.
    iIntros (Ht Hs WF Hq Hc) "#Hl HC Hd_t Hd_s Hf_t Hf_s Hid_t Hid_s".
    setoid_rewrite interp_bind.
  (*   iApply sim_expr_bind; iApply exp_conv_to_instr. *)

  (*   iApply (sim_expr_bupd_mono with "[HC Hd_t Hd_s]"); *)
  (*     [ | iApply (sim_local_read_exp_conv with "Hf_t Hf_s Hid_t Hid_s")]. *)

  (*   cont. *)
  (*   iDestruct "H" as (??) "(Hf_t & Hf_s & Hid_t & Hid_s)"; subst. *)
  (*   cbn. rewrite !bind_ret_l. *)
  (*   destruct (dvalue_eq_dec *)
  (*               (d1:=DVALUE_Addr l_t) *)
  (*               (d2:=DVALUE_Poison)) eqn: Heq ; [ done | ]; clear Heq. *)
  (*   destruct (dvalue_eq_dec *)
  (*               (d1:=DVALUE_Addr l_s) *)
  (*               (d2:=DVALUE_Poison)) eqn: Heq ; [ done | ]; clear Heq. *)
  (*   rewrite !interp_bind !interp_vis !bind_bind; iApply sim_expr_bind. *)

  (*   iApply (sim_expr_bupd_mono with "[Hd_t Hd_s Hf_t Hf_s Hid_t Hid_s]"); *)
  (*     last iApply (bij_laws.sim_bij_load_Some with "Hl HC"); eauto. *)

  (*   cont. *)

  (*   rewrite !bind_tau !interp_ret !bind_ret_l. *)
  (*   iApply sim_expr_tau. *)
  (*   setoid_rewrite instr_conv_localwrite. *)

  (*   iApply sim_expr_vis. *)

  (*   iApply (sim_expr_bupd_mono with "[Hid_t Hid_s H]"); last *)
  (*     iApply (sim_local_write_alloc _ _ _ _ _ _ _ _ Ht Hs with *)
  (*             "Hd_t Hd_s Hf_t Hf_s"). *)
  (*   iDestruct "H" as "(#Hv & HC)". *)

  (*   cont. *)
  (*   iApply sim_expr_tau; iApply sim_expr_base; iFrame. *)
  (*   iDestruct "H" as "(Hid_t & Hid_s & Hd_t & Hd_s & Hs_t & Hs_s)". *)
  (*   iExists _, _; iFrame; try done. *)
  (*   do 2 (iSplitL ""; [ done | ]). iExists _, _; by iFrame. *)
  (* Qed. *)
  Admitted.

  Lemma sim_instr_store_bij1 vt vs
    l_t l_s dt o i_t i_s `{non_void dt} L_t L_s C id_t id_s
    b v_t v_s val_t val_s:
    dtyp_WF dt ->
    dvalue_has_dtyp_fun v_t dt ->
    dvalue_has_dtyp_fun v_s dt ->
    C !! (l_t.1, l_s.1) = None ->
    ⊢ l_t ↔h l_s -∗
      checkout C -∗
      ldomain_tgt i_t L_t -∗
      ldomain_src i_s L_s -∗
      stack_tgt i_t -∗
      stack_src i_s -∗
      dval_rel v_t v_s -∗
      [ id_t := UVALUE_Addr l_t ]t i_t -∗
      [ id_s := UVALUE_Addr l_s ]s i_s -∗
      target_red (η := vir_handler)
        (exp_conv (denote_exp (Some dt) val_t))
        (lift_unary_post
           (fun x =>
              ⌜is_concrete x⌝ ∗ ⌜dvalue_to_uvalue v_t = x⌝ ∗
                ⌜dvalue_has_dtyp_fun v_t dt⌝)) -∗
      source_red (η := vir_handler)
        (exp_conv (denote_exp (Some dt) val_s))
        (lift_unary_post
           (fun x =>
              ⌜is_concrete x⌝ ∗ ⌜dvalue_to_uvalue v_s = x⌝ ∗
                ⌜dvalue_has_dtyp_fun v_s dt⌝)) -∗
      <{ %(IVoid vt) =
          (INSTR_Store b (dt, val_t)
                (DTYPE_Pointer, EXP_Ident (ID_Local id_t)) o) }> ⪯
      <{ %(IVoid vs) =
          (INSTR_Store b (dt, val_s)
                (DTYPE_Pointer, EXP_Ident (ID_Local id_s)) o) }>
      [{ (x_t, x_s),
          checkout C ∗
          ldomain_tgt i_t L_t ∗
          ldomain_src i_s L_s ∗
          stack_tgt i_t ∗
          stack_src i_s ∗
          [ id_t := UVALUE_Addr l_t ]t i_t ∗
          [ id_s := UVALUE_Addr l_s ]s i_s }].
  Proof.
  Admitted.
  (*   iIntros (WF Htyp_t Htyp_s H) *)
  (*     "#Hl HC Hd_t Hd_s Hf_t Hf_s #Hdv Hid_t Hid_s Hdt Hds". *)

  (*   setoid_rewrite interp_bind. *)
  (*   iApply sim_expr_bind; iApply exp_conv_to_instr. *)
  (*   iApply source_red_sim_expr. *)
  (*   iApply (source_red_mono with "[HC Hd_t Hd_s Hf_t Hf_s Hid_t Hid_s Hdt]"); *)
  (*     last iApply "Hds". *)
  (*   iIntros (?) "H". *)
  (*   iDestruct "H" as (????) "%Hv"; subst. *)
  (*   rewrite H0; clear H0. *)

  (*   iApply target_red_sim_expr. *)
  (*   iApply (target_red_mono with "[HC Hd_t Hd_s Hf_t Hf_s Hid_t Hid_s]"); *)
  (*           last iApply "Hdt". *)
  (*   iIntros (?) "H". *)
  (*   iDestruct "H" as (????) "%Hv'"; subst. *)
  (*   rewrite H0; clear H0. *)
  (*   iApply sim_expr_base. *)
  (*   rewrite !bind_ret_l. cbn. *)
  (*   rewrite /concretize_or_pick !is_concrete_dvalue_to_uvalue. *)
  (*   rewrite !uvalue_to_dvalue_of_dvalue_to_uvalue !interp_bind. *)
  (*   rewrite /lift_err !interp_ret !bind_ret_l. *)
  (*   destruct (dvalue_has_dtyp_fun v_t dt) eqn: Hv_t; try inversion Hv'. *)
  (*   destruct (dvalue_has_dtyp_fun v_s dt) eqn: Hv_s; try inversion Hv. *)
  (*   rewrite !interp_bind. *)

  (*   iApply sim_expr_bind; iApply exp_conv_to_instr. *)

  (*   iApply (sim_expr_bupd_mono with "[HC Hd_t Hd_s]"); *)
  (*     [ | iApply (sim_local_read_exp_conv with "Hf_t Hf_s Hid_t Hid_s")]. *)

  (*   cont. *)
  (*   iDestruct "H" as (??) "(Hf_t & Hf_s & Hid_t & Hid_s)"; subst. *)
  (*   cbn. rewrite !bind_ret_l. *)
  (*   destruct (dvalue_eq_dec *)
  (*               (d1:=DVALUE_Addr l_t) *)
  (*               (d2:=DVALUE_Poison)) eqn: Heq ; [ done | ]; clear Heq. *)
  (*   destruct (dvalue_eq_dec *)
  (*               (d1:=DVALUE_Addr l_s) *)
  (*               (d2:=DVALUE_Poison)) eqn: Heq ; [ done | ]; clear Heq. *)
  (*   rewrite !interp_vis; iApply sim_expr_bind. *)

  (*   iApply (sim_expr_bupd_mono with "[Hd_t Hd_s Hf_t Hf_s Hid_t Hid_s]"); *)
  (*     last iApply (bij_laws.sim_bij_store1 with "Hdv Hl HC"); *)
  (*     eauto. *)
  (*   2,3 : by eapply dvalue_has_dtyp_fun_sound. *)

  (*   cont. *)

  (*   rewrite !interp_ret; iApply sim_expr_tau. *)
  (*     iApply sim_expr_base; iFrame. *)

  (*   iExists _, _; iFrame; try done. *)
  (* Qed. *)

End more_properties.
