From iris.prelude Require Import options.

From velliris.base_logic Require Export gen_sim_prog.
From velliris.program_logic Require Import program_logic.
From velliris.vir Require Export
  vir vir_state spec util frame_laws primitive_laws tactics vir_util.

From ITree Require Import
  ITree Eq.Eqit Eq.EqAxiom Events.State Events.StateFacts.
From ITree Require Import Interp.InterpFacts Interp.TranslateFacts.

From Vellvm Require Import
  Syntax.LLVMAst
  Semantics.LLVMEvents
  Semantics.InterpretationStack
  Syntax.DynamicTypes
  Handlers.Handlers
  Handlers.MemoryTheory.

From Equations Require Import Equations.
Import DenoteTactics.

Set Default Proof Using "Type*".

Declare Custom Entry vir.

Notation "<{ e }>" :=
  (instr_conv (denote_instr e))
      (e custom vir at level 99).
Notation "x" := x (in custom vir at level 0, x constr at level 0).
Notation "% id '=' e" := (id, e)
    (in custom vir at level 50,
        format "% id  =  e").
Notation "'alloca' dt" :=
  (INSTR_Alloca dt _ _)
    (in custom vir at level 0, dt constr at level 0).
Notation "'load' dt , du * % ptr" :=
  (INSTR_Load _ dt (du,ptr) _)
    (in custom vir at level 0,
        dt constr at level 0,
        du constr at level 0,
        ptr constr at level 0,
    format "load  dt ,  du *  % ptr").
Notation "'store' dt val , du * % ptr" :=
  (INSTR_Store _ (dt, val) (du, ptr) _)
    (in custom vir at level 0,
        dt constr at level 0,
        val constr at level 0,
        du constr at level 0,
        ptr constr at level 0,
    format "store  dt  val ,  du *  % ptr").
Notation "<{{ e ( args ) }}> " :=
  (L0'expr_conv (denote_function e args))
      (e custom vir at level 99, args custom vir at level 99).

Notation "x1 :== x2   ;;; k " :=
  (ITree.bind (instr_conv (denote_instr (pair x1 x2))) (fun _ => (k)))
    (at level 30, x2 custom vir, k custom vir,
      right associativity).
Notation "'i32'" := (DynamicTypes.DTYPE_I 32) (at level 30).
Notation "' id '" := (EXP_Ident (ID_Local id)) (at level 30).
Notation "% id " := (IId (Raw id))  (at level 30).

(* Put here because of a universe inconsistency when introduced earlier
  in the compilation chain.. *)
Lemma denote_code_cons :
  forall i c,
    denote_code (i::c) ≅ ITree.bind (denote_instr i) (fun i => denote_code c).
Proof.
  intros.
  cbn.
  go.
  eapply eq_itree_clo_bind; first done; intros; subst.
  go.
  setoid_rewrite bind_ret_l.
  reflexivity.
Qed.

(* Change code context into instr-notation compatible proof environment *)
Ltac instr_conv_normalize :=
  repeat match goal with
    | |- context[instr_conv (ITree.bind (denote_instr ?x) _)] =>
        let Hx := fresh "Hx" in
          epose proof (instr_conv_bind (denote_instr x)) as Hx;
          setoid_rewrite Hx; clear Hx
  end.

Ltac to_instr :=
  repeat setoid_rewrite denote_code_cons;
  instr_conv_normalize;
  setoid_rewrite instr_conv_nil.

Ltac cont :=
  let Hret1 := fresh "Hret1" in
  let Hret2 := fresh "Hret2" in
  iIntros (??) "H";
  iDestruct "H" as (?? Hret1 Hret2) "H";
    rewrite Hret1 Hret2 !bind_ret_l; clear Hret1 Hret2.

Ltac unary_post :=
  rewrite /lift_unary_post; iExists _; iSplitL ""; first done.


Section instruction_laws.

  Context {Σ} `{!sheapGS Σ, !checkedoutGS Σ, !heapbijGS Σ}.

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

  Lemma target_instr_pure (x : LLVMAst.raw_id) (v : uvalue) o i L Ψ:
    x ∉ L ->
    ⊢ stack_tgt i -∗
      target_red (η := vir_handler) (exp_conv (denote_op o)) (lift_unary_post (fun x => ⌜x = v⌝)) -∗
      ldomain_tgt i L -∗
      ([ x := v ]t i -∗
        ldomain_tgt i ({[x]} ∪ L) -∗
        stack_tgt i -∗
        target_red (η := vir_handler) (Ret ()) Ψ) -∗
      target_red (η := vir_handler) (<{ %(IId x) = (INSTR_Op o) }>) Ψ.
  Proof.
    iIntros (H) "Hf Ht Hd H".
    cbn. rewrite /instr_conv.
    iApply target_red_eq_itree.
    { rewrite interp_bind. rewrite interp_translate.

      eapply eq_itree_clo_bind; first done.
      intros; subst. rewrite interp_vis. setoid_rewrite interp_ret at 1.
      rewrite /subevent /resum /ReSum_inr /cat /Cat_IFun /inr_ /Inr_sum1.
      simp instrE_conv.
      Unshelve.
      2 : exact
          (fun u2 => x0 <- trigger (LocalWrite x u2);; Tau (Ret x0)).
      reflexivity. }
    cbn.

    iApply target_red_bind.
    rewrite /exp_to_instr. simp instrE_conv.
    rewrite /exp_conv.
    assert (handler_eq:
      eq_Handler
        (λ T (e : exp_E T), Vis (instrE_conv T (inr1 (inr1 e))) (λ x0 : T, Ret x0))
        (λ T (e : exp_E T), Vis (exp_to_L0 e) Monad.ret)).
    { repeat intro. simp instrE_conv.
      rewrite /instr_to_L0 /exp_to_L0;
        destruct a; try destruct s; try reflexivity. }
    apply eq_itree_interp in handler_eq. do 2 red in handler_eq.
    specialize (handler_eq _ (denote_op o) _ (ltac:(reflexivity))).
    apply EqAxiom.bisimulation_is_eq in handler_eq;
      rewrite handler_eq; clear handler_eq.

    iApply (target_red_mono with "[Hf Hd H]"); [ | iApply "Ht"].
    rewrite /lift_unary_post.
    iIntros (??). destruct H0 as (?&?&?). subst.

    iApply target_red_eq_itree.
    { rewrite H0. rewrite !bind_ret_l. reflexivity. }
    clear H0.
    iApply target_red_bind.

    iApply (target_local_write_alloc with "Hd Hf"); try done.
    iIntros "Hi Hd Hs".
    iApply target_red_base.

    iApply target_red_eq_itree.
    { by rewrite bind_ret_l. }

    iApply target_red_tau. iApply ("H" with "Hi Hd Hs").
  Qed.

  Lemma source_instr_pure (x : LLVMAst.raw_id) (v : uvalue) o i L R1 Φ (e_t : _ R1):
    x ∉ L ->
    ⊢ stack_src i -∗
      source_red (η := vir_handler) (exp_conv (denote_op o)) (lift_unary_post (fun x => ⌜x = v⌝)) -∗
      ldomain_src i L -∗
      ([ x := v ]s i -∗
        ldomain_src i ({[x]} ∪ L) -∗
        stack_src i -∗
        source_red (η := vir_handler) (Ret ()) (fun e_s' => e_t ⪯ e_s' [{ Φ }])) -∗
      source_red (η := vir_handler) (<{ %(IId x) = (INSTR_Op o) }>) (fun e_s' => e_t ⪯ e_s' [{ Φ }]).
  Proof.
    iIntros (H) "Hf Ht Hd H".
    cbn. rewrite /instr_conv.
    iApply source_red_eq_itree.
    { rewrite interp_bind. rewrite interp_translate.

      eapply eq_itree_clo_bind; first done.
      intros; subst. rewrite interp_vis. setoid_rewrite interp_ret at 1.
      rewrite /subevent /resum /ReSum_inr /cat /Cat_IFun /inr_ /Inr_sum1.
      simp instrE_conv.
      Unshelve.
      2 : exact
          (fun u2 => x0 <- trigger (LocalWrite x u2);; Tau (Ret x0)).
      reflexivity. }
    cbn.

    iApply source_red_bind.
    rewrite /exp_to_instr. simp instrE_conv.
    rewrite /exp_conv.
    assert (handler_eq:
      eq_Handler
        (λ T (e : exp_E T), Vis (instrE_conv T (inr1 (inr1 e))) (λ x0 : T, Ret x0))
        (λ T (e : exp_E T), Vis (exp_to_L0 e) Monad.ret)).
    { repeat intro. simp instrE_conv.
      rewrite /instr_to_L0 /exp_to_L0;
        destruct a; try destruct s; try reflexivity. }
    apply eq_itree_interp in handler_eq. do 2 red in handler_eq.
    specialize (handler_eq _ (denote_op o) _ (ltac:(reflexivity))).
    apply EqAxiom.bisimulation_is_eq in handler_eq;
      rewrite handler_eq; clear handler_eq.

    iApply (source_red_mono with "[Hf Hd H]"); [ | iApply "Ht"].
    rewrite /lift_unary_post.
    iIntros (??). destruct H0 as (?&?&?). subst.

    iApply source_red_eq_itree.
    { rewrite H0. rewrite !bind_ret_l. reflexivity. }
    clear H0.
    iApply source_red_bind.

    iApply (source_local_write_alloc with "Hd Hf"); try done.
    iIntros "Hi Hd Hs".
    iApply source_red_base.

    iApply source_red_eq_itree.
    { by rewrite bind_ret_l. }

    iApply source_red_tau. iApply ("H" with "Hi Hd Hs").
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
  Proof.
    iIntros (Ht Hs) "Hf_t Hf_s Hp_t Hp_s H".
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

    iApply sim_expr_bupd_mono; last
    iApply (sim_local_write_alloc _ _ _ _ _ _ _ _ Ht Hs with
             "Hp_t Hp_s Hf_t Hf_s").

    iIntros (??) "H".

    iDestruct "H" as (????) "H".
    rewrite H1 H2 !bind_ret_l.
    iApply sim_expr_tau. iApply sim_expr_base.
    iExists _, _; do 2 (iSplitL ""; first done).
    done.
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
  Proof.
    iIntros (Hnt Hns) "Ha_t Ha_s Hd_t Hd_s Hf_t Hf_s".
    setoid_rewrite interp_bind.
    iApply sim_expr_bind.

    assert (Heq : forall dt,
        instr_conv (trigger (Alloca dt)) ≅
          x <- trigger (Alloca dt) ;; Tau (Ret x)).
    { intros. rewrite /instr_conv.
      rewrite interp_vis. setoid_rewrite interp_ret.

      rewrite /subevent /resum /ReSum_inr /cat /Cat_IFun /inr_ /Inr_sum1.
      simp instrE_conv. rewrite bind_trigger.
      reflexivity. }
    setoid_rewrite Heq.

    iApply sim_expr_bind.

    iApply (sim_expr_bupd_mono with "[Hd_t Hd_s] [Hf_t Hf_s Ha_t Ha_s]");
      [ | iApply (sim_alloca with "Ha_t Ha_s Hf_t Hf_s") ; eauto ].
    cbn. iIntros (??) "H".
    iDestruct "H" as (??????????)
      "(Ht & Hs & Ha_t & Ha_s & Hf_t & Hf_s & Hb_t & Hb_s)"; subst.
    rewrite H H0 !bind_ret_l; subst.
    iApply sim_expr_tau.
    iApply sim_expr_base.
    rewrite !bind_ret_l.

    setoid_rewrite instr_conv_localwrite. cbn.

    iApply sim_expr_vis.

    iApply (sim_expr_bupd_mono with
             "[Ht Hs Ha_t Ha_s Hb_t Hb_s] [Hf_t Hf_s Hd_t Hd_s]");
      [ | iApply (sim_local_write_alloc with "Hd_t Hd_s Hf_t Hf_s") ; eauto ].
    cbn.
    iIntros (??) "H".
    iDestruct "H" as (????) "(Hp_t & Hp_s & Hf_t & Hf_s)".
    rewrite H1 H2 !bind_ret_l.

    iApply sim_expr_tau; iApply sim_expr_base.
    iExists tt, tt; destruct v1, v2.
    do 2 (iSplitL ""; [ done |]).
    iExists l_t0, l_s0. base.
    by iFrame.
  Qed.

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
        target_red (η := vir_handler) (Ret ()) Ψ) -∗
      target_red (η := vir_handler)
        (<{ %(IId pid) = (INSTR_Load b dt (du, EXP_Ident (ID_Local id)) o) }>)
        Ψ.
  Proof.
    iIntros (WF Ht) "Hp Hl Hd Hf H".

    cbn. rewrite /instr_conv.
    iApply target_red_eq_itree.
    { rewrite interp_bind interp_translate; cbn.
      rewrite translate_vis interp_vis bind_bind.
      setoid_rewrite translate_ret.
      setoid_rewrite interp_ret.
      setoid_rewrite bind_tau.
      setoid_rewrite bind_ret_l.
      rewrite /LU_to_exp; cbn; rewrite /exp_to_instr.
      simp instrE_conv. reflexivity. }

    iApply target_red_bind.
    iApply (target_red_mono with "[Hp Hd H] [Hf Hl]");
      [ | iApply (target_local_read with "Hl Hf"); auto]; cycle 1.
    { iIntros "Hl Hf".
      iApply target_red_base.
      Unshelve.
      2 : exact (lift_unary_post (fun x => ⌜x = UVALUE_Addr (l, 0%Z)⌝
       ∗ stack_tgt i ∗ [id := UVALUE_Addr (l, 0%Z)]t i)%I).
      iExists _. do 2 (iSplitL ""; [ done | ]). iFrame. }

    iIntros (?) "HP".
    iDestruct "HP" as (???) "(Hf & Hl)".
    iApply target_red_eq_itree.
    { by rewrite H bind_ret_l. }

    iApply target_red_tau.

    rewrite H0; cbn.

    iApply target_red_eq_itree.
    { setoid_rewrite interp_bind.
      setoid_rewrite interp_ret.
      rewrite bind_ret_l. reflexivity. }

    destruct (dvalue_eq_dec (d1:=DVALUE_Addr (l, 0%Z)) (d2:=DVALUE_Poison)) eqn: Heq ; [ done | ].
    iApply target_red_eq_itree.
    { rewrite interp_bind.

      cbn.
      setoid_rewrite interp_vis.
      setoid_rewrite interp_ret.
      Unshelve.
      2 : exact (x <- trigger (Load dt (DVALUE_Addr (l, 0%Z))) ;;
                 x <- Tau (trigger (LocalWrite pid x)) ;; Tau (Ret x)).
      rewrite bind_bind.
      setoid_rewrite bind_tau.
      setoid_rewrite bind_ret_l.
      repeat setoid_rewrite bind_vis.
      repeat setoid_rewrite bind_ret_l.
      eapply eqit_Vis; intros.
      apply eqit_Tau.
      eapply eqit_Vis; intros. reflexivity. }

    iApply target_red_bind.

    change l with ((l, 0%Z).1) at 1.
    iApply (target_red_load1 with "Hp").

    iIntros "H'".
    iApply target_red_base.

    iApply target_red_eq_itree.
    { by rewrite bind_ret_l !bind_tau. }

    iApply target_red_tau; iApply target_red_bind.

    iApply (target_local_write_alloc _ _ _ _ _ Ht with "Hd Hf").
    iIntros "Hi H_t H_s".

    iApply target_red_base.

    iApply target_red_eq_itree.
    { by rewrite bind_ret_l. }

    iApply target_red_tau.

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
        target_red (η := vir_handler) (Ret ()) Ψ) -∗
      target_red (η := vir_handler)
        (<{ %(IId pid) = (INSTR_Load b dt (du, EXP_Ident (ID_Local id)) o) }>)
        Ψ.
  Proof.
    iIntros (WF Hdt Ht) "Hp Hl Hd Hf H".

    cbn. rewrite /instr_conv.
    iApply target_red_eq_itree.
    { rewrite interp_bind interp_translate; cbn.
      rewrite translate_vis interp_vis bind_bind.
      setoid_rewrite translate_ret.
      setoid_rewrite interp_ret.
      setoid_rewrite bind_tau.
      setoid_rewrite bind_ret_l.
      rewrite /LU_to_exp; cbn; rewrite /exp_to_instr.
      simp instrE_conv. reflexivity. }

    iApply target_red_bind.
    iApply (target_red_mono with "[Hp Hd H] [Hf Hl]");
      [ | iApply (target_local_read with "Hl Hf"); auto]; cycle 1.
    { iIntros "Hl Hf".
      iApply target_red_base.
      Unshelve.
      2 : exact (lift_unary_post (fun x => ⌜x = UVALUE_Addr (l, 0%Z)⌝
       ∗ stack_tgt i ∗ [id := UVALUE_Addr (l, 0%Z)]t i)%I).
      iExists _. do 2 (iSplitL ""; [ done | ]). iFrame. }

    iIntros (?) "HP".
    iDestruct "HP" as (???) "(Hf & Hl)".
    iApply target_red_eq_itree.
    { by rewrite H bind_ret_l. }

    iApply target_red_tau.

    rewrite H0; cbn.

    iApply target_red_eq_itree.
    { setoid_rewrite interp_bind.
      setoid_rewrite interp_ret.
      rewrite bind_ret_l. reflexivity. }

    destruct (dvalue_eq_dec (d1:=DVALUE_Addr (l, 0%Z)) (d2:=DVALUE_Poison)) eqn: Heq ; [ done | ].
    iApply target_red_eq_itree.
    { rewrite interp_bind.

      cbn.
      setoid_rewrite interp_vis.
      setoid_rewrite interp_ret.
      Unshelve.
      2 : exact (x <- trigger (Load dt (DVALUE_Addr (l, 0%Z))) ;;
                 x <- Tau (trigger (LocalWrite pid x)) ;; Tau (Ret x)).
      rewrite bind_bind.
      setoid_rewrite bind_tau.
      setoid_rewrite bind_ret_l.
      repeat setoid_rewrite bind_vis.
      repeat setoid_rewrite bind_ret_l.
      eapply eqit_Vis; intros.
      apply eqit_Tau.
      eapply eqit_Vis; intros. reflexivity. }

    iApply target_red_bind.
    iApply (target_red_mono with "[Hd Hf H Hl] [Hp]");
      [ | iApply (target_red_load _ _ _ _ _ WF Hdt with "Hp")]; cycle 1.

    Unshelve.
    3 : exact (lift_unary_post
          (fun x : uvalue => ⌜x = dvalue_to_uvalue v⌝ ∗ l ↦{q}t v)%I).
    { iIntros.
      iApply target_red_base.
      iExists _; eauto. }

    iIntros (?) "H'".
    iDestruct "H'" as (???) "H'"; subst.

    iApply target_red_eq_itree.
    { rewrite H1; by rewrite bind_ret_l !bind_tau. }

    iApply target_red_tau.
    iApply target_red_bind.

    iApply (target_red_mono with "[H Hl H'] [Hd Hf]");
      [ | iApply (target_local_write_alloc _ _ _ _ _ Ht with "Hd Hf")]; cycle 1.

    Unshelve.
    3 : exact (lift_unary_post
          (fun (_ : ()) => [ pid := dvalue_to_uvalue v ]t i ∗
            ldomain_tgt i ({[pid]} ∪ L) ∗ stack_tgt i))%I.
    { iIntros.
      iApply target_red_base; iExists _; by iFrame. }

    iIntros (?) "HP".
    iDestruct "HP" as (??)"(Hpl&Hd&Hf)".
    iSpecialize ("H" with "Hl Hpl H' Hd Hf").
    apply EqAxiom.bisimulation_is_eq in H0; rewrite H0.
    iApply target_red_eq_itree.
    { by rewrite bind_ret_l. }

    iApply target_red_tau. by destruct v0.
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
        source_red (η := vir_handler) (Ret ()) Ψ) -∗
      source_red (η := vir_handler)
        (<{ %(IId pid) = (INSTR_Load b dt (du, EXP_Ident (ID_Local id)) o) }>)
        Ψ.
  Proof.
    iIntros (WF Ht) "Hp Hl Hd Hf H".

    cbn. rewrite /instr_conv.
    iApply source_red_eq_itree.
    { rewrite interp_bind interp_translate; cbn.
      rewrite translate_vis interp_vis bind_bind.
      setoid_rewrite translate_ret.
      setoid_rewrite interp_ret.
      setoid_rewrite bind_tau.
      setoid_rewrite bind_ret_l.
      rewrite /LU_to_exp; cbn; rewrite /exp_to_instr.
      simp instrE_conv. reflexivity. }

    iApply source_red_bind.
    iApply (source_red_mono with "[Hp Hd H] [Hf Hl]");
      [ | iApply (source_local_read with "Hl Hf"); auto]; cycle 1.
    { iIntros "Hl Hf".
      iApply source_red_base.
      Unshelve.
      2 : exact (lift_unary_post (fun x => ⌜x = UVALUE_Addr (l, 0%Z)⌝
       ∗ stack_src i ∗ [id := UVALUE_Addr (l, 0%Z)]s i)%I).
      iExists _. do 2 (iSplitL ""; [ done | ]). iFrame. }

    iIntros (?) "HP".
    iDestruct "HP" as (???) "(Hf & Hl)".
    iApply source_red_eq_itree.
    { by rewrite H bind_ret_l. }

    iApply source_red_tau.

    rewrite H0; cbn.

    iApply source_red_eq_itree.
    { setoid_rewrite interp_bind.
      setoid_rewrite interp_ret.
      rewrite bind_ret_l. reflexivity. }

    destruct (dvalue_eq_dec (d1:=DVALUE_Addr (l, 0%Z)) (d2:=DVALUE_Poison)) eqn: Heq ; [ done | ].
    iApply source_red_eq_itree.
    { rewrite interp_bind.

      cbn.
      setoid_rewrite interp_vis.
      setoid_rewrite interp_ret.
      Unshelve.
      2 : exact (x <- trigger (Load dt (DVALUE_Addr (l, 0%Z))) ;;
                 x <- Tau (trigger (LocalWrite pid x)) ;; Tau (Ret x)).
      rewrite bind_bind.
      setoid_rewrite bind_tau.
      setoid_rewrite bind_ret_l.
      repeat setoid_rewrite bind_vis.
      repeat setoid_rewrite bind_ret_l.
      eapply eqit_Vis; intros.
      apply eqit_Tau.
      eapply eqit_Vis; intros. reflexivity. }

    iApply source_red_bind.

    change l with ((l, 0%Z).1) at 1.
    iApply (source_red_load1 with "Hp").

    iIntros "H'".
    iApply source_red_base.

    iApply source_red_eq_itree.
    { by rewrite bind_ret_l !bind_tau. }

    iApply source_red_tau; iApply source_red_bind.

    iApply (source_local_write_alloc _ _ _ _ _ Ht with "Hd Hf").
    iIntros "Hi H_t H_s".

    iApply source_red_base.

    iApply source_red_eq_itree.
    { by rewrite bind_ret_l. }

    iApply source_red_tau.

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
        source_red (η := vir_handler) (Ret ()) Ψ) -∗
      source_red (η := vir_handler)
        (<{ %(IId pid) = (INSTR_Load b dt (du, EXP_Ident (ID_Local id)) o) }>)
        Ψ.
  Proof.
    iIntros (WF Hdt Ht) "Hp Hl Hd Hf H".

    cbn. rewrite /instr_conv.
    iApply source_red_eq_itree.
    { rewrite interp_bind interp_translate; cbn.
      rewrite translate_vis interp_vis bind_bind.
      setoid_rewrite translate_ret.
      setoid_rewrite interp_ret.
      setoid_rewrite bind_tau.
      setoid_rewrite bind_ret_l.
      rewrite /LU_to_exp; cbn; rewrite /exp_to_instr.
      simp instrE_conv. reflexivity. }

    iApply source_red_bind.
    iApply (source_red_mono with "[Hp Hd H] [Hf Hl]");
      [ | iApply (source_local_read with "Hl Hf"); auto]; cycle 1.
    { iIntros "Hl Hf".
      iApply source_red_base.
      Unshelve.
      2 : exact (lift_unary_post (fun x => ⌜x = UVALUE_Addr (l, 0%Z)⌝
       ∗ stack_src i ∗ [id := UVALUE_Addr (l, 0%Z)]s i)%I).
      iExists _. do 2 (iSplitL ""; [ done | ]). iFrame. }

    iIntros (?) "HP".
    iDestruct "HP" as (???) "(Hf & Hl)".
    iApply source_red_eq_itree.
    { by rewrite H bind_ret_l. }

    iApply source_red_tau.
    rewrite H0; cbn.

    iApply source_red_eq_itree.
    { setoid_rewrite interp_bind.
      setoid_rewrite interp_ret.
      rewrite bind_ret_l. reflexivity. }

    destruct (dvalue_eq_dec (d1:=DVALUE_Addr (l, 0%Z)) (d2:=DVALUE_Poison)) eqn: Heq ; [ done | ].
    iApply source_red_eq_itree.
    { rewrite interp_bind.

      cbn.
      setoid_rewrite interp_vis.
      setoid_rewrite interp_ret.
      Unshelve.
      2 : exact (x <- trigger (Load dt (DVALUE_Addr (l, 0%Z))) ;;
                 x <- Tau (trigger (LocalWrite pid x)) ;; Tau (Ret x)).
      rewrite bind_bind.
      setoid_rewrite bind_tau.
      setoid_rewrite bind_ret_l.
      repeat setoid_rewrite bind_vis.
      repeat setoid_rewrite bind_ret_l.
      eapply eqit_Vis; intros.
      apply eqit_Tau.
      eapply eqit_Vis; intros. reflexivity. }

    iApply source_red_bind.
    iApply (source_red_mono with "[Hd Hf H Hl] [Hp]");
      [ | iApply (source_red_load _ _ _ _ _ WF Hdt with "Hp")]; cycle 1.

    Unshelve.
    3 : exact (lift_unary_post
          (fun x : uvalue => ⌜x = dvalue_to_uvalue v⌝ ∗ l ↦{q}s v)%I).
    { iIntros.
      iApply source_red_base.
      iExists _; eauto. }

    iIntros (?) "H'".
    iDestruct "H'" as (???) "H'"; subst.

    iApply source_red_eq_itree.
    { rewrite H1; by rewrite bind_ret_l !bind_tau. }

    iApply source_red_tau.
    iApply source_red_bind.

    iApply (source_red_mono with "[H Hl H'] [Hd Hf]");
      [ | iApply (source_local_write_alloc _ _ _ _ _ Ht with "Hd Hf")]; cycle 1.

    Unshelve.
    3 : exact (lift_unary_post
          (fun (_ : ()) => [ pid := dvalue_to_uvalue v ]s i ∗
            ldomain_src i ({[pid]} ∪ L) ∗ stack_src i))%I.
    { iIntros.
      iApply source_red_base; iExists _; by iFrame. }

    iIntros (?) "HP".
    iDestruct "HP" as (??)"(Hpl&Hd&Hf)".
    iSpecialize ("H" with "Hl Hpl H' Hd Hf").
    apply EqAxiom.bisimulation_is_eq in H0; rewrite H0.
    iApply source_red_eq_itree.
    { by rewrite bind_ret_l. }

    iApply source_red_tau. by destruct v0.
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
        target_red (η := vir_handler)
          (Ret ()) Ψ) -∗
      target_red (η := vir_handler)
        (<{ %(IVoid n) =
            (INSTR_Store b (dt, val) (DTYPE_Pointer, EXP_Ident (ID_Local id')) o) }>)
        Ψ.
  Proof.
    iIntros (Htyp) "Hp Hd Hf Hl H HP".

    cbn.
    rewrite /instr_conv.
    iApply target_red_eq_itree.
    { rewrite interp_bind.
      Unshelve.
      2 : exact
        (x <- exp_conv (denote_exp (Some dt) val) ;;
            instr_conv
              (dv <- concretize_or_pick x True;;
              (if dvalue_has_dtyp_fun dv dt
                then
                ua <- trigger (LocalRead id');;
                da <- pickUnique ua;;
                (if dvalue_eq_dec (d1:=da) (d2:=DVALUE_Poison)
                  then raiseUB "Store to poisoned address."
                  else trigger (Store da dv))
                else raise "Ill-typed store instruction"))).
      eapply eq_itree_clo_bind.
      { rewrite interp_translate. cbn.
        apply eq_itree_interp; first apply eq_handler_instrE_conv.
        done. }

      intros; subst.
      setoid_rewrite interp_bind.

      eapply eq_itree_clo_bind; first done.
      intros; subst.
      destruct (dvalue_has_dtyp_fun u0 dt) eqn: H; eauto; [ | done].

      setoid_rewrite <- translate_cmpE.
      setoid_rewrite translate_vis.
      setoid_rewrite interp_bind.
      eapply eq_itree_clo_bind.
      { do 2 rewrite interp_vis.
        tau_steps.
        apply eqit_Vis. intros.
        setoid_rewrite bind_ret_l.
        apply eqit_Tau.
        by rewrite translate_ret interp_ret. }
      intros; subst; done. }

    iApply target_red_bind.
    iApply (target_red_mono with "[Hp Hd Hf Hl HP]"); [ |  iApply "H"].

    iIntros (?) "H".
    iDestruct "H" as (????) "%Ht".

    iApply target_red_eq_itree.
    { rewrite H. rewrite /instr_conv.
      rewrite bind_ret_l interp_bind.
      rewrite /concretize_or_pick.
      destruct (is_concrete v0); inversion H0.
      cbn. rewrite -H1.
      rewrite uvalue_to_dvalue_of_dvalue_to_uvalue.
      rewrite /lift_err interp_ret bind_ret_l.
      destruct (dvalue_has_dtyp_fun dv dt); try inversion Ht.

      rewrite interp_bind.
      Unshelve.
      2 : exact
            (x <- trigger (LocalRead id');;
             Tau (
              instr_conv
                (da <- pickUnique x;;
                (if dvalue_eq_dec (d1:=da) (d2:=DVALUE_Poison)
                  then raiseUB "Store to poisoned address."
                  else trigger (Store da dv))))).
      cbn.
      rewrite interp_vis; setoid_rewrite interp_ret; cbn.
      setoid_rewrite bind_vis. setoid_rewrite bind_ret_l.
      cbn.
      rewrite bind_vis.
      apply eqit_Vis. intros.
      rewrite bind_tau.
      apply eqit_Tau; rewrite bind_ret_l. reflexivity. }

    iApply target_red_bind.
    iApply (target_red_mono with "[Hp Hd HP] [Hf Hl]");
      [ | iApply (target_local_read with "Hl Hf"); auto]; cycle 1.

    { iIntros "Hl Hf".
      iApply target_red_base.
      Unshelve.
      2 : exact (lift_unary_post (fun x => ⌜x = UVALUE_Addr (ptr, 0%Z)⌝
       ∗ stack_tgt i ∗ [id' := UVALUE_Addr (ptr, 0%Z)]t i)%I).
      iExists _. do 2 (iSplitL ""; [ done | ]). iFrame. }

    iIntros (?) "HΦ".
    iDestruct "HΦ" as (???) "(Hf & Hl)".


    destruct (dvalue_eq_dec (d1:=DVALUE_Addr (ptr, 0%Z)) (d2:=DVALUE_Poison)) eqn: Heq ; [ done | ].
    iApply target_red_eq_itree.
    { rewrite H2; subst. rewrite bind_ret_l; cbn.
      rewrite /instr_conv.
      setoid_rewrite bind_ret_l.
      rewrite Heq.
      rewrite interp_vis.
      setoid_rewrite interp_ret.
      apply eqit_Tau.
      setoid_rewrite bind_vis.
      setoid_rewrite bind_ret_l.
      Unshelve.
      2 : exact (x <- trigger (Store (DVALUE_Addr (ptr, 0%Z)) dv) ;;
                 Tau (Ret x))%I.
      tau_steps. setoid_rewrite bind_ret_l.
      reflexivity. }

    subst.
    iApply target_red_tau.
    iApply target_red_bind.

    destruct (dvalue_has_dtyp_fun v dt) eqn: Hdt; subst; try done.
    destruct (dvalue_has_dtyp_fun dv dt) eqn: Hdt'; subst; try done.
    apply dvalue_has_dtyp_fun_sound in Hdt, Hdt'.

    pose proof (dvalue_has_dtyp_serialize _ _ _ Hdt Hdt').
    iApply (target_red_store _ _ _ _ H1 with "Hp").
    iIntros "Hp".
    iApply target_red_base.
    iApply target_red_eq_itree.
    { by rewrite bind_ret_l. }

    iApply target_red_tau.

    iApply ("HP" with "Hd Hf Hl Hp").
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
        source_red (η := vir_handler)
          (Ret ()) Ψ) -∗
      source_red (η := vir_handler)
        (<{ %(IVoid n) =
            (INSTR_Store b (dt, val)
               (DTYPE_Pointer, EXP_Ident (ID_Local id')) o) }>)
        Ψ.
  Proof.

    iIntros (Htyp) "Hp Hd Hf Hl H HP".

    cbn.
    rewrite /instr_conv.
    iApply source_red_eq_itree.
    { rewrite interp_bind.
      Unshelve.
      2 : exact
        (x <- exp_conv (denote_exp (Some dt) val) ;;
            instr_conv
              (dv <- concretize_or_pick x True;;
              (if dvalue_has_dtyp_fun dv dt
                then
                ua <- trigger (LocalRead id');;
                da <- pickUnique ua;;
                (if dvalue_eq_dec (d1:=da) (d2:=DVALUE_Poison)
                  then raiseUB "Store to poisoned address."
                  else trigger (Store da dv))
                else raise "Ill-typed store instruction"))).
      eapply eq_itree_clo_bind.
      { rewrite interp_translate. cbn.
        apply eq_itree_interp; first apply eq_handler_instrE_conv.
        done. }

      intros; subst.
      setoid_rewrite interp_bind.

      eapply eq_itree_clo_bind; first done.
      intros; subst.
      destruct (dvalue_has_dtyp_fun u0 dt) eqn: H; eauto; [ | done].

      setoid_rewrite <- translate_cmpE.
      setoid_rewrite translate_vis.
      setoid_rewrite interp_bind.
      eapply eq_itree_clo_bind.
      { do 2 rewrite interp_vis.
        tau_steps.
        apply eqit_Vis. intros.
        setoid_rewrite bind_ret_l.
        apply eqit_Tau.
        by rewrite translate_ret interp_ret. }
      intros; subst; done. }

    iApply source_red_bind.
    iApply (source_red_mono with "[Hp Hd Hf Hl HP]"); [ |  iApply "H"].

    iIntros (?) "H".
    iDestruct "H" as (????) "%Ht".

    iApply source_red_eq_itree.
    { rewrite H. rewrite /instr_conv.
      rewrite bind_ret_l interp_bind.
      rewrite /concretize_or_pick.
      destruct (is_concrete v0); inversion H0.
      cbn. rewrite -H1.
      rewrite uvalue_to_dvalue_of_dvalue_to_uvalue.
      rewrite /lift_err interp_ret bind_ret_l.
      destruct (dvalue_has_dtyp_fun dv dt); try inversion Ht.

      rewrite interp_bind.
      Unshelve.
      2 : exact
            (x <- trigger (LocalRead id');;
             Tau (
              instr_conv
                (da <- pickUnique x;;
                (if dvalue_eq_dec (d1:=da) (d2:=DVALUE_Poison)
                  then raiseUB "Store to poisoned address."
                  else trigger (Store da dv))))).
      cbn.
      rewrite interp_vis; setoid_rewrite interp_ret; cbn.
      setoid_rewrite bind_vis. setoid_rewrite bind_ret_l.
      cbn.
      rewrite bind_vis.
      apply eqit_Vis. intros.
      rewrite bind_tau.
      apply eqit_Tau; rewrite bind_ret_l. reflexivity. }

    iApply source_red_bind.
    iApply (source_red_mono with "[Hp Hd HP] [Hf Hl]");
      [ | iApply (source_local_read with "Hl Hf"); auto]; cycle 1.

    { iIntros "Hl Hf".
      iApply source_red_base.
      Unshelve.
      2 : exact (lift_unary_post (fun x => ⌜x = UVALUE_Addr (ptr, 0%Z)⌝
       ∗ stack_src i ∗ [id' := UVALUE_Addr (ptr, 0%Z)]s i)%I).
      iExists _. do 2 (iSplitL ""; [ done | ]). iFrame. }

    iIntros (?) "HΦ".
    iDestruct "HΦ" as (???) "(Hf & Hl)".


    destruct (dvalue_eq_dec (d1:=DVALUE_Addr (ptr, 0%Z)) (d2:=DVALUE_Poison)) eqn: Heq ; [ done | ].
    iApply source_red_eq_itree.
    { rewrite H2; subst. rewrite bind_ret_l; cbn.
      rewrite /instr_conv.
      setoid_rewrite bind_ret_l.
      rewrite Heq.
      rewrite interp_vis.
      setoid_rewrite interp_ret.
      apply eqit_Tau.
      setoid_rewrite bind_vis.
      setoid_rewrite bind_ret_l.
      Unshelve.
      2 : exact (x <- trigger (Store (DVALUE_Addr (ptr, 0%Z)) dv) ;;
                 Tau (Ret x))%I.
      tau_steps. setoid_rewrite bind_ret_l.
      reflexivity. }

    subst.
    iApply source_red_tau.
    iApply source_red_bind.

    destruct (dvalue_has_dtyp_fun v dt) eqn: Hdt; subst; try done.
    destruct (dvalue_has_dtyp_fun dv dt) eqn: Hdt'; subst; try done.
    apply dvalue_has_dtyp_fun_sound in Hdt, Hdt'.

    pose proof (dvalue_has_dtyp_serialize _ _ _ Hdt Hdt').
    iApply (source_red_store _ _ _ _ H1 with "Hp").
    iIntros "Hp".
    iApply source_red_base.
    iApply source_red_eq_itree.
    { by rewrite bind_ret_l. }

    iApply source_red_tau.

    iApply ("HP" with "Hd Hf Hl Hp").
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
        source_red (η := vir_handler) (Ret ()) Ψ) -∗
      source_red (η := vir_handler)
        (<{ %(IVoid n) =
            (INSTR_Store b (dt, val)
               (DTYPE_Pointer, EXP_Ident (ID_Local id')) o) }>)
        Ψ.
  Proof.
    iIntros "Hp Hd Hf Hl H HP".

    cbn.
    rewrite /instr_conv.
    iApply source_red_eq_itree.
    { rewrite interp_bind.
      Unshelve.
      2 : exact
        (x <- exp_conv (denote_exp (Some dt) val) ;;
            instr_conv
              (dv <- concretize_or_pick x True;;
              (if dvalue_has_dtyp_fun dv dt
                then
                ua <- trigger (LocalRead id');;
                da <- pickUnique ua;;
                (if dvalue_eq_dec (d1:=da) (d2:=DVALUE_Poison)
                  then raiseUB "Store to poisoned address."
                  else trigger (Store da dv))
                else raise "Ill-typed store instruction"))).
      eapply eq_itree_clo_bind.
      { rewrite interp_translate. cbn.
        apply eq_itree_interp; first apply eq_handler_instrE_conv.
        done. }

      intros; subst.
      setoid_rewrite interp_bind.

      eapply eq_itree_clo_bind; first done.
      intros; subst.
      destruct (dvalue_has_dtyp_fun u0 dt) eqn: H; eauto; [ | done].
      setoid_rewrite <- translate_cmpE.
      setoid_rewrite translate_vis.
      setoid_rewrite interp_bind.
      rewrite !interp_vis !bind_bind.

      eapply eq_itree_clo_bind; first done.
      intros; subst.
      setoid_rewrite interp_bind.
      eapply eq_itree_clo_bind.
      { rewrite translate_ret !interp_ret.
        apply eqit_Tau.
        apply eqit_Ret. reflexivity. }
      intros; subst; done. }

    iApply source_red_bind.
    iApply (source_red_mono with "[Hp Hd Hf Hl HP]"); [ |  iApply "H"].

    iIntros (?) "H".
    iDestruct "H" as (????) "%Ht".

    iApply source_red_eq_itree.
    { rewrite H. rewrite /instr_conv.
      rewrite bind_ret_l interp_bind.
      rewrite /concretize_or_pick.
      destruct (is_concrete v); inversion H0.
      cbn. rewrite -H1.
      rewrite uvalue_to_dvalue_of_dvalue_to_uvalue.
      rewrite /lift_err interp_ret bind_ret_l.
      Unshelve.
      2 : exact
            (x <- trigger (LocalRead id');;
             Tau (
              instr_conv
                (da <- pickUnique x;;
                (if dvalue_eq_dec (d1:=da) (d2:=DVALUE_Poison)
                  then raiseUB "Store to poisoned address."
                  else trigger (Store da dv))))).
      cbn.
      destruct (dvalue_has_dtyp_fun dv dt) eqn : Htyp ; [ | done].
      rewrite interp_bind.
      rewrite interp_vis; setoid_rewrite interp_ret; cbn.
      setoid_rewrite bind_vis. setoid_rewrite bind_ret_l.
      cbn.
      rewrite bind_vis.
      apply eqit_Vis. intros.
      rewrite bind_tau.
      apply eqit_Tau; rewrite bind_ret_l. reflexivity. }

    iApply source_red_bind.
    iApply (source_red_mono with "[Hp Hd HP] [Hf Hl]");
      [ | iApply (source_local_read with "Hl Hf"); auto]; cycle 1.

    { iIntros "Hl Hf".
      iApply source_red_base.
      Unshelve.
      2 : exact (lift_unary_post (fun x => ⌜x = UVALUE_Addr (ptr, 0%Z)⌝
       ∗ stack_src i ∗ [id' := UVALUE_Addr (ptr, 0%Z)]s i)%I).
      iExists _. do 2 (iSplitL ""; [ done | ]). iFrame. }

    iIntros (?) "HΦ".
    iDestruct "HΦ" as (???) "(Hf & Hl)".

    destruct (dvalue_eq_dec (d1:=DVALUE_Addr (ptr, 0%Z)) (d2:=DVALUE_Poison)) eqn: Heq ; [ done | ].
    iApply source_red_eq_itree.
    { rewrite H2; subst. rewrite bind_ret_l; cbn.
      rewrite /instr_conv.
      setoid_rewrite bind_ret_l.
      rewrite Heq.
      rewrite interp_vis.
      setoid_rewrite interp_ret.
      apply eqit_Tau.
      setoid_rewrite bind_vis.
      setoid_rewrite bind_ret_l.
      Unshelve.
      2 : exact (x <- trigger (Store (DVALUE_Addr (ptr, 0%Z)) dv) ;;
                 Tau (Ret x))%I.
      tau_steps. setoid_rewrite bind_ret_l.
      reflexivity. }

    subst.
    iApply source_red_tau.
    iApply source_red_bind.

    change (ptr) with ((ptr, 0%Z).1) at 1.
    iApply (source_red_store1 with "Hp").
    iIntros "Hp".
    iApply source_red_base.
    iApply source_red_eq_itree.
    { by rewrite bind_ret_l. }

    iApply source_red_tau.

    cbn.
    by iSpecialize ("HP" with "Hd Hf Hl Hp").
  Qed.

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
        target_red (η := vir_handler) (Ret ()) Ψ) -∗
      target_red (η := vir_handler)
        (<{ %(IVoid n) =
            (INSTR_Store b (dt, val)
               (DTYPE_Pointer, EXP_Ident (ID_Local id')) o) }>)
        Ψ.
  Proof.
    iIntros "Hp Hd Hf Hl H HP".

    cbn.
    rewrite /instr_conv.
    iApply target_red_eq_itree.
    { rewrite interp_bind.
      Unshelve.
      2 : exact
        (x <- exp_conv (denote_exp (Some dt) val) ;;
            instr_conv
              (dv <- concretize_or_pick x True;;
              (if dvalue_has_dtyp_fun dv dt
                then
                ua <- trigger (LocalRead id');;
                da <- pickUnique ua;;
                (if dvalue_eq_dec (d1:=da) (d2:=DVALUE_Poison)
                  then raiseUB "Store to poisoned address."
                  else trigger (Store da dv))
                else raise "Ill-typed store instruction"))).
      eapply eq_itree_clo_bind.
      { rewrite interp_translate. cbn.
        apply eq_itree_interp; first apply eq_handler_instrE_conv.
        done. }

      intros; subst.
      setoid_rewrite interp_bind.

      eapply eq_itree_clo_bind; first done.
      intros; subst.
      destruct (dvalue_has_dtyp_fun u0 dt) eqn: H; eauto; [ | done].
      setoid_rewrite <- translate_cmpE.
      setoid_rewrite translate_vis.
      setoid_rewrite interp_bind.
      rewrite !interp_vis !bind_bind.

      eapply eq_itree_clo_bind; first done.
      intros; subst.
      setoid_rewrite interp_bind.
      eapply eq_itree_clo_bind.
      { rewrite translate_ret !interp_ret.
        apply eqit_Tau.
        apply eqit_Ret. reflexivity. }
      intros; subst; done. }

    iApply target_red_bind.
    iApply (target_red_mono with "[Hp Hd Hf Hl HP]"); [ |  iApply "H"].

    iIntros (?) "H".
    iDestruct "H" as (????) "%Ht".

    iApply target_red_eq_itree.
    { rewrite H. rewrite /instr_conv.
      rewrite bind_ret_l interp_bind.
      rewrite /concretize_or_pick.
      destruct (is_concrete v); inversion H0.
      cbn. rewrite -H1.
      rewrite uvalue_to_dvalue_of_dvalue_to_uvalue.
      rewrite /lift_err interp_ret bind_ret_l.
      Unshelve.
      2 : exact
            (x <- trigger (LocalRead id');;
             Tau (
              instr_conv
                (da <- pickUnique x;;
                (if dvalue_eq_dec (d1:=da) (d2:=DVALUE_Poison)
                  then raiseUB "Store to poisoned address."
                  else trigger (Store da dv))))).
      cbn.
      destruct (dvalue_has_dtyp_fun dv dt) eqn : Htyp ; [ | done].
      rewrite interp_bind.
      rewrite interp_vis; setoid_rewrite interp_ret; cbn.
      setoid_rewrite bind_vis. setoid_rewrite bind_ret_l.
      cbn.
      rewrite bind_vis.
      apply eqit_Vis. intros.
      rewrite bind_tau.
      apply eqit_Tau; rewrite bind_ret_l. reflexivity. }

    iApply target_red_bind.
    iApply (target_red_mono with "[Hp Hd HP] [Hf Hl]");
      [ | iApply (target_local_read with "Hl Hf"); auto]; cycle 1.

    { iIntros "Hl Hf".
      iApply target_red_base.
      Unshelve.
      2 : exact (lift_unary_post (fun x => ⌜x = UVALUE_Addr (ptr, 0%Z)⌝
       ∗ stack_tgt i ∗ [id' := UVALUE_Addr (ptr, 0%Z)]t i)%I).
      iExists _. do 2 (iSplitL ""; [ done | ]). iFrame. }

    iIntros (?) "HΦ".
    iDestruct "HΦ" as (???) "(Hf & Hl)".

    destruct (dvalue_eq_dec (d1:=DVALUE_Addr (ptr, 0%Z)) (d2:=DVALUE_Poison)) eqn: Heq ; [ done | ].
    iApply target_red_eq_itree.
    { rewrite H2; subst. rewrite bind_ret_l; cbn.
      rewrite /instr_conv.
      setoid_rewrite bind_ret_l.
      rewrite Heq.
      rewrite interp_vis.
      setoid_rewrite interp_ret.
      apply eqit_Tau.
      setoid_rewrite bind_vis.
      setoid_rewrite bind_ret_l.
      Unshelve.
      2 : exact (x <- trigger (Store (DVALUE_Addr (ptr, 0%Z)) dv) ;;
                 Tau (Ret x))%I.
      tau_steps. setoid_rewrite bind_ret_l.
      reflexivity. }

    subst.
    iApply target_red_tau.
    iApply target_red_bind.

    change (ptr) with ((ptr, 0%Z).1) at 1.
    iApply (target_red_store1 with "Hp").
    iIntros "Hp".
    iApply target_red_base.
    iApply target_red_eq_itree.
    { by rewrite bind_ret_l. }

    iApply target_red_tau.

    cbn.
    by iSpecialize ("HP" with "Hd Hf Hl Hp").
  Qed.

  From velliris.vir Require Import bij_laws.

End instruction_laws.


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
            Vis (call_conv T (instr_to_L0' e)) (λ x0 : T, Ret x0)).
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

  Context {Σ : gFunctors} `{!sheapGS Σ, !checkedoutGS Σ, !heapbijGS Σ}.

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

  Context {Σ : gFunctors} `{!sheapGS Σ, !checkedoutGS Σ, !heapbijGS Σ}.


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
    iIntros (Hnt Hns) "Ha_t Ha_s Hd_t Hd_s Hf_t Hf_s HC".
    setoid_rewrite interp_bind.
    iApply sim_expr_bind.

    assert (Heq : forall dt,
        instr_conv (trigger (Alloca dt)) ≅
          x <- trigger (Alloca dt) ;; Tau (Ret x)).
    { intros. rewrite /instr_conv.
      rewrite interp_vis. setoid_rewrite interp_ret.

      rewrite /subevent /resum /ReSum_inr /cat /Cat_IFun /inr_ /Inr_sum1.
      simp instrE_conv. rewrite bind_trigger.
      reflexivity. }
    setoid_rewrite Heq.

    iApply sim_expr_bind.

    iApply (sim_expr_bupd_mono with
             "[HC Hd_t Hd_s] [Hf_t Hf_s Ha_t Ha_s]");
      [ | iApply (sim_alloca with "Ha_t Ha_s Hf_t Hf_s") ; eauto ].
    cbn. iIntros (??) "H".
    iDestruct "H" as (??????????)
      "(Ht & Hs & Ha_t & Ha_s & Hf_t & Hf_s & Hb_t & Hb_s)"; subst.

    rewrite H H0 !bind_ret_l; subst.
    iApply sim_expr_tau.
    iApply sim_expr_base.
    rewrite !bind_ret_l.

    iApply sim_update_si.
    iModIntro; iIntros (??) "SI".
    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & %WF_SI & SI)".

    iAssert ((¬ ⌜set_Exists (λ '(b_t', b_s'), l_t0 = b_t') S⌝)%I) as "%Hext_t".
    { iIntros (([b_t' b_s'] & Hin & <-)).
      iDestruct "Hbij" as "(Hbij & Hheap)".
      iPoseProof (big_sepS_elem_of with "Hheap") as "Hr"; first by apply Hin.
      iDestruct "Hr" as (? v_t' v_s') "(Hr_t & Ha_t' & Ha_s')".
      by iApply (heap_block_size_excl with "Hb_t Ha_t'"). }

    iPoseProof (lb_rel_empty_blocks dt) as "Hrel".

    destruct_HC "Hh_s".
    iDestruct (ghost_var_agree with "Hf_s HCF") as %Hd_s; subst.
    iDestruct (ghost_var_agree with "HC H_c") as %Hc_s; subst.
    rewrite allocaS_eq.
    iDestruct (ghost_var_agree with "Ha_s HA") as %Hd_s; subst.

    iDestruct "Hh_t" as (cft hFt)
        "(Hσ_t&HB_t&HCF_t&HA_t&HL_t&HD_t&HSA_t&HG_t&%Hdup_t&%Hbs_t&%Hwf_t)".
    iDestruct (ghost_var_agree with "Hf_t HCF_t") as %Hd_t; subst.
    iDestruct (ghost_var_agree with "Ha_t HA_t") as %Hd_t; subst.
    iFrame.

    iSplitR "Hd_t Hd_s HC Ha_t Ha_s Ht Hs Hb_t Hb_s Hf_t Hf_s".
    { iExists _, S, G; iFrame.
      iSplitR "HB_t HCF_t HA_t HL_t HD_t HSA_t".
      { iModIntro; iExists _, _; iFrame. done. }
      iSplitR "".
      { iModIntro; iExists _, _; iFrame. done. }
      iModIntro. iPureIntro. set_solver. }

    setoid_rewrite instr_conv_localwrite. cbn.

    iApply sim_expr_vis.

    iApply (sim_expr_bupd_mono with
             "[HC Ht Hs Ha_t Ha_s Hb_t Hb_s] [Hf_t Hf_s Hd_t Hd_s]");
      [ | iApply (sim_local_write_alloc with "Hd_t Hd_s Hf_t Hf_s") ; eauto ].
    cbn.
    iIntros (??) "H".
    iDestruct "H" as (????) "(Hp_t & Hp_s & Hf_t & Hf_s)".
    rewrite H1 H2 !bind_ret_l.

    iApply sim_expr_tau; iApply sim_expr_base.
    iExists tt, tt; destruct v1, v2.
    do 2 (iSplitL ""; [ done |]).
    iExists l_t0, l_s0. base. iFrame.
    iDestruct "Hf_s" as "(?&?&?)"; iFrame.
    iPureIntro. clear -WF_SI Hext_t.
    apply not_elem_of_dom_1.
    set_solver.
  Qed.

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
    iIntros (Ht) "#Hbij HC Hl Hd Hf H".

    cbn. rewrite !instr_conv_bind bind_bind.
    rewrite !translate_vis. setoid_rewrite interp_vis.
    rewrite bind_bind. do 2 setoid_rewrite translate_ret.
    setoid_rewrite interp_ret. setoid_rewrite bind_tau.
    setoid_rewrite bind_ret_l.
    iApply source_red_sim_expr; iApply source_red_bind.

    iApply (source_red_mono with "[]");
      [ | iApply (source_local_read with "Hl Hf"); auto];
      first (iIntros (?) "H"; done).

    iIntros "Hl Hst".
    do 2 iApply source_red_base.
    rewrite bind_ret_l.
    iApply sim_expr_tauL.
    setoid_rewrite instr_conv_bind. cbn.
    setoid_rewrite instr_conv_ret.
    rewrite bind_ret_l.

    destruct (dvalue_eq_dec (d1:=DVALUE_Addr l) (d2:=DVALUE_Poison))
      eqn: Heq ; [ done | ].

    setoid_rewrite instr_conv_bind.
    rewrite bind_bind; setoid_rewrite interp_vis.
    rewrite bind_bind.
    rewrite sim_expr_eq.

    iIntros (??) "SI".
    rewrite interp_L2_bind.
    rewrite {2}/interp_L2. rewrite StateFacts.interp_state_vis.
    rewrite /subevent; unfold_cat. simp instrE_conv.
    rewrite /instr_to_L0 bind_tau; cbn.

    destruct σ_s as ((?&?)&(?&?)&?) eqn: Hs; cbn.

    destruct (read (g0, g1, f) l dt) eqn : Hread.
    (* UB case *)
    { rewrite bind_tau. iApply sim_coind_tauR.
      rewrite !bind_bind bind_vis.
      iApply sim_coind_ub. }
    rewrite !bind_bind !bind_ret_l.
    setoid_rewrite StateFacts.interp_state_ret.
    rewrite !bind_tau. rewrite bind_ret_l.

    cbn. rewrite interp_ret bind_tau bind_ret_l.
    rewrite !bind_bind. rewrite interp_L2_tau.
    repeat iApply sim_coind_tauR.
    rewrite bind_vis.

    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij' & SI)".

    unfold interp_L2. rewrite StateFacts.interp_state_vis.
    simp instrE_conv. rewrite /instr_to_L0 bind_tau; cbn; rewrite bind_bind.
    iApply sim_coind_tauR.
    rewrite /handle_local_stack; cbn. destruct p.
    rewrite /ITree.map !bind_bind !bind_ret_l.
    iApply sim_coind_tauR; rewrite bind_tau interp_ret bind_ret_l.
    rewrite StateFacts.interp_state_tau; iApply sim_coind_tauR.

    iSpecialize ("H" with "Hl").

    iMod ((lheap_domain_alloc _ _ u)
           with "Hd Hst Hh_s") as "(Hh_s & Hp_s & Hf_s & Hd_s)"; [done | ].

    iDestruct (lheap_lookup with "Hh_s Hf_s Hp_s") as %Hl_s; cbn.

    iSpecialize ("H" with "Hp_s HC Hd_s Hf_s").
    iApply "H".
    iExists C0, S, G; iFrame.
  Qed.

End exp_laws.


Section more_properties.

  Context {Σ : gFunctors} `{!sheapGS Σ, !checkedoutGS Σ, !heapbijGS Σ}.


   Lemma target_instr_load_in l dt du b o L i pid id q Ψ u v:
    is_supported dt ->
    dvalue_has_dtyp v dt ->
    ⊢ l ↦{q}t v -∗
      [ id := UVALUE_Addr (l, 0%Z) ]t i -∗
      [ pid := u ]t i -∗
      ldomain_tgt i L -∗
      stack_tgt i -∗
      ([ id := UVALUE_Addr (l, 0%Z) ]t i -∗
        [ pid := dvalue_to_uvalue v]t i -∗
        l ↦{q}t v -∗
        ldomain_tgt i L -∗
        stack_tgt i -∗
        target_red (η := vir_handler) (Ret ()) Ψ) -∗
      target_red (η := vir_handler)
        (<{ %(IId pid) = (INSTR_Load b dt (du, EXP_Ident (ID_Local id)) o) }>)
        Ψ.
  Proof.
    iIntros (WF Hτ) "Hp Hl Hid Hd Hf H".

    cbn. rewrite /instr_conv.
    iApply target_red_eq_itree.
    { rewrite interp_bind interp_translate; cbn.
      rewrite translate_vis interp_vis bind_bind.
      setoid_rewrite translate_ret.
      setoid_rewrite interp_ret.
      setoid_rewrite bind_tau.
      setoid_rewrite bind_ret_l.
      rewrite /LU_to_exp; cbn; rewrite /exp_to_instr.
      simp instrE_conv. reflexivity. }

    iApply target_red_bind.
    iApply (target_red_mono with "[Hp Hid Hd H] [Hf Hl]");
      [ | iApply (target_local_read with "Hl Hf"); auto]; cycle 1.
    { iIntros "Hl Hf".
      iApply target_red_base.
      Unshelve.
      2 : exact (lift_unary_post (fun x => ⌜x = UVALUE_Addr (l, 0%Z)⌝
       ∗ stack_tgt i ∗ [id := UVALUE_Addr (l, 0%Z)]t i)%I).
      iExists _. do 2 (iSplitL ""; [ done | ]). iFrame. }

    iIntros (?) "HP".
    iDestruct "HP" as (???) "(Hf & Hl)".
    iApply target_red_eq_itree.
    { by rewrite H bind_ret_l. }

    iApply target_red_tau.

    rewrite H0; cbn.

    iApply target_red_eq_itree.
    { setoid_rewrite interp_bind.
      setoid_rewrite interp_ret.
      rewrite bind_ret_l. reflexivity. }

    destruct (dvalue_eq_dec (d1:=DVALUE_Addr (l, 0%Z)) (d2:=DVALUE_Poison)) eqn: Heq ; [ done | ].
    iApply target_red_eq_itree.
    { rewrite interp_bind.

      cbn.
      setoid_rewrite interp_vis.
      setoid_rewrite interp_ret.
      Unshelve.
      2 : exact (x <- trigger (Load dt (DVALUE_Addr (l, 0%Z))) ;;
                 x <- Tau (trigger (LocalWrite pid x)) ;; Tau (Ret x)).
      rewrite bind_bind.
      setoid_rewrite bind_tau.
      setoid_rewrite bind_ret_l.
      repeat setoid_rewrite bind_vis.
      repeat setoid_rewrite bind_ret_l.
      eapply eqit_Vis; intros.
      apply eqit_Tau.
      eapply eqit_Vis; intros. reflexivity. }

    iApply target_red_bind.

    change l with ((l, 0%Z).1) at 1.
    iApply (target_red_load with "Hp"); auto.

    iIntros "H'".
    iApply target_red_base.

    iApply target_red_eq_itree.
    { by rewrite bind_ret_l !bind_tau. }

    iApply target_red_tau; iApply target_red_bind.

    iApply (target_local_write with "Hid Hd Hf").
    iIntros "Hi H_t H_s".

    iApply target_red_base.

    iApply target_red_eq_itree.
    { by rewrite bind_ret_l. }

    iApply target_red_tau.

    cbn.
    by iSpecialize ("H" with "Hl Hi H' H_t H_s").
  Qed.

   Lemma source_instr_load_in l dt du b o L i pid id q Ψ u v:
    is_supported dt ->
    dvalue_has_dtyp v dt  ->
    ⊢ l ↦{q}s v -∗
      [ id := UVALUE_Addr (l, 0%Z) ]s i -∗
      [ pid := u ]s i -∗
      ldomain_src i L -∗
      stack_src i -∗
      ([ id := UVALUE_Addr (l, 0%Z) ]s i -∗
        [ pid := dvalue_to_uvalue v ]s i -∗
        l ↦{q}s v -∗
        ldomain_src i L -∗
        stack_src i -∗
        source_red (η := vir_handler) (Ret ()) Ψ) -∗
      source_red (η := vir_handler)
        (<{ %(IId pid) = (INSTR_Load b dt (du, EXP_Ident (ID_Local id)) o) }>)
        Ψ.
  Proof.
    iIntros (WF Hdt) "Hp Hl Hid Hd Hf H".

    cbn. rewrite /instr_conv.
    iApply source_red_eq_itree.
    { rewrite interp_bind interp_translate; cbn.
      rewrite translate_vis interp_vis bind_bind.
      setoid_rewrite translate_ret.
      setoid_rewrite interp_ret.
      setoid_rewrite bind_tau.
      setoid_rewrite bind_ret_l.
      rewrite /LU_to_exp; cbn; rewrite /exp_to_instr.
      simp instrE_conv. reflexivity. }

    iApply source_red_bind.
    iApply (source_red_mono with "[Hp Hid Hd H] [Hf Hl]");
      [ | iApply (source_local_read with "Hl Hf"); auto]; cycle 1.
    { iIntros "Hl Hf".
      iApply source_red_base.
      Unshelve.
      2 : exact (lift_unary_post (fun x => ⌜x = UVALUE_Addr (l, 0%Z)⌝
       ∗ stack_src i ∗ [id := UVALUE_Addr (l, 0%Z)]s i)%I).
      iExists _. do 2 (iSplitL ""; [ done | ]). iFrame. }

    iIntros (?) "HP".
    iDestruct "HP" as (???) "(Hf & Hl)".
    iApply source_red_eq_itree.
    { by rewrite H bind_ret_l. }

    iApply source_red_tau.

    rewrite H0; cbn.

    iApply source_red_eq_itree.
    { setoid_rewrite interp_bind.
      setoid_rewrite interp_ret.
      rewrite bind_ret_l. reflexivity. }

    destruct (dvalue_eq_dec (d1:=DVALUE_Addr (l, 0%Z)) (d2:=DVALUE_Poison)) eqn: Heq ; [ done | ].
    iApply source_red_eq_itree.
    { rewrite interp_bind.

      cbn.
      setoid_rewrite interp_vis.
      setoid_rewrite interp_ret.
      Unshelve.
      2 : exact (x <- trigger (Load dt (DVALUE_Addr (l, 0%Z))) ;;
                 x <- Tau (trigger (LocalWrite pid x)) ;; Tau (Ret x)).
      rewrite bind_bind.
      setoid_rewrite bind_tau.
      setoid_rewrite bind_ret_l.
      repeat setoid_rewrite bind_vis.
      repeat setoid_rewrite bind_ret_l.
      eapply eqit_Vis; intros.
      apply eqit_Tau.
      eapply eqit_Vis; intros. reflexivity. }

    iApply source_red_bind.

    change l with ((l, 0%Z).1) at 1.
    iApply (source_red_load with "Hp"); auto.

    iIntros "H'".
    iApply source_red_base.

    iApply source_red_eq_itree.
    { by rewrite bind_ret_l !bind_tau. }

    iApply source_red_tau; iApply source_red_bind.

    iApply (source_local_write with "Hid Hd Hf").
    iIntros "Hi H_t H_s".

    iApply source_red_base.

    iApply source_red_eq_itree.
    { by rewrite bind_ret_l. }

    iApply source_red_tau.

    cbn.
    by iSpecialize ("H" with "Hl Hi H' H_t H_s").
  Qed.

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
    iApply sim_expr_bind; iApply exp_conv_to_instr.

    iApply (sim_expr_bupd_mono with "[HC Hd_t Hd_s]");
      [ | iApply (sim_local_read_exp_conv with "Hf_t Hf_s Hid_t Hid_s")].

    cont.
    iDestruct "H" as (??) "(Hf_t & Hf_s & Hid_t & Hid_s)"; subst.
    cbn. rewrite !bind_ret_l.
    destruct (dvalue_eq_dec
                (d1:=DVALUE_Addr l_t)
                (d2:=DVALUE_Poison)) eqn: Heq ; [ done | ]; clear Heq.
    destruct (dvalue_eq_dec
                (d1:=DVALUE_Addr l_s)
                (d2:=DVALUE_Poison)) eqn: Heq ; [ done | ]; clear Heq.
    rewrite !interp_bind !interp_vis !bind_bind; iApply sim_expr_bind.

    iApply (sim_expr_bupd_mono with "[Hd_t Hd_s Hf_t Hf_s Hid_t Hid_s]");
      last iApply (bij_laws.sim_bij_load_Some with "Hl HC"); eauto.

    cont.

    rewrite !bind_tau !interp_ret !bind_ret_l.
    iApply sim_expr_tau.
    setoid_rewrite instr_conv_localwrite.

    iApply sim_expr_vis.

    iApply (sim_expr_bupd_mono with "[Hid_t Hid_s H]"); last
      iApply (sim_local_write_alloc _ _ _ _ _ _ _ _ Ht Hs with
              "Hd_t Hd_s Hf_t Hf_s").
    iDestruct "H" as "(#Hv & HC)".

    cont.
    iApply sim_expr_tau; iApply sim_expr_base; iFrame.
    iDestruct "H" as "(Hid_t & Hid_s & Hd_t & Hd_s & Hs_t & Hs_s)".
    iExists _, _; iFrame; try done.
    do 2 (iSplitL ""; [ done | ]). iExists _, _; by iFrame.
  Qed.

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
    iIntros (WF Htyp_t Htyp_s H)
      "#Hl HC Hd_t Hd_s Hf_t Hf_s #Hdv Hid_t Hid_s Hdt Hds".

    setoid_rewrite interp_bind.
    iApply sim_expr_bind; iApply exp_conv_to_instr.
    iApply source_red_sim_expr.
    iApply (source_red_mono with "[HC Hd_t Hd_s Hf_t Hf_s Hid_t Hid_s Hdt]");
      last iApply "Hds".
    iIntros (?) "H".
    iDestruct "H" as (????) "%Hv"; subst.
    rewrite H0; clear H0.

    iApply target_red_sim_expr.
    iApply (target_red_mono with "[HC Hd_t Hd_s Hf_t Hf_s Hid_t Hid_s]");
            last iApply "Hdt".
    iIntros (?) "H".
    iDestruct "H" as (????) "%Hv'"; subst.
    rewrite H0; clear H0.
    iApply sim_expr_base.
    rewrite !bind_ret_l. cbn.
    rewrite /concretize_or_pick !is_concrete_dvalue_to_uvalue.
    rewrite !uvalue_to_dvalue_of_dvalue_to_uvalue !interp_bind.
    rewrite /lift_err !interp_ret !bind_ret_l.
    destruct (dvalue_has_dtyp_fun v_t dt) eqn: Hv_t; try inversion Hv'.
    destruct (dvalue_has_dtyp_fun v_s dt) eqn: Hv_s; try inversion Hv.
    rewrite !interp_bind.

    iApply sim_expr_bind; iApply exp_conv_to_instr.

    iApply (sim_expr_bupd_mono with "[HC Hd_t Hd_s]");
      [ | iApply (sim_local_read_exp_conv with "Hf_t Hf_s Hid_t Hid_s")].

    cont.
    iDestruct "H" as (??) "(Hf_t & Hf_s & Hid_t & Hid_s)"; subst.
    cbn. rewrite !bind_ret_l.
    destruct (dvalue_eq_dec
                (d1:=DVALUE_Addr l_t)
                (d2:=DVALUE_Poison)) eqn: Heq ; [ done | ]; clear Heq.
    destruct (dvalue_eq_dec
                (d1:=DVALUE_Addr l_s)
                (d2:=DVALUE_Poison)) eqn: Heq ; [ done | ]; clear Heq.
    rewrite !interp_vis; iApply sim_expr_bind.

    iApply (sim_expr_bupd_mono with "[Hd_t Hd_s Hf_t Hf_s Hid_t Hid_s]");
      last iApply (bij_laws.sim_bij_store1 with "Hdv Hl HC");
      eauto.
    2,3 : by eapply dvalue_has_dtyp_fun_sound.

    cont.

    rewrite !interp_ret; iApply sim_expr_tau.
      iApply sim_expr_base; iFrame.

    iExists _, _; iFrame; try done.
  Qed.

End more_properties.
