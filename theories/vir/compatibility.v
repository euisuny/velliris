From iris.prelude Require Import options.

From Equations Require Import Equations.

From Vellvm Require Import Syntax.ScopeTheory.

From velliris.program_logic Require Import program_logic.
From velliris.vir Require Import
  vir spec
  logical_relations
  tactics
  vir_sim_properties
.

Set Default Proof Using "Type*".

Import ListNotations.

(* ------------------------------------------------------------------------ *)

(** *Compatibility lemmas *)
Section compatibility.

  Context {Σ : gFunctors} `{!vellirisGS Σ}.

  (* Invariants *)
  Context
    (I : local_env -> local_env -> iProp Σ).

(** *Compatibility lemmas *)

  (* LATER: See if the [id] generalization is also possible *)
  Theorem phi_compat bid bid' id ϕ ϕ' C A_t A_s:
    (let '(Phi dt  args )  := ϕ in
     let '(Phi dt' args')  := ϕ' in
     match Util.assoc bid args, Util.assoc bid' args' with
     | Some op, Some op' =>
         expr_logrel I C
           (denote_exp (Some dt) op)
           (denote_exp (Some dt') op')
           A_t A_s
     | None, None => True
     | _ , _ => False
     end) -∗
    phi_logrel I
       (denote_phi bid (id, ϕ))
       (denote_phi bid' (id, ϕ')) C A_t A_s.
  Proof with vsimp.
    iIntros "He" (????) "H".
    iDestruct "H" as (Harg Hnd_t Hnd_s)
      "(Hdt&Hds&Hat&Has&Hv&Hs_t&Hs_s&#HWF&HC&Ha_t&Ha_s & #Hl)";
      destruct ϕ, ϕ'; cbn.
    rename t0 into t', args0 into args'.
    rewrite /denote_phi.

    destruct (Util.assoc bid' args') eqn: H;
      [ | iApply exp_conv_raise].
    destruct (Util.assoc bid args) eqn: H'; last done.

    vsimp. Cut...
    mono: iApply "He"...
    { iDestruct "HΦ" as "(Hv & CI)"...

    iApply sim_update_si; rewrite /update_si.

    iIntros (??) "SI".
    iDestruct "CI" as (??)
      "(Hd_t & Hd_s & Hs_t & Hs_s & HA & %Hc & Ha_t & Ha_s)".

    iFrame. vfinal.
    repeat iExists _; by iFrame. }

    iExists _, _; iFrame; by iFrame "HWF Hl".
  Qed.

  Lemma phi_list_compat bid (Φ Φ' : list (local_id * phi dtyp)) C i_t i_s A_t A_s:
    ([∗ list] ϕ;ϕ' ∈ Φ; Φ',
        phi_logrel I (denote_phi bid ϕ) (denote_phi bid ϕ') C A_t A_s) -∗
    code_inv I C i_t i_s A_t A_s -∗
    instr_conv (map_monad (λ x, translate exp_to_instr (denote_phi bid x)) Φ) ⪯
      instr_conv (map_monad (λ x, translate exp_to_instr (denote_phi bid x)) Φ')
    [{ (r_t, r_s),
        ([∗ list] v_t; v_s ∈ r_t; r_s,
           ⌜v_t.1 = v_s.1⌝ ∗ uval_rel v_t.2 v_s.2)
            ∗ code_inv I C i_t i_s A_t A_s }].
  Proof with vsimp.
    iIntros "HΦ CI".

    iInduction Φ as [] "IH" forall (Φ').
    { cbn.
      iPoseProof (big_sepL2_nil_inv_l with "HΦ") as "%Heq"; subst; cbn...
      vfinal. }

    destruct a as (?&[]).
    iPoseProof (big_sepL2_cons_inv_l with "HΦ") as (???) "(He & HΦ)"; subst.
    destruct x2 as (l' & []).
    rename t0 into t', args0 into args', l2' into Φ'.
    iSpecialize ("IH" with "HΦ").
    cbn -[denote_phi]...

    iDestruct "CI" as (??)
        "(Hd_t & Hd_s & Hat & Has & #HWF &
        %Hargs & Hs_t & Hs_s & Hv & HC & Ha_t & Ha_s & %Hnd_t & %Hnd_s & #Hl)".

    Cut...
    iApply (sim_expr_bupd_mono with "[IH]"); [ | iApply "He"];
      try iFrame; eauto; cycle 1.

    cbn. iIntros (??) "H".
    iDestruct "H" as (?????) "(#H & CI)".
    rewrite H H0...

    iSpecialize ("IH" with "CI"). subst.
    Cut... mono: (iApply "IH")...
    iDestruct "HΦ" as "(H' & CI)".
    vfinal; cbn; vsimp; by iFrame "H".
  Qed.

  Theorem phis_compat C bid (Φ Φ' : list (local_id * phi dtyp)) A_t A_s:
    ([∗ list] ϕ;ϕ' ∈ Φ; Φ',
        phi_logrel I (denote_phi bid ϕ) (denote_phi bid ϕ') C A_t A_s) -∗
    phis_logrel I (denote_phis bid Φ) (denote_phis bid Φ') C A_t A_s.
  Proof with vsimp.
    iIntros "HΦ" (??) "CI".
    iPoseProof (phi_list_compat with "HΦ CI") as "H".
    rewrite /denote_phis... Cut...
    mono: iApply "H"...
    iDestruct "HΦ" as "(H & CI)".

    setoid_rewrite instr_conv_ret.

    iInduction r_s as [] "IH" forall (r_t).
    { iDestruct (big_sepL2_nil_inv_r with "H") as %Hx; subst; cbn...
      Cut... do 2 vfinal. }

    iDestruct (big_sepL2_cons_inv_r with "H") as (???) "(CI1 & CI2)";
    destruct a, x1; subst; cbn...
    Cut...

    iDestruct "CI1" as "(%Hl & Hv)"; subst.

    Cut...
    mono: (iApply (local_write_refl with "CI Hv")) with "[CI2]"...

    final.
    iSpecialize ("IH" with "CI2 HΦ")...
    iPoseProof (sim_expr_fmap_inv with "IH") as "Hf".
    Cut.

    mono: iApply "Hf"...

    iDestruct "HΦ" as (????) "H".
    apply eqitree_inv_Ret in H, H0; subst.
    do 2 vfinal.
  Qed.

  Theorem code_compat (c c' : code dtyp) A_t A_s:
    code_WF c ->
    code_WF c' ->
    ([∗ list] '(id, i); '(id', i') ∈ c; c',
        ∀ A_t A_s, instr_logrel id i id' i' ∅ A_t A_s) -∗
    code_logrel c c' ∅ A_t A_s.
  Proof with vsimp.
    iIntros (Hwf Hwf') "Hi"; iIntros (??) "CI"; cbn.
    vsimp. setoid_rewrite instr_conv_ret.

    iInduction c as [| a l] "IHl" forall (c' Hwf' i_t i_s A_t A_s); cbn...
    { iDestruct (big_sepL2_nil_inv_l with "Hi") as %Hx;
        subst; cbn...
      Cut... do 2 vfinal; iExists ∅, ∅; iFrame. }

    iDestruct (big_sepL2_cons_inv_l with "Hi") as (???) "(CI1 & CI2)".
    destruct a, x2; subst; cbn -[denote_instr]... Cut...

    (* TODO: Pull out lemma *)
    cbn in Hwf; apply andb_prop_elim in Hwf;
      destruct Hwf as (HW1 & HW2).
    cbn in Hwf'; apply andb_prop_elim in Hwf';
      destruct Hwf' as (HW1' & HW2').

    Cut...
    mono: (iApply ("CI1" with "CI")) with "[CI2]"...
    Cut... iDestruct "HΦ" as (??) "CI".
    iSpecialize ("IHl" $! HW2 _ HW2' with "CI2 CI").
    iPoseProof (sim_expr_fmap_inv with "IHl") as "H".

    mono: iApply "H"...
    iDestruct "HΦ" as (??????) "H". destruct r_t, r_s.
    repeat vfinal.
    iExists (nA_t0 ++ nA_t), (nA_s0 ++ nA_s).
    by rewrite !app_assoc.
  Qed.

  Theorem block_compat b b' bid A_t A_s:
    block_WF b ->
    block_WF b' ->
    phis_logrel
      (denote_phis bid (blk_phis b))
      (denote_phis bid (blk_phis b'))
      ∅ A_t A_s -∗
    code_logrel
      (blk_code b)
      (blk_code b')
      ∅ A_t A_s -∗
    term_logrel
       (blk_term b)
       (blk_term b')
       ∅ -∗
    block_logrel b b' bid ∅ A_t A_s.
  Proof with vsimp.
    iIntros (WF_b WF_b') "HΦ Hc Ht".
    iIntros (??) "CI".
    cbn -[denote_phis]...
    setoid_rewrite instr_conv_bind at 3. Cut...

    (* Phis *)
    mono: (iApply ("HΦ" with "CI")) with "[Hc Ht]"...
    rewrite instr_conv_bind... Cut...

    (* Code block *)
    iSpecialize ("Hc" with "HΦ").
    rewrite /denote_code /map_monad_.
    rewrite !instr_conv_bind ; setoid_rewrite instr_conv_ret.
    iPoseProof (sim_expr_fmap_inv with "Hc") as "Hc".
    mono: (iApply "Hc") with "[Ht]"...
    iDestruct "HΦ" as ([][] _ _ ??) "HI".

    (* Well-formedness of block *)
    apply andb_prop_elim in WF_b, WF_b';
      destruct WF_b, WF_b'.

    (* Terminator *)
    mono: iApply "Ht"...

    iIntros (??) "H".
    iDestruct "H" as (????) "(Hi & H)".
    iExists _,_. rewrite H3 H4.
    do 2 (iSplitL ""; [ done | ]). iFrame.
    by iExists _, _.
  Qed.

  Theorem ocfg_compat (c c' : CFG.ocfg dtyp) b1 b2 A_t A_s:
    ocfg_WF c ->
    ocfg_WF c' ->
    □ ([∗ list] b; b' ∈ c; c',
        (* The blocks have the same block ids, in order  *)
        ⌜blk_id b = blk_id b'⌝ ∗
        (* and are logically related *)
        ∀ A_t A_s be, block_logrel b b' be ∅ A_t A_s) -∗
    ocfg_logrel c c' ∅ A_t A_s b1 b2.
  Proof with vsimp.
    iIntros (WF WF') "#Hb"; iIntros (??) "CI".
    rewrite /ocfg_WF in WF.
    rewrite /denote_ocfg.
    unfold CategoryOps.iter, CategoryKleisli.Iter_Kleisli,
      Basics.iter, MonadIter_itree.

    (* That's really ugly... TODO: Fix *)
    epose proof
      (@interp_iter' _ _ instrE_conv_h _ _
      (λ '(bid_from, bid_src),
        match CFG.find_block c bid_src with
        | Some block_src =>
            Monad.bind (denote_block block_src bid_from)
              (λ bd : block_id + uvalue,
                  match bd with
                  | inl bid_target => Monad.ret (inl (bid_src, bid_target))
                  | inr dv => Monad.ret (inr (inr dv))
                  end)
        | None => Monad.ret (inr (inl (bid_from, bid_src)))
        end)
      (λ i, interp instrE_conv_h
      (let
       '(bid_from, bid_src) := i in
        match CFG.find_block c bid_src with
        | Some block_src =>
            Monad.bind (denote_block block_src bid_from)
              (λ bd : block_id + uvalue,
                 match bd with
                 | inl bid_target => Monad.ret (inl (bid_src, bid_target))
                 | inr dv => Monad.ret (inr (inr dv))
                 end)
        | None => Monad.ret (inr (inl (bid_from, bid_src)))
        end)) _ (b1, b2)).
    Unshelve. 2 : intros; reflexivity.
    eapply EqAxiom.bisimulation_is_eq in H.
    rewrite /instr_conv. rewrite H; clear H.

    epose proof
      (@interp_iter' _ _ instrE_conv_h _ _
      (λ '(bid_from, bid_src),
        match CFG.find_block c' bid_src with
        | Some block_src =>
            Monad.bind (denote_block block_src bid_from)
              (λ bd : block_id + uvalue,
                  match bd with
                  | inl bid_target => Monad.ret (inl (bid_src, bid_target))
                  | inr dv => Monad.ret (inr (inr dv))
                  end)
        | None => Monad.ret (inr (inl (bid_from, bid_src)))
        end)
      (λ i, interp instrE_conv_h
      (let
       '(bid_from, bid_src) := i in
        match CFG.find_block c' bid_src with
        | Some block_src =>
            Monad.bind (denote_block block_src bid_from)
              (λ bd : block_id + uvalue,
                 match bd with
                 | inl bid_target => Monad.ret (inl (bid_src, bid_target))
                 | inr dv => Monad.ret (inr (inr dv))
                 end)
        | None => Monad.ret (inr (inl (bid_from, bid_src)))
        end)) _ (b1, b2)).
    Unshelve. 2 : intros; reflexivity.
    eapply EqAxiom.bisimulation_is_eq in H.
    rewrite /instr_conv. rewrite H.

    iApply sim_expr'_tau_inv.
    { iModIntro. iIntros (??). iSplitL.
      - iIntros "(Hb' & H & H')"; iFrame.
      - iIntros "(H & H')".
        iDestruct "H'" as (????) "H''".
        iFrame.
        iSplitL "".
        { rewrite /base. eauto. }
        eauto. }

    match goal with
    | |- context[sim_expr' _
          (Tau (ITree.iter ?body1 ?index1)) (Tau (ITree.iter ?body2 ?index2))] =>
        change (Tau (ITree.iter body1 index1)) with (guarded_iter' _ _ _ body1 index1);
        change (Tau (ITree.iter body2 index2)) with (guarded_iter' _ _ _ body2 index2)
    end.

    iApply (sim_expr_guarded_iter' _ _ (fun x y => ⌜x = y⌝
       ∗ code_inv_post ∅ i_t i_s A_t A_s)%I
             with "[Hb] [CI]"); cycle 1.
    { iSplitL ""; first done.
      by iExists ∅, ∅. }
    iModIntro.
    iIntros (??) "(%Heq & CI)"; rewrite Heq. destruct i_t0, i_s0; inv Heq.
    iDestruct "CI" as (??) "CI".
    iApply sim_expr_lift.

    (* The block for block id [b0] is in the OCFG. *)
    destruct (CFG.find_block c' b4) eqn: Hb0.
    { (* Since the two OCFG's have the same block ids, a related block can be found
         for the other OCFG. *)
      iPoseProof (code_same_block_ids_find_block c c'
        (fun b b' => ∀ A_t A_s be, block_logrel b b' be ∅ A_t A_s) with "Hb")%I
        as "H".
      iSpecialize ("H" $! _ _ Hb0); iDestruct "H" as (??) "Hrel". rewrite H0.

      (* FIXME: Why doesn't [vsimp] work here? *)
      rewrite interp_bind (interp_bind _ (denote_block b b3)).

      apply find_block_has_id in Hb0, H0.
      Cut...
      iSpecialize ("Hrel" with "CI").
      rewrite /instr_conv.
      iApply sim_expr_bupd_mono; [ | iApply "Hrel"]; eauto; cycle 1.

      iIntros (??) "H".
      iDestruct "H" as (??->->) "(H & l)".
      iDestruct "H" as (??) "H".
      vsimp.
      destruct r_t, r_s; try (iDestruct "l" as %Heq; inversion Heq).
      - rewrite !interp_ret. final; iLeft.
        iExists (b4, b5), (b4, b5); iFrame; eauto.
        do 3 (iSplitL ""; first done).
        rewrite !app_assoc.
        by iExists (nA_t0 ++ nA_t), (nA_s0 ++ nA_s).
      - do 2 rewrite interp_ret. final; iRight.
        iDestruct "l" as "#l". subst. iFrame.
        repeat iExists _; do 2 (iSplitL ""; eauto).
        iSplitL.
        { iExists (nA_t0 ++ nA_t), (nA_s0 ++ nA_s).
          by rewrite !app_assoc. }

        repeat iExists _; do 2 (iSplitL ""; eauto); done. }

    rewrite big_sepL2_sep. iDestruct "Hb" as "(Hblk & Hb)".

    iDestruct (code_same_block_ids_find_block_None with "Hblk") as %Heq.
    specialize (Heq b4); rewrite Hb0 in Heq. specialize (Heq eq_refl); rewrite Heq.
    rewrite interp_ret. final. iRight. iFrame.
    do 2 iExists _; do 2 (iSplitL ""; eauto).
    iSplitL "CI".
    { iExists nA_t, nA_s; by iFrame. }

    repeat iExists _; do 2 (iSplitL ""; eauto); done.
  Qed.

  Theorem cfg_compat c c' A_t A_s:
    cfg_WF c ->
    cfg_WF c' ->
    CFG.init c = CFG.init c' ->
    ocfg_logrel (blks c) (blks c') ∅ A_t A_s
      (CFG.init c) (CFG.init c) -∗
    cfg_logrel c c' ∅ A_t A_s.
  Proof with vsimp.
    iIntros (WF WF' Heq) "Hocfg". iIntros (??) "CI".
    setoid_rewrite interp_bind.
    destruct c, c'; cbn in *; subst.
    iSpecialize ("Hocfg" with "CI").
    iApply sim_expr'_bind; iApply (sim_expr'_bupd_mono); cycle 1.
    { iApply "Hocfg". }
    iIntros (??) "(H & HC)".
    iDestruct "H" as (??) "CI".
    iDestruct "HC" as (????) "HC".
    rewrite H H0. do 2 rewrite bind_ret_l.
    destruct v_t as [(?&?) | ], v_s as [(?&?) |];
      try (iDestruct "HC" as "%Hv"; inversion Hv); cycle 1.
    { do 2 rewrite interp_ret. iApply sim_expr'_base.
      iExists _,_.
      do 2 (iSplitL ""; [ done | ]). iFrame.
      by iExists nA_t,nA_s. }

    (* absurd *)
    rewrite /raise.
    rewrite interp_bind. iApply sim_expr_lift.
    iApply sim_expr_bind.
    unfold trigger. rewrite interp_vis.
    iApply sim_expr_bind.
    cbn. rewrite /subevent /resum /ReSum_inr /cat /Cat_IFun /inr_ /Inr_sum1.
    simp call_conv.
    iApply sim_expr_exception.
  Qed.
 
  Theorem fun_compat f f':
    fun_WF f ->
    fun_WF f' ->
    df_args f =  df_args f' ->
    (∀ A_t A_s, cfg_logrel (df_instrs f) (df_instrs f') ∅ A_t A_s) -∗
    fun_logrel f f' ∅.
  Proof with vsimp.
    iIntros (WF WF' Hargs_eq) "Hf".
    iIntros (i_t i_s args_t args_s Hlen) "Hs_t Hs_s Hv HC".

    rewrite /denote_function; cbn -[denote_cfg].
    destruct (length (df_args f') =? length args_s)%nat eqn : Hlen_args;
      cycle 1.
    { rewrite bind_bind bind_vis.
      setoid_rewrite interp_bind.
      setoid_rewrite interp_vis; rewrite bind_trigger.
      iApply sim_expr_lift.
      iApply sim_expr_exception_vis. }

    rewrite /val_rel.Forall2.
    iDestruct (big_sepL2_length  with "Hv") as %Hargs.
    assert (Hlen_f: (length (df_args f) =? length args_t = true)%nat).
    { apply PeanoNat.Nat.eqb_eq; subst. rewrite Hargs_eq.
      apply PeanoNat.Nat.eqb_eq in Hlen_args; rewrite Hlen_args; done. }
    rewrite Hlen_f. rewrite !bind_ret_l.

    rewrite -!(bind_bind (trigger MemPush)) /L0'expr_conv
      !(interp_bind _ (ITree.bind (trigger MemPush) _)).
    Cut...

    match goal with
      | |- context [sim_expr' _ ?l _] =>
          replace l with
            (r <- trigger MemPush ;;
              _ <- Tau (Ret r);;
              r <- trigger (StackPush (combine (df_args f) args_t)) ;;
              Tau (Ret r):
              expr vir_lang _)
     end ;cycle 1.
    (* TODO *)
    { eapply EqAxiom.bisimulation_is_eq.
      tau_steps; eapply eqit_Vis; intros; tau_steps.
      eapply eqit_Tau; intros; tau_steps.
      eapply eqit_Vis; intros; tau_steps.
      eapply eqit_Tau; intros; by tau_steps. }

    match goal with
      | |- context [sim_expr' _ _ ?R] =>
          replace R with
            (r <- trigger MemPush ;;
              _ <- Tau (Ret r);;
              r <- trigger (StackPush (combine (df_args f') args_s)) ;;
              Tau (Ret r):
              expr vir_lang _)
     end ;cycle 1.
    (* TODO *)
    { eapply EqAxiom.bisimulation_is_eq.
      tau_steps; eapply eqit_Vis; intros; tau_steps.
      eapply eqit_Tau; intros; tau_steps.
      eapply eqit_Vis; intros; tau_steps.
      eapply eqit_Tau; intros; by tau_steps. }

    rewrite -!bind_bind. Cut. rewrite !bind_bind.

    apply PeanoNat.Nat.eqb_eq in Hlen_args, Hlen_f.
    apply andb_prop_elim in WF. destruct WF.
    apply andb_prop_elim in WF'. destruct WF'.
    assert (Hnd: NoDup_b (df_args f) = true).
    { destruct (NoDup_b (df_args f)); done. }
    assert (Hnd': NoDup_b (df_args f') = true).
    { destruct (NoDup_b (df_args f')); done. }
    apply NoDup_b_NoDup in Hnd, Hnd'. clear H. rename H0 into WF.
    iCombine "Hs_t Hs_s" as "Hst".
    iApply (sim_expr'_bupd_mono with "[Hv HC Hf]");
      [ | iApply sim_expr_lift; iApply (frame_laws.sim_push_frame' with "Hst") ];
      [ | rewrite combine_fst | rewrite combine_fst ]; eauto.

    (* cbn -[denote_cfg]. *)
    iIntros (??) "H".
    iDestruct "H" as (??????)
        "(Hs_t & Hs_s & Ha_t & Ha_s & Hd_t & Hd_s & Harg_t & Harg_s)".
    rewrite H H0; clear H H0.
    vsimp. Tau. iApply sim_expr'_base...
    Cut... iApply instr_to_L0'.

    iDestruct "Hv" as "#Hv".
    iApply sim_expr'_bupd_mono;
      [ | iApply ("Hf" with
          "[HC Hs_t Hs_s Ha_t Ha_s Hd_t Hd_s Harg_t Harg_s]") ];
      eauto; cycle 1.
    { Unshelve.
      4 : exact (j_t :: i_t). 4 : exact (j_s :: i_s).
      2 : exact ∅. 2 : exact ∅.
      iExists (combine (df_args f) args_t),
              (combine (df_args f') args_s); iFrame.
      iSplitL "".
      { iPureIntro; eauto. }

      iSplitL "".
      { rewrite !combine_fst; auto. }
      { rewrite !combine_snd; eauto; iFrame.
        rewrite /val_rel.Forall2; iFrame "Hv".
        cbn.
        by rewrite NoDup_nil. } }

    clear e_t0 e_s0.

    iIntros (e_t e_s) "H".
    iDestruct "H" as (????) "(#Hr & HC)".
    rewrite H H0 !bind_ret_l.
    iDestruct "HC" as (??) "HC".

    iDestruct "HC" as (??) "CI".
    rewrite !app_nil_r.

    iDestruct "CI" as
      "(Hd_t&Hd_s&Hs_t&Hs_s&#HWF&%Heq&Hargs_t&Hargs_s&#Huv&HC&Ha_t&Ha_s&#Hbij)".
    iApply sim_expr_lift.

    iApply sim_update_si; iModIntro.
    iIntros (??) "SI".
    iDestruct (bij_laws.state_interp_WF with "SI") as "%WF_S".
    iFrame.
    iDestruct "HWF" as %HWF.

    repeat setoid_rewrite interp_bind.
    setoid_rewrite interp_ret.
    rewrite !interp_vis !bind_bind.
    setoid_rewrite interp_ret.
    setoid_rewrite bind_tau;
    setoid_rewrite bind_ret_l.
    setoid_rewrite interp_vis.
    setoid_rewrite bind_bind.
    setoid_rewrite interp_ret.
    setoid_rewrite bind_tau.
    setoid_rewrite bind_ret_l.
    setoid_rewrite <- bind_tau.
    rewrite -!bind_bind.
    iApply sim_expr_bind.
    iApply sim_expr_bupd_mono; cycle 1.
    { iDestruct "Hbij" as (Hnd_t Hnd_s) "Hbij".
      iPoseProof (frame_laws.sim_pop_frame_bij with
                   "Hs_t Hs_s Ha_t Ha_s HC Hbij") as "H";
        eauto.
      { intros. cbn in H1.
        assert (length i_s > 0).
        { cbn in H3. lia. } cbn; lia. } }

    iIntros (??) "H".
    iDestruct "H" as (??->->) "(HC & Hst & Hss)".
    final.
    iFrame. iExists _, _; iFrame "Hr"; done.
  Qed.

  Theorem fundefs_compat r r' Attr:
    ⌜fundefs_WF r Attr⌝ -∗
    ⌜fundefs_WF r' Attr⌝ -∗
    ([∗ list] '(v, f); '(v', f') ∈ r; r', fun_logrel f f' ∅) -∗
    fundefs_logrel r r' Attr Attr ∅.
  Proof with vsimp.
    rewrite /fundefs_logrel.
    iInduction r as [ | f l] "H" forall (r' Attr); first (iIntros; done).
    iIntros (WF WF') "Hf".
    iIntros (i f_t' f_s'
      addr_t addr_s attr Hlu_t Hlu_s Hattr_t Hattr_s) "#Hrel".
    iIntros (i_t i_s args_t args_s Hlen) "Hs_t Hs_s #Hargs HC".
    (* iIntros (τ Hcall). *)
    pose proof fundefs_WF_cons_inv. destruct Attr.
    { clear -Hattr_t. set_solver. }
    clear H.
    pose proof (fundefs_WF_cons_inv _ _ _ _ WF) as HWF_t.
    destruct HWF_t as (?&?).

    iDestruct (big_sepL2_cons_inv_l with "Hf") as (???)
      "(CI1 & CI2)". destruct x2; subst.
    pose proof (fundefs_WF_cons_inv _ _ _ _ WF') as HWF_s.
    destruct HWF_s as (?&?).
    destruct f.

    destruct i.
    { cbn in Hlu_t, Hlu_s, Hattr_t, Hattr_s.
      inversion Hlu_t; subst.
      inversion Hlu_s; subst.
      inversion Hattr_t; subst.
      iApply ("CI1" with "[] [Hs_t] [Hs_s]"); eauto. }
    { rewrite /fundefs_WF in H, H1.
      cbn in H, H1.
      iSpecialize ("H" $! _ _ H0 H2 with "CI2").
      inversion Hlu_t; inversion Hlu_s; inversion Hattr_t.
      iSpecialize ("H" $! i _ _ _ _ _ H4 H5 H6 H6
                  with "Hrel").
      iSpecialize ("H" $! _ _ _ _ Hlen with "Hs_t Hs_s Hargs HC"). done. }
  Qed.

End compatibility.
