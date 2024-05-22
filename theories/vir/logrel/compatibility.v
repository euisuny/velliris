From iris.prelude Require Import options.

From velliris.vir.lang Require Import lang.
From velliris.vir.rules Require Import rules.
From velliris.vir.logrel Require Import wellformedness logical_relations.

Set Default Proof Using "Type*".

Import ListNotations.
Import SemNotations.
Import LLVMAst.

(** *Compatibility lemmas *)

Section compatibility.

  Context {Σ : gFunctors} `{!vellirisGS Σ}.

(* ------------------------------------------------------------------------ *)
  (* Utility *)

  Lemma local_bij_except_add {l_t l_s args_t args_s v_t v_s i_t i_s x}:
    x ∈ (remove_ids l_t args_t).*1 ->
    uval_rel v_t v_s -∗
    local_bij i_t i_s
      (alist_add x v_t (alist_remove x (remove_ids l_t args_t)))
      (alist_add x v_s (alist_remove x (remove_ids l_s args_s))) -∗
    local_bij_except l_t l_s i_t i_s args_t args_s.
  Proof.
  Admitted.

  Lemma local_bij_except_add_notin {l_t l_s args_t args_s v_t v_s i_t i_s x}:
    x ∉ (remove_ids l_t args_t).*1 ->
    uval_rel v_t v_s -∗
    local_bij_except l_t l_s i_t i_s args_t args_s -∗
    [ x := v_s ]s i_s -∗
    [ x := v_t ]t i_t -∗
    local_bij_except l_t l_s i_t i_s
      (alist_add x v_t args_t)
      (alist_add x v_s args_s).
  Proof.
  Admitted.

  Lemma remove_ids_not_elem_of
    {K : Type} {R : K → K → Prop} `{RelDec.RelDec _ R}:
      ∀ {V : Type} (l: list K) (L: alist K V) x,
    x ∉ l ->
    x ∉ (remove_ids l L).*1 ->
    x ∉ L.*1.
  Proof. Admitted.

(* ------------------------------------------------------------------------ *)

  (* LATER: See if the [id] generalization is also possible *)
  Theorem phi_compat ΠL ΠA bid bid' id ϕ ϕ' C A_t A_s:
    (let '(Phi dt  args )  := ϕ in
    let '(Phi dt' args')  := ϕ' in
    (* Look up on both sides which block it came from, and resolve the
        expressions *)
    match Util.assoc bid args, Util.assoc bid' args' with
    | Some op, Some op' =>
        expr_logrel ΠL ΠA C
          (Some dt) (Some dt') op op' A_t A_s
    | None, None => True
    | _ , _ => False
    end) -∗
    phi_logrel ΠL ΠA
      bid bid' (id, ϕ) (id, ϕ') C A_t A_s.
  Proof with vsimp.
    iIntros "He" (????) "H".
    destruct ϕ, ϕ'; cbn.
    rename t0 into t', args0 into args'.

    destruct (Util.assoc bid' args') eqn: H; [ | iApply exp_conv_raise].
    destruct (Util.assoc bid args) eqn: H'; last done...

    Cut; mono: iApply "He"...
    { iDestruct "HΦ" as "(Hv & HΦ)"; vfinal. }

    sfinal.
  Qed.

  Lemma phi_list_compat ΠL ΠA bid Φ Φ' C i_t i_s A_t A_s:
    ([∗ list] ϕ;ϕ' ∈ Φ; Φ',
        phi_logrel ΠL ΠA bid bid ϕ ϕ' C A_t A_s) -∗
    code_inv ΠL ΠA C i_t i_s A_t A_s -∗
    instr_conv (map_monad (λ x, translate exp_to_instr (denote_phi bid x)) Φ) ⪯
      instr_conv (map_monad (λ x, translate exp_to_instr (denote_phi bid x)) Φ')
    [{ (r_t, r_s),
        ⌜r_t.*1 = Φ.*1⌝ ∗
        ⌜r_s.*1 = Φ'.*1⌝ ∗
        ([∗ list] v_t; v_s ∈ r_t; r_s, uval_rel v_t.2 v_s.2)
            ∗ code_inv ΠL ΠA C i_t i_s A_t A_s }].
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
    destruct_code_inv.

    Cut...
    iApply (sim_expr_bupd_mono with "[IH]"); [ | iApply "He"];
      try iFrame; eauto; cycle 1.

    cbn. iIntros (??) "H".
    iDestruct "H" as (????) "(#H & CI)".
    rewrite H H0...

    iSpecialize ("IH" with "CI"). subst.
    Cut... mono: (iApply "IH")...
    iDestruct "HΦ" as (??) "(H' & CI)".
    vfinal; cbn; vsimp; iFrame "H".
    rewrite H H0; done.
  Qed.

  (* TODO Move *)
  Lemma local_write_frame_source_alloc {R}
    {x_s v_s i_t i_s C} {L_t L_s : local_env} {e_t: _ R} Q:
    x_s ∉ L_s.*1 ->
    ⊢ frameR i_t i_s L_t.*1 L_s.*1 C -∗
      ([ x_s := v_s ]s i_s -∗
      frameR i_t i_s L_t.*1 (alist_add x_s v_s L_s).*1 C -∗
      e_t ⪯ Ret () [{ Q }]) -∗
      e_t ⪯ trigger (LocalWrite x_s v_s)
      [{ Q }].
  Proof.
    iIntros (He) "Hf HΦ".
    destruct_frame.
    iDestruct "Hft" as (?) "(Hs_t & Hd_t)".
    iDestruct "Hfs" as (?) "(Hs_s & Hd_s)".
    iApply source_red_sim_expr.
    iApply (source_red_mono with "[HΦ]");
      last (iApply (source_local_write_alloc with "Hd_s Hs_s")); cycle 1.
    { set_solver. }
    { iIntros "Hx Hd Hs".
      Unshelve.
      2 : exact (fun x => ⌜x = Ret tt⌝ ∗ [ x_s := v_s ]s i_s ∗
         frameR i_t i_s L_t.*1 (alist_add x_s v_s L_s).*1 C)%I.
      iFrame; iFrame "WF_frame"; sfinal.
      cbn; rewrite alist_remove_not_in; eauto; iFrame.
      iPureIntro; apply NoDup_cons; split; eauto. }
    iIntros (?) "H"; iDestruct "H" as (?) "(Hxs & Hf)".
    subst. iApply ("HΦ" with "Hxs Hf").
  Qed.

  Lemma local_write_frame_target_alloc {R}
    {x_t v_t i_t i_s C} {L_t L_s : local_env} {e_s: _ R} Q:
    x_t ∉ L_t.*1 ->
    ⊢ frameR i_t i_s L_t.*1 L_s.*1 C -∗
      ([ x_t := v_t ]t i_t -∗
      frameR i_t i_s (alist_add x_t v_t L_t).*1 L_s.*1 C -∗
      Ret () ⪯ e_s [{ Q }]) -∗
      trigger (LocalWrite x_t v_t) ⪯ e_s
      [{ Q }].
  Proof.
    iIntros (He) "Hf HΦ".
    destruct_frame.
    iDestruct "Hft" as (?) "(Hs_t & Hd_t)".
    iDestruct "Hfs" as (?) "(Hs_s & Hd_s)".
    iApply target_red_sim_expr.
    iApply (target_red_mono with "[HΦ]");
      last (iApply (target_local_write_alloc with "Hd_t Hs_t")); cycle 1.
    { set_solver. }
    { iIntros "Hx Hd Hs".
      Unshelve.
      2 : exact (fun x => ⌜x = Ret tt⌝ ∗
                [ x_t := v_t ]t i_t ∗
                frameR i_t i_s (alist_add x_t v_t L_t).*1 L_s.*1 C)%I.
      iFrame; iFrame "WF_frame"; sfinal.
      cbn; rewrite alist_remove_not_in; eauto; iFrame.
      iPureIntro. split; auto. apply NoDup_cons; split; eauto. }
    iIntros (?) "H"; iDestruct "H" as (?) "(Hxs & Hf)".
    subst. iApply ("HΦ" with "Hxs Hf").
  Qed.

  Lemma local_write_frame_source {R}
    x_s v_s v_s' i_t i_s L_t L_s C (e_t: _ R) Q:
    ⊢ frameR i_t i_s L_t L_s C -∗
      [ x_s := v_s ]s i_s -∗
      ([ x_s := v_s' ]s i_s -∗
      frameR i_t i_s L_t L_s C -∗
      e_t ⪯ Ret () [{ Q }]) -∗
      e_t ⪯ trigger (LocalWrite x_s v_s')
      [{ Q }].
  Proof.
    iIntros "Hf Hxs HΦ".
    destruct_frame.
    iDestruct "Hft" as (?) "(Hs_t & Hd_t)".
    iDestruct "Hfs" as (?) "(Hs_s & Hd_s)".
    iApply source_red_sim_expr.
    iApply (source_red_mono with "[HΦ]");
      last (iApply (source_local_write with "Hxs Hs_s")); cycle 1.
    { iIntros "Hx Hs".
      Unshelve.
      2 : exact (fun x => ⌜x = Ret tt⌝ ∗ [ x_s := v_s' ]s i_s ∗ frameR i_t i_s L_t L_s C)%I.
      iFrame; iFrame "WF_frame"; done. }
    iIntros (?) "H"; iDestruct "H" as (?) "(Hxs & Hf)".
    subst. iApply ("HΦ" with "Hxs Hf").
  Qed.

  Lemma local_write_frame_target {R}
    x_t v_t v_t' i_t i_s L_t L_s C (e_s: _ R) Q:
    ⊢ frameR i_t i_s L_t L_s C -∗
      [ x_t := v_t ]t i_t -∗
      ([ x_t := v_t' ]t i_t -∗
      frameR i_t i_s L_t L_s C -∗
      Ret () ⪯ e_s [{ Q }]) -∗
      trigger (LocalWrite x_t v_t') ⪯ e_s
      [{ Q }].
  Proof.
    iIntros "Hf Hxs HΦ".
    destruct_frame.
    iDestruct "Hft" as (?) "(Hs_t & Hd_t)".
    iDestruct "Hfs" as (?) "(Hs_s & Hd_s)".
    iApply target_red_sim_expr.
    iApply (target_red_mono with "[HΦ]");
      last (iApply (target_local_write with "Hxs Hs_t")); cycle 1.
    { iIntros "Hx Hs".
      Unshelve.
      2 : exact (fun x => ⌜x = Ret tt⌝ ∗ [ x_t := v_t' ]t i_t ∗ frameR i_t i_s L_t L_s C)%I.
      iFrame; iFrame "WF_frame"; done. }
    iIntros (?) "H"; iDestruct "H" as (?) "(Hxs & Hf)".
    subst. iApply ("HΦ" with "Hxs Hf").
  Qed.

  Lemma local_write_bij_except
    ΠA C x v_t v_s i_t i_s A_t A_s l_t l_s Q:
    x ∉ l_t ->
    x ∉ l_s ->
    code_inv (local_bij_except l_t l_s) ΠA C i_t i_s A_t A_s -∗
    uval_rel v_t v_s -∗
    (code_inv (local_bij_except l_t l_s) ΠA C i_t i_s A_t A_s -∗
      Ret tt ⪯ Ret tt [{ Q }]) -∗
    trigger (LocalWrite x v_t) ⪯ trigger (LocalWrite x v_s)
    [{ Q }].
  Proof.
    iIntros (Hnt Hns) "CI #Hv HΦ"; destruct_code_inv.

    (* The location is in bijection *)
    destruct (decide (x ∈ (remove_ids l_t args_t).*1)).
    { destruct_local_inv.
      iDestruct (local_bij_remove x with "HL") as (??)
        "(Hxt & Hxs & #Hv' & HL)"; auto.

      iApply (local_write_frame_source with "Hf Hxs"); iIntros "Hxs Hf".
      iApply (local_write_frame_target with "Hf Hxt"); iIntros "Hxt Hf".

      iApply ("HΦ" with "[AI Hf HL Hxs Hxt]"); iFrame.
      iPoseProof (local_bij_add with "Hxt Hxs Hv HL") as "Hbij".
      { admit. }
      iExists args_t, args_s; iFrame.
      rewrite /local_bij_except.

      iApply (local_bij_except_add e with "Hv Hbij"). }

    (* The location is not in bijection *)
    { destruct_local_inv.

      iDestruct (local_bij_elem_of with "HL") as %Hdom.
      rewrite Hdom in n.
      mono: iApply (local_write_frame_source_alloc Q with "Hf").
      { by iIntros (??) "H". }
      { eapply (remove_ids_not_elem_of l_s); eauto. }
      iIntros "Hs Hf".

      mono: iApply (local_write_frame_target_alloc Q with "Hf").
      { by iIntros (??) "H". }
      { rewrite -Hdom in n;
        eapply (remove_ids_not_elem_of l_t); eauto. }
      iIntros "Ht Hf".
      iApply "HΦ"; iFrame.
      iExists (alist_add x v_t args_t), (alist_add x v_s args_s); iFrame.
      iApply (local_bij_except_add_notin with "Hv HL Hs Ht").
      by rewrite Hdom. }
  Admitted.

  (* Phi instructions are compatible up to equivalent phi identifiers and that
     the phi identifiers are in bijection. *)
  Theorem phis_compat ΠA C bid Φ Φ' A_t A_s l_t l_s:
    Φ.*1 ## l_t ->
    Φ'.*1 ## l_s ->
    Φ.*1 = Φ'.*1 ->
    ([∗ list] ϕ;ϕ' ∈ Φ; Φ',
       phi_logrel (local_bij_except l_t l_s)
         ΠA bid bid ϕ ϕ' C A_t A_s) -∗
    phis_logrel (local_bij_except l_t l_s)
      ΠA bid bid Φ Φ' C A_t A_s.
  Proof with vsimp.
    iIntros (Hnt Hns Heq) "HΦ"; iIntros (??) "CI".
    iPoseProof (phi_list_compat with "HΦ CI") as "H".
    rewrite /denote_phis... Cut...
    mono: iApply "H"...
    iDestruct "HΦ" as (Hrt Hrs) "(H & CI)".
    setoid_rewrite instr_conv_ret.

    iInduction r_s as [] "IH" forall (r_t Hrt Hrs).
    { iDestruct (big_sepL2_nil_inv_r with "H") as %Hx; subst; cbn...
      Cut... do 2 vfinal. }

    iDestruct (big_sepL2_cons_inv_r with "H") as (???) "(#Hv & #CI2)";
    destruct a, x1; subst; cbn...
    Cut...
    iClear "H".

    Cut... assert (l0 = l) by admit. subst.
    iApply (local_write_bij_except with "CI Hv").
    1,2: admit.
    iIntros "CI"; vfinal... vfinal...

    iSpecialize ("IH" $! _ _ _ with "CI2 CI")...
    iPoseProof (sim_expr_fmap_inv with "IH") as "Hf".
    Cut.

    mono: iApply "Hf"...

    iDestruct "HΦ" as (????) "HΦ".
    apply eqitree_inv_Ret in H, H0; subst.
    do 2 vfinal.
  Admitted.

  Theorem code_compat ΠL ΠA (c c' : code dtyp) A_t A_s:
    code_WF c ->
    code_WF c' ->
    ([∗ list] '(id, i); '(id', i') ∈ c; c',
        ∀ i_t i_s A_t A_s, instr_logrel ΠL ΠA i_t i_s id i id' i' ∅ A_t A_s) -∗
    code_logrel ΠL ΠA c c' ∅ A_t A_s.
  Proof with vsimp.
    iIntros (Hwf Hwf') "Hi"; iIntros (??) "CI"; cbn.
    vsimp. setoid_rewrite instr_conv_ret.

    iInduction c as [| a l] "IHl" forall (c' Hwf' i_t i_s A_t A_s); cbn...
    { iDestruct (big_sepL2_nil_inv_l with "Hi") as %Hx;
        subst; cbn...
      Cut... do 2 vfinal; iExists ∅, ∅; iFrame. }

    iDestruct (big_sepL2_cons_inv_l with "Hi") as (???) "(CI1 & CI2)".
    destruct a, x2; subst; cbn -[denote_instr]... Cut...
    apply code_WF_cons_inv in Hwf; destruct Hwf as (Hwf1 & Hwf2).
    apply code_WF_cons_inv in Hwf'; destruct Hwf' as (Hwf'1 & Hwf'2).

    Cut...
    (* mono: (iApply ("CI1" with "CI")) with "[CI2]"... *)
    (* Cut... iDestruct "HΦ" as (??) "CI". *)
    (* iSpecialize ("IHl" $! Hwf2 _ Hwf'2 with "CI2 CI"). *)
    (* iPoseProof (sim_expr_fmap_inv with "IHl") as "H". *)

    (* mono: iApply "H"... *)
    (* iDestruct "HΦ" as (??????) "H". destruct r_t, r_s. *)
    (* repeat vfinal. *)
    (* iExists (nA_t0 ++ nA_t), (nA_s0 ++ nA_s). *)
    (* by rewrite !app_assoc. *)
  Admitted.

  Theorem block_compat ΠL ΠA b b' bid A_t A_s:
    block_WF b ->
    block_WF b' ->
    phis_logrel ΠL ΠA
      bid bid (blk_phis b) (blk_phis b')
      ∅ A_t A_s -∗
    code_logrel ΠL ΠA
      (blk_code b)
      (blk_code b')
      ∅ A_t A_s -∗
    term_logrel ΠL ΠA
      (blk_term b)
      (blk_term b')
      ∅ -∗
    block_logrel ΠL ΠA b b' bid ∅ A_t A_s.
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

    apply block_WF_inv in WF_b, WF_b'.
    destruct WF_b as (WF_c & WF_t); destruct WF_b' as (WF_c' & WF_t').

    (* Terminator *)
    mono: iApply "Ht"...

    iIntros (??) "H".
    iDestruct "H" as (????) "(Hi & H)".
    iExists _,_. rewrite H H0.
    do 2 (iSplitL ""; [ done | ]). iFrame.
    by iExists _, _.
  Qed.

  Theorem ocfg_compat ΠL ΠA (c c' : CFG.ocfg dtyp) b1 b2 A_t A_s:
    ocfg_WF c ->
    ocfg_WF c' ->
    □ ([∗ list] b; b' ∈ c; c',
        (* The blocks have the same block ids, in order  *)
        ⌜blk_id b = blk_id b'⌝ ∗
        (* and are logically related *)
        ∀ A_t A_s be, block_logrel ΠL ΠA b b' be ∅ A_t A_s) -∗
    ocfg_logrel ΠL ΠA c c' ∅ A_t A_s b1 b2.
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
      ∗ code_inv_post ΠL ΠA ∅ i_t i_s A_t A_s)%I
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
        (fun b b' => ∀ A_t A_s be, block_logrel ΠL ΠA b b' be ∅ A_t A_s) with "Hb")%I
        as "H".
      iSpecialize ("H" $! _ _ Hb0); iDestruct "H" as (??) "Hrel". rewrite H0.

      (* FIXME: Why doesn't [vsimp] work here? *)
      rewrite interp_bind (interp_bind _ (denote_block b b3)).

      apply ScopeTheory.find_block_has_id in Hb0, H0.
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

  Theorem cfg_compat ΠL ΠA c c' A_t A_s:
    cfg_WF c ->
    cfg_WF c' ->
    CFG.init c = CFG.init c' ->
    ocfg_logrel ΠL ΠA (blks c) (blks c') ∅ A_t A_s
      (CFG.init c) (CFG.init c) -∗
    cfg_logrel ΠL ΠA c c' ∅ A_t A_s.
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

  (* LATER: Generalize [alloca_bij] relation *)
  Theorem fun_compat ΠL f f':
    fun_WF f ->
    fun_WF f' ->
    df_args f =  df_args f' ->
    (* Related arguments on the function imply the invariant *)
    (∀ args_t args_s i_t i_s,
      ⌜df_args f = args_s.*1⌝ -∗
      ⌜df_args f = args_t.*1⌝ -∗
      ([∗ list] '(l_t, v_t) ∈ args_t, [ l_t := v_t ]t i_t) -∗
      ([∗ list] '(l_s, v_s) ∈ args_s, [ l_s := v_s ]s i_s) -∗
      ([∗ list] y1;y2 ∈ args_t.*2;args_s.*2, uval_rel y1 y2) -∗
      ΠL i_t i_s args_t args_s) -∗
    (∀ A_t A_s, cfg_logrel ΠL alloca_bij (df_instrs f) (df_instrs f') ∅ A_t A_s) -∗
    fun_logrel f f' ∅.
  Proof with vsimp.
    iIntros (WF WF' Hargs_eq) "HInv Hf".
    iIntros (i_t i_s args_t args_s Hlen) "Hs_t Hs_s Hv HC".

    rewrite /denote_function; cbn -[denote_cfg].

    destruct (length (df_args f') =? length args_s)%nat eqn : Hlen_args;
      cycle 1.
    { vsimp.
      setoid_rewrite interp_bind; setoid_rewrite interp_vis...
      setoid_rewrite bind_vis at 6. iApply sim_expr_lift.
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
    rewrite /fun_WF in WF, WF'.
    apply PeanoNat.Nat.eqb_eq in Hlen_args, Hlen_f.
    destructb. apply NoDup_b_NoDup in H1, H.

    (* Push 'em on the stack. *)
    iCombine "Hs_t Hs_s" as "Hst".
    iApply (sim_expr'_bupd_mono with "[Hv HC Hf HInv]");
      [ | iApply sim_expr_lift; iApply (frame_laws.sim_push_frame' with "Hst") ];
      [ | rewrite combine_fst | rewrite combine_fst ]; eauto.

    iIntros (??) "H".
    iDestruct "H" as (??????)
        "(Hs_t & Hs_s & Ha_t & Ha_s & Hd_t & Hd_s & Harg_t & Harg_s)".
    rewrite H3 H4; clear H3 H4.
    vsimp. Tau. iApply sim_expr'_base...
    Cut... iApply instr_to_L0'.

    iDestruct "Hv" as "#Hv".
    iApply sim_expr'_bupd_mono;
      [ | iApply ("Hf" with
          "[HInv HC Hs_t Hs_s Ha_t Ha_s Hd_t Hd_s Harg_t Harg_s]") ];
      eauto; cycle 1.
    { Unshelve.
      4 : exact (j_t :: i_t). 4 : exact (j_s :: i_s).
      2 : exact ∅. 2 : exact ∅.
      iExists (combine (df_args f) args_t),
              (combine (df_args f') args_s); iFrame.
      iSplitR ""; cycle 1.
      { cbn. iPureIntro; split; eauto; split; by apply NoDup_nil. }
      iSplitL "".
      { iPureIntro; split; eauto; split; rewrite combine_fst; eauto. }

      iApply ("HInv" $! _ _ _ _ _ _ with "Harg_t Harg_s").
      do 2 (rewrite combine_snd; eauto); done. }

    clear e_t0 e_s0.

    iIntros (e_t e_s) "H".
    iDestruct "H" as (????) "(#Hr & HC)".
    rewrite H3 H4 !bind_ret_l.
    iDestruct "HC" as (??) "HC".

    iDestruct "HC" as (??) "CI".
    rewrite !app_nil_r.

    iApply sim_expr_lift.

    iApply sim_update_si; iModIntro.
    iIntros (??) "SI".
    iDestruct (bij_laws.state_interp_WF with "SI") as "%WF_S".
    iFrame.

    iDestruct "CI" as "(LI & AI)".
    destruct_local_inv.
    destruct_alloca_inv.

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
    { do 3 destruct_frame.
      (* I think we need a variant where we have full ownership of
         everything. *)
      iPoseProof (frame_laws.sim_pop_frame_bij with
                  "Hs_t Hs_s Ha_t Ha_s CI") as "H";
        eauto.
      { intros. cbn in H1.
        assert (length i_s > 0).
        { cbn in H5. lia. } cbn; lia. }

      change (Vis (call_conv () (subevent () StackPop)) ret) with
        (trigger StackPop : expr vir_lang _).

      change (Vis (call_conv () (subevent () MemPop)) ret) with
        (trigger MemPop : expr vir_lang _).
      iApply "H". iApply "AI". }

    iIntros (??) "H".
    iDestruct "H" as (??->->) "(HC & Hst & Hss)".
    final.
    iFrame. iExists _, _; iFrame "Hr"; done.
    Unshelve.
    all: rewrite combine_fst; eauto.
  Qed.

  (* Theorem fundefs_compat r r' Attr: *)
  (*   ⌜fundefs_WF r Attr⌝ -∗ *)
  (*   ⌜fundefs_WF r' Attr⌝ -∗ *)
  (*   ([∗ list] '(v, f); '(v', f') ∈ r; r', fun_logrel f f' ∅) -∗ *)
  (*   fundefs_logrel r r' Attr Attr ∅. *)
  (* Proof with vsimp. *)
  (*   rewrite /fundefs_logrel. *)
  (*   iInduction r as [ | f l] "H" forall (r' Attr); first (iIntros; done). *)
  (*   iIntros (WF WF') "Hf". *)
  (*   iIntros (i f_t' f_s' *)
  (*     addr_t addr_s attr Hlu_t Hlu_s Hattr_t Hattr_s) "#Hrel". *)
  (*   iIntros (i_t i_s args_t args_s Hlen) "Hs_t Hs_s #Hargs HC". *)
  (*   (* iIntros (τ Hcall). *) *)
  (*   pose proof fundefs_WF_cons_inv. destruct Attr. *)
  (*   { clear -Hattr_t. set_solver. } *)
  (*   clear H. *)
  (*   pose proof (fundefs_WF_cons_inv _ _ _ _ WF) as HWF_t. *)
  (*   destruct HWF_t as (?&?). *)

  (*   iDestruct (big_sepL2_cons_inv_l with "Hf") as (???) *)
  (*     "(CI1 & CI2)". destruct x2; subst. *)
  (*   pose proof (fundefs_WF_cons_inv _ _ _ _ WF') as HWF_s. *)
  (*   destruct HWF_s as (?&?). *)
  (*   destruct f. *)

  (*   destruct i. *)
  (*   { cbn in Hlu_t, Hlu_s, Hattr_t, Hattr_s. *)
  (*     inversion Hlu_t; subst. *)
  (*     inversion Hlu_s; subst. *)
  (*     inversion Hattr_t; subst. *)
  (*     iApply ("CI1" with "[] [Hs_t] [Hs_s]"); eauto. } *)
  (*   { rewrite /fundefs_WF in H, H1. *)
  (*     cbn in H, H1. *)
  (*     iSpecialize ("H" $! _ _ H0 H2 with "CI2"). *)
  (*     inversion Hlu_t; inversion Hlu_s; inversion Hattr_t. *)
  (*     iSpecialize ("H" $! i _ _ _ _ _ H4 H5 H6 H6 *)
  (*                 with "Hrel"). *)
  (*     iSpecialize ("H" $! _ _ _ _ Hlen with "Hs_t Hs_s Hargs HC"). done. } *)
  (* Qed. *)

End compatibility.
