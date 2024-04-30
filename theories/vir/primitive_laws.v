(** * Primitive Laws. *)

From iris.prelude Require Import options.

From velliris.program_logic Require Import program_logic.
From velliris.vir Require Export vir vir_state spec util.

From ITree Require Import
  ITree Eq.Eqit Eq.EqAxiom Events.State Events.StateFacts Extra.IForest.
From Vellvm Require Import Semantics.LLVMEvents Handlers.Handlers Handlers.MemoryTheory.
Set Default Proof Using "Type*".

Section proof.

  Context {Σ} `{!vellirisGS Σ}.

  Lemma non_void_allocate_abs:
    forall τ σ s, non_void τ -> ~ (allocate σ τ = inl s).
  Proof.
    intros; destruct τ; eauto.
  Qed.

  Lemma source_red_alloca τ `{non_void τ} Ψ S_s i:
    alloca_src i S_s -∗
    stack_src i -∗
    (∀ z,
        ⌜z ∉ S_s⌝ -∗
        z ↦s [ make_empty_logical_block τ ] -∗
        alloca_src i ({[ z ]} ∪ S_s) -∗
        stack_src i -∗
        source_block_size z (Some (N.to_nat (sizeof_dtyp τ))) -∗
        (* TODO: Change - Ψ (DVALUE_Addr (z, 0%Z))*)
        source_red (η := vir_handler) (Ret (DVALUE_Addr (z, 0%Z))) Ψ) -∗
    source_red (η := vir_handler) (trigger (Alloca τ)) Ψ.
  Proof.
    rewrite !source_red_eq !source_red_def_unfold /source_red_rec.
    iIntros "Hal Hf Hl". iLeft. iIntros (σ_t σ_s) "SI".

    destruct (allocate (vmem σ_s) τ) eqn: Ht.
    { exfalso; eapply non_void_allocate_abs; eauto. }
    destruct p.

    (** *HEAP *)
    (* Allocation is successful on source and source logical views *)
    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & SI)".

    iCombine "Hal Hf Hh_s" as "Hs".
    iMod (heap_allocate_1 with "Hs") as "(Hh_s & %Hdom & Hal & Hf & Hl_s' & Hbs)"; eauto.
    destruct a; cbn.

    iSpecialize ("Hl" $! _ Hdom with "Hl_s' Hal Hf Hbs").

    iModIntro.
    iExists dvalue,
      (DVALUE_Addr (z, z0)),(fun x => Tau (Ret x)),
      (update_mem m σ_s).
    iSplitL "".

    { iPureIntro.
      match goal with
      | |- _ ≅ ?r => remember r as RHS
      end.
      unfold interp_L2. rewrite interp_state_vis.
      rewrite /add_tau bind_tau. cbn.
      do 2 rewrite bind_bind.
      unfold lift_pure_err. rewrite Ht.
      rewrite !bind_ret_l interp_state_ret.
      subst. rewrite bind_tau bind_ret_l.
      apply eqitree_Tau; cbn.
      rewrite /interp_L2.
      by rewrite interp_state_tau interp_state_ret. }
    iFrame.

    apply allocate_inv in Ht.
    destruct Ht as (?&?&?). inversion H0; subst.
    inversion H1; subst.

    iSplitR "Hl"; cycle 1.
    { pose proof (source_red_tau (η := vir_handler) Ψ).
      rewrite source_red_eq in H0.
      iApply H0. cbn. iApply "Hl". }
    cbn.

    iExists C, S, G; iFrame.

    rewrite -!vir_logical_frame_add_to_frame.
    cbn in *. unfold frames; cbn.
    destruct (vmem σ_s); cbn in *.
    destruct f; cbn -[frame_at]; iFrame.
  Qed.

  Lemma target_red_alloca τ `{non_void τ} Ψ S_s i:
    alloca_tgt i S_s -∗
    stack_tgt i -∗
    (∀ z,
        ⌜z ∉ S_s⌝ -∗
        z ↦t [ make_empty_logical_block τ ] -∗
        alloca_tgt i ({[ z ]} ∪ S_s) -∗
        stack_tgt i -∗
        target_block_size z (Some (N.to_nat (sizeof_dtyp τ))) -∗
        target_red (η := vir_handler) (Ret (DVALUE_Addr (z, 0%Z))) Ψ) -∗
    target_red (η := vir_handler) (trigger (Alloca τ)) Ψ.
  Proof.
    rewrite !target_red_eq !target_red_def_unfold /target_red_rec.
    iIntros "Hal Hf Hl". iLeft. iIntros (σ_t σ_s) "SI".

    destruct (allocate (vmem σ_t) τ) eqn: Ht.
    { exfalso; eapply non_void_allocate_abs; eauto. }
    destruct p.

    (** *HEAP *)
    (* Allocation is successful on target and target logical views *)
    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & SI)".

    iCombine "Hal Hf Hh_t" as "Ht".
    iMod (heap_allocate_1 with "Ht") as
      "(Hh_t & %Hdom & Hal & Hf & Hl_t' & Hbs)"; eauto.

    destruct a; cbn.

    iSpecialize ("Hl" $! _ Hdom with "Hl_t' Hal Hf Hbs").

    iModIntro.
    iExists dvalue,
      (DVALUE_Addr (z, z0)),(fun x => Tau (Ret x)),
      (update_mem m σ_t).
    iSplitL "".

    { iPureIntro.
      match goal with
      | |- _ ≅ ?r => remember r as RHS
      end.
      unfold interp_L2. rewrite interp_state_vis.
      rewrite /add_tau bind_tau. cbn.
      do 2 rewrite bind_bind.
      unfold lift_pure_err. rewrite Ht.
      rewrite !bind_ret_l interp_state_ret. 
      subst. rewrite bind_tau bind_ret_l.
      apply eqitree_Tau; cbn.
      rewrite /interp_L2.
      by rewrite interp_state_tau interp_state_ret. }
    iFrame.

    apply allocate_inv in Ht.
    destruct Ht as (?&?&?). inversion H0; subst.
    inversion H1; subst.

    iSplitR "Hl"; cycle 1.
    { pose proof (target_red_tau (η := vir_handler) Ψ).
      rewrite target_red_eq in H0.
      iApply H0. cbn. iApply "Hl". }
    cbn.

    iExists C, S, G; iFrame.

    rewrite -!vir_logical_frame_add_to_frame.
    cbn in *. unfold frames; cbn.
    destruct (vmem σ_t); cbn in *.
    destruct f; cbn -[frame_at]; iFrame.
  Qed.

  Lemma sim_alloca τ S_t S_s i_t i_s `{non_void τ}:
    alloca_tgt i_t S_t -∗
    alloca_src i_s S_s -∗
    stack_tgt i_t -∗
    stack_src i_s -∗
    trigger (Alloca τ) ⪯ trigger (Alloca τ)
      [{ (a, a0),
          ∃ l_t l_s,
            ⌜a = DVALUE_Addr (l_t, 0%Z)⌝ ∗ ⌜a0 = DVALUE_Addr (l_s, 0%Z)⌝ ∗
            ⌜l_t ∉ S_t⌝ ∗ ⌜l_s ∉ S_s⌝ ∗
            l_t ↦t [ make_empty_logical_block τ ] ∗
            l_s ↦s [ make_empty_logical_block τ ] ∗
            alloca_tgt i_t ({[l_t]} ∪ S_t) ∗
            alloca_src i_s ({[l_s]} ∪ S_s) ∗
            stack_tgt i_t ∗
            stack_src i_s ∗
            target_block_size l_t (Some (N.to_nat (sizeof_dtyp τ))) ∗
            source_block_size l_s (Some (N.to_nat (sizeof_dtyp τ)))}].
  Proof.
    iIntros "Hl_t Hl_s Hf_t Hf_s".
    iApply target_red_sim_expr.
    iApply (target_red_alloca with "Hl_t Hf_t"); [ done | ].
    iIntros (??) "Hl_t Ha_t Hf_t Hb_t".
    iApply target_red_base.

    iApply source_red_sim_expr.
    iApply (source_red_alloca with "Hl_s Hf_s"); [ done | ].
    iIntros (??) "Hl_s Ha_s Hf_s Hb_s".
    iApply source_red_base.

    iApply sim_expr_base. iExists _,_; iFrame.
    repeat (iSplitL ""; [ done | ]).
    repeat iExists _; iFrame. done.
  Qed.

  Lemma read_logical_view m ptr n b o τ:
    (⊙ m) !! ptr.1 = Some (LBlock n b o) ->
    read m ptr τ = inr (read_in_mem_block b (snd ptr) τ).
  Proof.
    intros Hs.
    apply get_logical_block_logical_view in Hs.
    rewrite /read. setoid_rewrite Hs. reflexivity.
  Qed.

  Lemma source_red_load1 ptr τ Ψ q n b o:
    ptr.1 ↦{q}s [ LBlock n b o ] -∗
    (ptr.1 ↦{q}s [ LBlock n b o ] -∗
      source_red (η := vir_handler) (Ret (read_in_mem_block b (snd ptr) τ)) Ψ) -∗
    source_red (η := vir_handler) (trigger (Load τ (DVALUE_Addr ptr))) Ψ.
  Proof.
    rewrite {2} source_red_eq !source_red_def_unfold /source_red_rec.
    iIntros "Hs Hl". iLeft.
    iIntros (σ_t σ_s) "SI".
    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & SI)".

    iPoseProof (heap_read_st_1 with "Hh_s Hs") as "%lookup".
    cbn in *.
    eapply read_logical_view in lookup.

    iModIntro.
    iExists _,_,_,σ_s. iFrame. (* Long processing time *)
    iSpecialize ("Hl" with "Hs").
    iSplitL "".
    { unfold interp_L2. rewrite interp_state_vis.
      cbn.
      rewrite
        /resum /ReSum_inr /cat /Cat_IFun /inr_ /Inr_sum1 /add_tau /case_; cbn.
      rewrite lookup.
      rewrite bind_ret_l.
      iPureIntro.
      rewrite !bind_tau.
      apply eqit_Tau. cbn. rewrite !bind_ret_l.
      rewrite <- interp_state_tau. cbn.
      rewrite update_mem_id.
      reflexivity. }
    pose proof (source_red_tau (η := vir_handler) Ψ).
    rewrite source_red_eq in H.
    iSplitR "Hl"; [ | iApply H; by rewrite source_red_eq].
    repeat iExists _; iFrame. Unshelve. exact τ.
  Qed.

  Lemma target_red_load1 ptr τ Ψ q n b o:
    ptr.1 ↦{q}t [ LBlock n b o ] -∗
    (ptr.1 ↦{q}t [ LBlock n b o ] -∗
      target_red (η := vir_handler) (Ret (read_in_mem_block b (snd ptr) τ)) Ψ) -∗
    target_red (η := vir_handler) (trigger (Load τ (DVALUE_Addr ptr))) Ψ.
  Proof.
    rewrite {2} target_red_eq !target_red_def_unfold /target_red_rec.
    iIntros "Ht Hl". iLeft.
    iIntros (σ_t σ_s) "SI".
    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & SI)".

    iPoseProof (heap_read_st_1 with "Hh_t Ht") as "%lookup".
    cbn in *.
    eapply read_logical_view in lookup.

    iModIntro. iExists _,_,_,σ_t. iFrame.
    iSpecialize ("Hl" with "Ht").
    iSplitL "".
    { unfold interp_L2. rewrite interp_state_vis.
      cbn.
      rewrite
        /resum /ReSum_inr /cat /Cat_IFun /inr_ /Inr_sum1 /add_tau /case_; cbn.
      rewrite lookup.
      rewrite bind_ret_l.
      iPureIntro.
      rewrite !bind_tau.
      apply eqit_Tau. cbn. rewrite !bind_ret_l.
      rewrite <- interp_state_tau. cbn.
      rewrite update_mem_id.
      reflexivity. }
    pose proof (target_red_tau (η := vir_handler) Ψ).
    rewrite target_red_eq in H.
    iSplitR "Hl"; [ | iApply H; by rewrite target_red_eq].
    repeat iExists _; iFrame. Unshelve. exact τ.
  Qed.

  Corollary source_red_load2 ptr τ Ψ q b:
    ptr.1 ↦{q}s [ b ] -∗
    (ptr.1 ↦{q}s [ b ] -∗
      source_red (η := vir_handler)
      (Ret (read_in_mem_block (lb_mem b) (snd ptr) τ)) Ψ) -∗
    source_red (η := vir_handler) (trigger (Load τ (DVALUE_Addr ptr))) Ψ.
  Proof.
    destruct b.
    iApply source_red_load1.
  Qed.

  Corollary target_red_load2 ptr τ Ψ q b:
    ptr.1 ↦{q}t [ b ] -∗
    (ptr.1 ↦{q}t [ b ] -∗
      target_red (η := vir_handler)
      (Ret (read_in_mem_block (lb_mem b) (snd ptr) τ)) Ψ) -∗
    target_red (η := vir_handler) (trigger (Load τ (DVALUE_Addr ptr))) Ψ.
  Proof.
    destruct b.
    iApply target_red_load1.
  Qed.

  Lemma source_red_load l τ v Ψ q :
    is_supported τ ->
    dvalue_has_dtyp v τ  ->
    l ↦{q}s v -∗
    (l ↦{q}s v -∗
      source_red (η := vir_handler) (Ret (dvalue_to_uvalue v)) Ψ) -∗
    source_red (η := vir_handler) (trigger (Load τ (# l))) Ψ.
  Proof.
    rewrite {2} source_red_eq !source_red_def_unfold /source_red_rec.
    iIntros (Hs Hτ) "Hs Hl". iLeft.
    iIntros (σ_t σ_s) "SI".
    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & %WF & SI)".

    iPoseProof (heap_read with "Hh_s Hs") as "%lookup".
    cbn.
    pose proof (read_uvalue_logical_view _ _ _ _ Hs Hτ lookup) as Hread.

    iModIntro. iExists _,_,_,_. iFrame.
    iSpecialize ("Hl" with "Hs").
    iSplitL "".
    { unfold interp_L2. rewrite interp_state_vis.
      cbn.
      rewrite
        /resum /ReSum_inr /cat /Cat_IFun /inr_ /Inr_sum1 /add_tau /case_; cbn.
      rewrite Hread.
      rewrite bind_ret_l.
      iPureIntro.
      rewrite !bind_tau.
      apply eqit_Tau. cbn. rewrite !bind_ret_l.
      rewrite <- interp_state_tau. cbn.
      rewrite update_mem_id.
      reflexivity. }
    pose proof (source_red_tau (η := vir_handler) Ψ).
    rewrite source_red_eq in H.
    iSplitR "Hl"; [ | iApply H; by rewrite source_red_eq].
    repeat iExists _; iFrame. done.
  Qed.

  Lemma target_red_load l τ v Ψ q :
    is_supported τ ->
    dvalue_has_dtyp v τ  ->
    l ↦{q}t v -∗
    (l ↦{q}t v -∗
      target_red (η := vir_handler) (Ret (dvalue_to_uvalue v)) Ψ) -∗
    target_red (η := vir_handler) (trigger (Load τ (# l))) Ψ.
  Proof.
    rewrite {2} target_red_eq !target_red_def_unfold /target_red_rec.
    iIntros (Hs Hτ) "Ht Hl". iLeft.
    iIntros (σ_t σ_s) "SI".
    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & %WF & SI)".

    iPoseProof (heap_read with "Hh_t Ht") as "%lookup".
    cbn.
    pose proof (read_uvalue_logical_view _ _ _  _ Hs Hτ lookup) as Hread.

    iModIntro. iExists _,_,_,_. iFrame.
    iSpecialize ("Hl" with "Ht").
    iSplitL "".
    { unfold interp_L2. rewrite interp_state_vis.
      cbn.
      rewrite
        /resum /ReSum_inr /cat /Cat_IFun /inr_ /Inr_sum1 /add_tau /case_; cbn.
      rewrite Hread.
      rewrite bind_ret_l.
      iPureIntro.
      rewrite !bind_tau.
      apply eqit_Tau. cbn. rewrite !bind_ret_l.
      rewrite <- interp_state_tau. cbn.
      rewrite update_mem_id.
      reflexivity. }
    pose proof (target_red_tau (η := vir_handler) Ψ).
    rewrite target_red_eq in H.
    iSplitR "Hl"; [ | iApply H; by rewrite target_red_eq].
    repeat iExists _; by iFrame.
  Qed.

  Lemma sim_load l_t l_s τ v_t v_s q_t q_s:
    is_supported τ ->
    dvalue_has_dtyp v_t τ  ->
    dvalue_has_dtyp v_s τ  ->
    l_t ↦{q_t}t v_t -∗ l_s ↦{q_s}s v_s -∗
    trigger (Load τ (# l_t)) ⪯ trigger (Load τ (# l_s))
      [{ (uv_t, uv_s),
            ⌜uvalue_to_dvalue uv_t = inr v_t⌝ ∗
            ⌜uvalue_to_dvalue uv_s = inr v_s⌝ ∗
            l_t ↦{q_t}t v_t ∗ l_s ↦{q_s}s v_s }].
  Proof.
    iIntros (Hs Hτ_t Hτ_s) "Hl_t Hl_s".
    iApply target_red_sim_expr.
    iApply (target_red_load _ _ _ _ _ Hs Hτ_t with "Hl_t").
    iIntros "Hl_t".
    iApply target_red_base.

    iApply source_red_sim_expr.
    iApply (source_red_load _ _ _ _ _ Hs Hτ_s with "Hl_s").
    iIntros "Hl_s".
    iApply source_red_base.

    iApply sim_expr_base. iExists _,_; iFrame.
    repeat (iSplitL ""; [ done | ]).
    rewrite !uvalue_to_dvalue_of_dvalue_to_uvalue; done.
  Qed.

  Lemma source_red_store1 v v' n i Ψ ptr:
    ptr.1 ↦s [ LBlock n v i ] -∗
    (ptr.1 ↦s [ LBlock n (add_all_index (serialize_dvalue v') ptr.2 v) i ] -∗
      source_red (η := vir_handler) (Ret tt) Ψ) -∗
    source_red (η := vir_handler) (trigger (Store (DVALUE_Addr ptr) v')) Ψ.
  Proof.
    rewrite {2} source_red_eq !source_red_def_unfold /source_red_rec.
    iIntros "Hs Hl". iLeft.
    iIntros (σ_t σ_s) "SI".
    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & SI)".

    iDestruct (heap_read_st_1 with "Hh_s Hs") as %?; auto.
    iPoseProof (heap_write with "Hh_s Hs") as ">(Hh_s & Hs)".
    cbn. destruct ptr.
    iSpecialize ("Hl" with "Hs").

    iModIntro. iExists _,_,_,_.
    iSplitL "".
    { unfold interp_L2. rewrite interp_state_vis.
      cbn.
      rewrite
        /resum /ReSum_inr /cat /Cat_IFun /inr_ /Inr_sum1 /add_tau /case_; cbn.
      rewrite bind_bind.
      rewrite /lift_pure_err /lift_err. cbn in *.
      apply get_logical_block_logical_view in H. rewrite /write.
      rewrite /vir_heap in H. rewrite /get_logical_block /get_logical_block_mem.
      rewrite H; cbn.
      rewrite bind_ret_l.
      iPureIntro.
      rewrite !bind_tau.
      apply eqit_Tau. cbn. rewrite !bind_ret_l.
      rewrite <- interp_state_tau. cbn. reflexivity. }
    pose proof (source_red_tau (η := vir_handler) Ψ).
    rewrite source_red_eq in H0. iFrame.
    iSplitR "Hl"; [ | iApply H0; by rewrite source_red_eq].
    repeat iExists _; iFrame. cbn.

    rewrite <- vir_heap_add_logical_block. cbn.
    rewrite /dvalue_to_block.
    cbn in *. rewrite /frames; cbn; eauto.
    destruct_HC "Hh_s".

    assert ({[ z ]} ∪ (vmem σ_s).1.2 = (vmem σ_s).1.2).
    { destruct Hbs. cbn in *.
      specialize (H2 z (ltac:(rewrite lookup_insert; eauto))).
      destruct H2. set_solver. }

    destruct (vmem σ_s); destruct f; cbn in *;
    rewrite H1;
    iExists _, _; iFrame; done.
  Qed.

  Lemma source_red_store v v' l Ψ:
    length (serialize_dvalue v) = length (serialize_dvalue v') ->
    l ↦s v -∗
    (l ↦s v' -∗
      source_red (η := vir_handler) (Ret tt) Ψ) -∗
    source_red (η := vir_handler) (trigger (Store (# l) v')) Ψ.
  Proof.
    rewrite {2} source_red_eq !source_red_def_unfold /source_red_rec.
    iIntros (Hlen) "Hs Hl". iLeft.
    iIntros (σ_t σ_s) "SI".
    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & SI)".

    iDestruct (heap_read with "Hh_s Hs") as %?; auto.
    rewrite mapsto_dval_eq /mapsto_dval_def.
    iPoseProof (heap_write with "Hh_s Hs") as ">(Hh_s & Hs)".
    cbn.
    iSpecialize ("Hl" with "Hs").

    iModIntro. iExists _,_,_,_.
    iSplitL "".
    { unfold interp_L2. rewrite interp_state_vis.
      cbn.
      rewrite
        /resum /ReSum_inr /cat /Cat_IFun /inr_ /Inr_sum1 /add_tau /case_; cbn.
      rewrite bind_bind.
      rewrite /lift_pure_err /lift_err.
      rewrite /write.
      cbn in H.
      rewrite get_logical_block_logical_view in H. rewrite H.
      rewrite bind_ret_l.
      iPureIntro.
      rewrite !bind_tau.
      apply eqit_Tau. cbn. rewrite !bind_ret_l.
      rewrite <- interp_state_tau. cbn. reflexivity. }
    pose proof (source_red_tau (η := vir_handler) Ψ).
    rewrite source_red_eq in H0. iFrame.
    iSplitR "Hl"; [ | iApply H0; by rewrite source_red_eq].
    repeat iExists _; iFrame. cbn.

    rewrite <- vir_heap_add_logical_block. cbn.
    rewrite /dvalue_to_block.
    apply Nat2Z.inj_iff in Hlen. do 2 rewrite <- Zlength_correct in Hlen.

    epose proof (@add_all_index_twice _ _ _ _ _ 0 (init_block (N.of_nat (length (serialize_dvalue v)))) Hlen).
    apply leibniz_equiv in H1. rewrite H1.
    rewrite !Zlength_correct in Hlen.
    apply Nat2Z.inj in Hlen. rewrite Hlen.
    rewrite /frames.
    destruct (vmem σ_s) ; cbn in *.

    destruct_HC "Hh_s".

    assert ({[ l ]} ∪ p.2 = p.2).
    { destruct Hbs. cbn in *.
      destruct p. cbn in *.
      specialize (H3 l (ltac:(rewrite lookup_insert; eauto))).
      set_solver. }
    rewrite H2.

    iExists _, _; iFrame; done.
  Qed.

  Lemma target_red_store1 v v' n i Ψ ptr:
    ptr.1 ↦t [ LBlock n v i ] -∗
    (ptr.1 ↦t [ LBlock n (add_all_index (serialize_dvalue v') ptr.2 v) i ] -∗
      target_red (η := vir_handler) (Ret tt) Ψ) -∗
    target_red (η := vir_handler) (trigger (Store (DVALUE_Addr ptr) v')) Ψ.
  Proof.
    rewrite {2} target_red_eq !target_red_def_unfold /target_red_rec.
    iIntros "Ht Hl". iLeft.
    iIntros (σ_t σ_s) "SI".
    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & SI)".

    iDestruct (heap_read_st_1 with "Hh_t Ht") as %?; auto.
    iPoseProof (heap_write with "Hh_t Ht") as ">(Hh_t & Ht)".
    cbn. destruct ptr.
    iSpecialize ("Hl" with "Ht").

    iModIntro. iExists _,_,_,_.
    iSplitL "".
    { unfold interp_L2. rewrite interp_state_vis.
      cbn.
      rewrite
        /resum /ReSum_inr /cat /Cat_IFun /inr_ /Inr_sum1 /add_tau /case_; cbn.
      rewrite bind_bind.
      rewrite /lift_pure_err /lift_err. cbn in *.
      apply get_logical_block_logical_view in H. rewrite /write.
      rewrite /vir_heap in H. rewrite /get_logical_block /get_logical_block_mem.
      rewrite H; cbn.
      rewrite bind_ret_l.
      iPureIntro.
      rewrite !bind_tau.
      apply eqit_Tau. cbn. rewrite !bind_ret_l.
      rewrite <- interp_state_tau. cbn. reflexivity. }
    pose proof (target_red_tau (η := vir_handler) Ψ).
    rewrite target_red_eq in H0. iFrame.
    iSplitR "Hl"; [ | iApply H0; by rewrite target_red_eq].
    repeat iExists _; iFrame. cbn.

    rewrite <- vir_heap_add_logical_block. cbn.
    rewrite /dvalue_to_block.

    destruct (vmem σ_t); cbn in *.

    rewrite /frames; cbn.

    destruct_HC "Hh_t".

    assert ({[ z ]} ∪ p.2 = p.2).
    { destruct Hbs. cbn in *.
      destruct p. cbn in *.
      specialize (H2 z (ltac:(rewrite lookup_insert; eauto))).
      set_solver. }
    rewrite H1.

    iExists _, _; iFrame; done.
  Qed.

  Lemma target_red_store v v' l Ψ:
    length (serialize_dvalue v) = length (serialize_dvalue v') ->
    l ↦t v -∗
    (l ↦t v' -∗
        target_red (η := vir_handler) (Ret tt) Ψ) -∗
    target_red (η := vir_handler) (trigger (Store (# l) v')) Ψ.
  Proof.
    rewrite {2} target_red_eq !target_red_def_unfold /target_red_rec.
    iIntros (Hlen) "Ht Hl". iLeft.
    iIntros (σ_t σ_s) "SI".
    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & SI)".

    iDestruct (heap_read with "Hh_t Ht") as %?; auto.
    rewrite mapsto_dval_eq /mapsto_dval_def.
    iPoseProof (heap_write with "Hh_t Ht") as ">(Hh_t & Ht)".
    cbn.
    iSpecialize ("Hl" with "Ht").

    iModIntro. iExists _,_,_,_.
    iSplitL "".
    { unfold interp_L2. rewrite interp_state_vis.
      cbn.
      rewrite
        /resum /ReSum_inr /cat /Cat_IFun /inr_ /Inr_sum1 /add_tau /case_; cbn.
      rewrite bind_bind.
      rewrite /lift_pure_err /lift_err.
      rewrite /write.
      cbn in H.
      rewrite get_logical_block_logical_view in H; rewrite H.
      rewrite bind_ret_l.
      iPureIntro.
      rewrite !bind_tau.
      apply eqit_Tau. cbn. rewrite !bind_ret_l.
      rewrite <- interp_state_tau. cbn. reflexivity. }
    pose proof (target_red_tau (η := vir_handler) Ψ).
    rewrite target_red_eq in H0. iFrame.
    iSplitR "Hl"; [ | iApply H0; by rewrite target_red_eq].
    repeat iExists _; iFrame. cbn.

    rewrite <- vir_heap_add_logical_block. cbn.
    rewrite /dvalue_to_block.
    apply Nat2Z.inj_iff in Hlen. do 2 rewrite <- Zlength_correct in Hlen.

    epose proof (@add_all_index_twice _ _ _ _ _ 0 (init_block (N.of_nat (length (serialize_dvalue v)))) Hlen).
    apply leibniz_equiv in H1. rewrite H1.
    rewrite !Zlength_correct in Hlen.
    apply Nat2Z.inj in Hlen. rewrite Hlen.
    rewrite /frames.
    destruct (vmem σ_t); cbn in *.

    destruct_HC "Hh_t".

    assert ({[ l ]} ∪ p.2 = p.2).
    { destruct Hbs. cbn in *.
      destruct p. cbn in *.
      specialize (H3 l (ltac:(rewrite lookup_insert; eauto))).
      set_solver. }
    rewrite H2.

    iExists _, _; iFrame; done.
  Qed.

  Definition update_mem (b : logical_block) (f : mem_block -> mem_block) : logical_block :=
    match b with
      | LBlock n m i => LBlock n (f m) i
    end.

  Corollary source_red_store2 b v' Ψ ptr:
    ptr.1 ↦s [ b ] -∗
    (ptr.1 ↦s [ update_mem b
                  (fun v => add_all_index (serialize_dvalue v') ptr.2 v) ] -∗
      source_red (η := vir_handler) (Ret tt) Ψ) -∗
    source_red (η := vir_handler) (trigger (Store (DVALUE_Addr ptr) v')) Ψ.
  Proof.
    destruct b.
    iApply source_red_store1.
  Qed.

  Corollary target_red_store2 b v' Ψ ptr:
    ptr.1 ↦t [ b ] -∗
    (ptr.1 ↦t [ update_mem b
                  (fun v => add_all_index (serialize_dvalue v') ptr.2 v) ] -∗
      target_red (η := vir_handler) (Ret tt) Ψ) -∗
    target_red (η := vir_handler) (trigger (Store (DVALUE_Addr ptr) v')) Ψ.
  Proof.
    destruct b.
    iApply target_red_store1.
  Qed.

  Lemma sim_store v_t v_s v_t' v_s' l_t l_s:
    length (serialize_dvalue v_t) = length (serialize_dvalue v_t') ->
    length (serialize_dvalue v_s) = length (serialize_dvalue v_s') ->
    l_t ↦t v_t -∗ l_s ↦s v_s -∗
      trigger (Store (# l_t) v_t') ⪯ trigger (Store (# l_s) v_s')
      [{ (v_t, v_s), l_t ↦t v_t' ∗ l_s ↦s v_s' }].
  Proof.
    iIntros (Hlen_t Hlen_s) "Hl_t Hl_s".
    iApply target_red_sim_expr.
    iApply (target_red_store _ _ _ _ Hlen_t with "Hl_t").
    iIntros "Hl_t".
    iApply target_red_base.

    iApply source_red_sim_expr.
    iApply (source_red_store _ _ _ _ Hlen_s with "Hl_s").
    iIntros "Hl_s".
    iApply source_red_base.

    iApply sim_expr_base. iExists _,_; iFrame.
    by repeat (iSplitL ""; [ done | ]).
  Qed.

  Lemma target_local_read (x : LLVMAst.raw_id) (v : uvalue) i Ψ:
    ⊢ [x := v]t i -∗
      stack_tgt i -∗
      ([x := v]t i -∗
        stack_tgt i -∗
        target_red (η := vir_handler) (Ret v) Ψ) -∗
      target_red (η := vir_handler) (trigger (LocalRead x)) Ψ.
  Proof.
    setoid_rewrite target_red_unfold at 2.
    iIntros "Hl Hf H".
    iLeft.
    iIntros (σ_t σ_s) "SI".
    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & SI)".

    iDestruct (lheap_lookup with "Hh_t Hf Hl") as %Ht.
    rewrite -alist_find_to_map_Some in Ht.

    iExists _, v, (fun x => Tau(Ret x)), σ_t.

    destruct (vlocal σ_t) eqn : Hσ_t.
    iSplitL "".
    { unfold interp_L2. rewrite interp_state_vis.
      rewrite
        /resum /ReSum_inr /cat /Cat_IFun /inr_ /Inr_sum1
          /add_tau /case_; cbn.
      rewrite /add_tau. cbn. rewrite Hσ_t.
      rewrite bind_bind.
      iPureIntro. cbn. rewrite Ht. rewrite !bind_ret_l. rewrite bind_tau.
      setoid_rewrite interp_state_ret. rewrite bind_ret_l; cbn.
      rewrite bind_tau.
      rewrite !bind_ret_l; cbn.
      rewrite interp_state_tau interp_state_ret.
      repeat f_equiv; cbn. rewrite -Hσ_t. rewrite update_local_id.
      reflexivity. }

    iSpecialize ("H" with "Hl Hf"); iFrame.
    iSplitR "H"; cycle 1.
    { by iApply target_red_tau. }

    repeat iExists _; rewrite Hσ_t. by iFrame.
  Qed.

  Lemma source_local_read (x : LLVMAst.raw_id) (v : uvalue) i Ψ:
    ⊢ [x := v]s i -∗
      stack_src i -∗
      ([x := v]s i -∗
        stack_src i -∗
        source_red (η := vir_handler) (Ret v) Ψ) -∗
      source_red (η := vir_handler) (trigger (LocalRead x)) Ψ.
  Proof.
    setoid_rewrite source_red_unfold at 2.
    iIntros "Hl Hf H".
    iLeft.
    iIntros (σ_t σ_s) "SI".

    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & SI)".

    iDestruct (lheap_lookup with "Hh_s Hf Hl") as %Ht.
    rewrite -alist_find_to_map_Some in Ht.

    iExists _, v, (fun x => Tau(Ret x)), _.

    destruct (vlocal σ_s) eqn: Hσ_s.
    iSplitL "".
    { unfold interp_L2. rewrite interp_state_vis.
      cbn.
      rewrite
        /resum /ReSum_inr /cat /Cat_IFun /inr_ /Inr_sum1
          /add_tau /case_; cbn.
      rewrite Hσ_s. rewrite bind_bind.
      iPureIntro. cbn. rewrite Ht. rewrite !bind_ret_l. rewrite bind_tau.
      setoid_rewrite interp_state_ret. rewrite bind_ret_l; cbn.
      rewrite bind_tau.
      rewrite !bind_ret_l; cbn.
      rewrite interp_state_tau interp_state_ret.
      rewrite -Hσ_s update_local_id.
      reflexivity. }

    iSpecialize ("H" with "Hl Hf"); iFrame.
    iSplitR "H"; cycle 1.
    { by iApply source_red_tau. }

    repeat iExists _; rewrite Hσ_s; by iFrame.
  Qed.

  Lemma sim_local_read (x_t x_s : LLVMAst.raw_id) (v_t v_s : uvalue) i_t i_s:
    ⊢ [ x_t := v_t ]t i_t -∗
      [ x_s := v_s ]s i_s -∗
      stack_tgt i_t -∗ stack_src i_s -∗
    trigger (LocalRead x_t) ⪯ trigger (LocalRead x_s)
      [{ (v_t', v_s'),
        ⌜v_t = v_t'⌝ ∗ ⌜v_s = v_s'⌝
         ∗ [ x_t := v_t ]t i_t ∗ [ x_s := v_s ]s i_s
         ∗ stack_tgt i_t ∗ stack_src i_s }].
  Proof.
    rewrite sim_expr_unfold.

    iIntros "Ht Hs Hf_t Hf_s %σ_t %σ_s SI".
    rewrite /interp_L2;
    provide_case: TAU_STEP.
    (iSplitL ""; [ iPureIntro | ]).
    { apply Eq.EqAxiom.bisimulation_is_eq.
      rewrite -itree_eta.
      rewrite interp_state_vis; cbn.
      setoid_rewrite interp_state_ret.
      setoid_rewrite bind_tau; cbn.
      rewrite bind_bind.
      cbn; reflexivity. }
    (iSplitL ""; [ iPureIntro | ]).
    { apply Eq.EqAxiom.bisimulation_is_eq.
      rewrite -itree_eta.
      rewrite interp_state_vis; cbn.
      setoid_rewrite interp_state_ret.
      setoid_rewrite bind_tau; cbn.
      rewrite bind_bind.
      cbn; reflexivity. }

    (* destruct p, p1; cbn. *)
    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij &  SI)".
    iDestruct (lheap_lookup with "Hh_t Hf_t Ht") as %Ht.
    iDestruct (lheap_lookup with "Hh_s Hf_s Hs") as %Hs.
    rewrite -alist_find_to_map_Some in Ht.
    rewrite -alist_find_to_map_Some in Hs.
    destruct (vlocal σ_t) eqn: Hσ_t, (vlocal σ_s) eqn: Hσ_s.
    cbn; rewrite Ht Hs. cbn.
    iApply sim_coindF_tau; cbn; iApply sim_coindF_base.

    rewrite /lift_expr_rel.
    repeat iExists _.
    do 2 (iSplitL ""; [ iPureIntro; reflexivity | ]); iFrame.
    iSplitR ""; [ | repeat iExists _; done].
    repeat iExists _; by iFrame.
  Qed.

  Lemma sim_local_read_not_in_domain {R} (x_s : LLVMAst.raw_id) L_s Φ (e_t : _ R) i:
    x_s ∉ L_s ->
    ⊢ ldomain_src i L_s -∗
      stack_src i -∗
      e_t ⪯ trigger (LocalRead x_s) [{ Φ }].
  Proof.
    rewrite sim_expr_unfold.

    iIntros (He) "Hd Hf %σ_t %σ_s SI".
    rewrite /interp_L2;
    provide_case: STUTTER_R.
    (iSplitL ""; [ iPureIntro | ]).
    { apply Eq.EqAxiom.bisimulation_is_eq. cbn; reflexivity. }
    cbn. rewrite /handle_local_stack; cbn.

    iDestruct "SI" as (???)
      "(Hh_s & Hh_t & H_c & Hbij & SI)".

    destruct_HC "Hh_s".
    iDestruct (ghost_var_agree with "Hf HCF") as %Hf; subst.
    iDestruct (ghost_var_agree with "Hd HD") as %Hag_s; subst.
    apply alist_find_dom_None' in He.
    destruct (vlocal σ_s) in *; cbn.
    rewrite He; cbn.

    rewrite sim_indF_unfold /sim_expr_inner.
    provide_case: SOURCE_EXC.
    iPureIntro.
    apply Eq.EqAxiom.bisimulation_is_eq; cbn.
    eapply eqit_Vis; intros. inversion u.
    Unshelve.
    intros; inversion H.
  Qed.

  (* Ghost resource doesn't check that it gets assigned only once. It must be a
    well-formed LLVM IR program. *)
  Lemma sim_local_write (x_t x_s : LLVMAst.raw_id) (v_t v_s : uvalue) v_t' v_s' i_t i_s:
    ⊢ stack_tgt i_t -∗ stack_src i_s -∗
      [ x_t := v_t ]t i_t -∗ [ x_s := v_s ]s i_s -∗
    trigger (LocalWrite x_t v_t') ⪯ trigger (LocalWrite x_s v_s')
      [{ (v_t, v_s),
          [ x_t := v_t' ]t i_t ∗ [ x_s := v_s' ]s i_s ∗
          stack_tgt i_t ∗ stack_src i_s}].
  Proof.
    rewrite sim_expr_unfold.

    iIntros "Hf_t Hf_s Ht Hs %σ_t %σ_s SI".
    rewrite /interp_L2;
    provide_case: TAU_STEP.
    (iSplitL ""; [ iPureIntro | ]).
    { apply Eq.EqAxiom.bisimulation_is_eq. cbn; reflexivity. }
    (iSplitL ""; [ iPureIntro | ]).
    { apply Eq.EqAxiom.bisimulation_is_eq. cbn; reflexivity. }

    destruct (vlocal σ_t) eqn: Hlocal_t; destruct (vlocal σ_s) eqn: Hlocal_s.
    rewrite sim_coindF_unfold sim_indF_unfold /sim_expr_inner.

    cbn.
    provide_case: TAU_STEP. cbn.
    iDestruct "SI" as (???) "(Hh_s&Hh_t&HC&Hbij&Hg)".
    rewrite sim_coindF_unfold sim_indF_unfold /sim_expr_inner.

    iMod (lheap_write with "Hh_t Hf_t Ht") as "(Hh_t & Hf_t & Ht)".
    iMod (lheap_write with "Hh_s Hf_s Hs") as "(Hh_s & Hf_s & Hs)".
    provide_case:BASE.

    rewrite /lift_expr_rel; cbn; iFrame.
    iSplitR ""; cycle 1.
    { repeat iExists _; done. }
    iExists C, S, G; iFrame. rewrite Hlocal_t Hlocal_s; iFrame.
  Qed.

  (* TODO: Term [alloc] is misleading; rename *)
  Lemma target_local_write_alloc
    (x : LLVMAst.raw_id) (v : uvalue) L i Φ :
    x ∉ L ->
    ⊢ ldomain_tgt i L -∗
      stack_tgt i -∗
      ([ x := v ]t i -∗
        ldomain_tgt i ({[x]} ∪ L) -∗
          stack_tgt i -∗
          target_red (η := vir_handler) (Ret tt) Φ) -∗
      target_red (η := vir_handler) (trigger (LocalWrite x v)) Φ.
  Proof.
    setoid_rewrite target_red_unfold at 2.
    iIntros (Hlen) "Hd Hf Hl".
    iLeft.
    iIntros (σ_t σ_s) "SI".

    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & SI)".
    destruct (vlocal σ_t) eqn: Hlocal_t.

    iExists _,
      (update_local (alist_add x v l, l0) σ_t),
      (fun x => Tau (Ret tt)),_.

    iSplitL "".
    { unfold interp_L2. rewrite interp_state_vis.
      cbn.
      rewrite
        /resum /ReSum_inr /cat /Cat_IFun /inr_ /Inr_sum1 /add_tau /case_; cbn.
      rewrite Hlocal_t.
      rewrite bind_bind. rewrite !bind_ret_l.
      iPureIntro.
      setoid_rewrite interp_state_ret. rewrite !bind_tau.
      rewrite !bind_ret_l.
      apply eqit_Tau. cbn.
      rewrite interp_state_tau interp_state_ret.
      reflexivity. }

    (* Ned to go back to repair *)
    iMod ((lheap_domain_alloc _ _ v)
           with "Hd Hf Hh_t") as "(Hh_t & Hp_t & Hf_t & Hd_t)"; [done | ].

    iDestruct (lheap_lookup with "Hh_t Hf_t Hp_t") as %Hl_t.
    cbn. iFrame.

    iSpecialize ("Hl" with "Hp_t Hd_t Hf_t"); iFrame.
    iSplitR "Hl"; cycle 1.
    { by iApply target_red_tau. }

    repeat iExists _; by iFrame.
  Qed.

  Lemma source_local_write_alloc
    (x : LLVMAst.raw_id) (v : uvalue) L i Φ :
    x ∉ L ->
    ⊢ ldomain_src i L -∗
      stack_src i -∗
      ([ x := v ]s i -∗
        ldomain_src i ({[x]} ∪ L) -∗
          stack_src i -∗
          source_red (η := vir_handler) (Ret tt) Φ) -∗
      source_red (η := vir_handler) (trigger (LocalWrite x v)) Φ.
  Proof.
    setoid_rewrite source_red_unfold at 2.
    iIntros (Hlen) "Hd Hf Hl".
    iLeft.
    iIntros (σ_t σ_s) "SI".

    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & SI)".
    destruct (vlocal σ_s) eqn: Hlocal_s.

    iExists _,
      (update_local (alist_add x v l, l0) σ_s),
      (fun x => Tau (Ret tt)),_.

    iSplitL "".
    { unfold interp_L2. rewrite interp_state_vis.
      cbn.
      rewrite
        /resum /ReSum_inr /cat /Cat_IFun /inr_ /Inr_sum1 /add_tau /case_; cbn.
      rewrite Hlocal_s.
      rewrite bind_bind. rewrite !bind_ret_l.
      iPureIntro.
      setoid_rewrite interp_state_ret. rewrite !bind_tau.
      rewrite !bind_ret_l.
      apply eqit_Tau. cbn.
      rewrite interp_state_tau interp_state_ret.
      reflexivity. }

    iMod ((lheap_domain_alloc _ _ v)
           with "Hd Hf Hh_s") as "(Hh_s & Hp_s & Hf_s & Hd_s)"; [done | ].

    iDestruct (lheap_lookup with "Hh_s Hf_s Hp_s") as %Hl_s.
    cbn. iFrame.

    iSpecialize ("Hl" with "Hp_s Hd_s Hf_s"); iFrame.
    iSplitR "Hl"; cycle 1.
    { by iApply source_red_tau. }

    repeat iExists _; by iFrame.
  Qed.

  Lemma sim_local_write_alloc
    (x_t x_s : LLVMAst.raw_id) (v_t v_s : uvalue) L_t L_s i_t i_s:
    x_t ∉ L_t ->
    x_s ∉ L_s ->
    ⊢ ldomain_tgt i_t L_t -∗ ldomain_src i_s L_s -∗
      stack_tgt i_t -∗ stack_src i_s -∗
    trigger (LocalWrite x_t v_t) ⪯ trigger (LocalWrite x_s v_s)
      [{ (v1, v2),
          [ x_t := v_t ]t i_t ∗ [ x_s := v_s ]s i_s ∗
          ldomain_tgt i_t ({[x_t]} ∪ L_t) ∗ ldomain_src i_s ({[x_s]} ∪ L_s)
          ∗ stack_tgt i_t ∗ stack_src i_s }].
  Proof.
    rewrite sim_expr_unfold.

    iIntros (Ht Hs) "Ht Hs Hf_t Hf_s %σ_t %σ_s SI".
    cbn. destruct (vlocal σ_t), (vlocal σ_s).

    rewrite /interp_L2;
    provide_case: TAU_STEP.

    rewrite sim_coindF_unfold sim_indF_unfold /sim_expr_inner.

    provide_case: TAU_STEP. cbn.
    do 2 (iSplitL ""; [ done | ]).

    iDestruct "SI" as (???) "(Hh_s&Hh_t&HC&Hbij&Hg)".
    cbn.
    rewrite sim_coindF_unfold sim_indF_unfold /sim_expr_inner.

    iMod ((lheap_domain_alloc _ _ v_t) with "Ht Hf_t Hh_t") as "(Hh_t & Hp_t & Hf_t & Hd_t)"; [done | ].
    iMod ((lheap_domain_alloc _ _ v_s) with "Hs Hf_s Hh_s") as "(Hh_s & Hp_s & Hf_s & Hd_s)"; [done | ].

    iDestruct (lheap_lookup with "Hh_t Hf_t Hp_t") as %Hl_t.
    iDestruct (lheap_lookup with "Hh_s Hf_s Hp_s") as %Hl_s.
    cbn.
    provide_case: BASE; iFrame.
    iSplitR ""; [ cbn; rewrite /state_interp; repeat iExists _; iFrame | ].

    repeat iExists _; by iFrame.
  Qed.

  Lemma target_local_write
    (x : LLVMAst.raw_id) (v v' : uvalue) L i Φ :
    ⊢ [ x := v' ]t i -∗
      ldomain_tgt i L -∗
      stack_tgt i -∗
      ([ x := v ]t i -∗
        ldomain_tgt i L -∗
          stack_tgt i -∗
          target_red (η := vir_handler) (Ret tt) Φ) -∗
      target_red (η := vir_handler) (trigger (LocalWrite x v)) Φ.
  Proof.
    setoid_rewrite target_red_unfold at 2.
    iIntros "Hx Hd Hf Hl".
    iLeft; iIntros (σ_t σ_s) "SI".

    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & SI)".
    destruct (vlocal σ_t) eqn: Hlocal_t.

    iExists _,
      (update_local (alist_add x v l, l0) σ_t),
      (fun x => Tau (Ret tt)),_.

    iSplitL "".
    { unfold interp_L2. rewrite interp_state_vis.
      cbn.
      rewrite
        /resum /ReSum_inr /cat /Cat_IFun /inr_ /Inr_sum1 /add_tau /case_; cbn.
      rewrite Hlocal_t.
      rewrite bind_bind. rewrite !bind_ret_l.
      iPureIntro.
      setoid_rewrite interp_state_ret. rewrite !bind_tau.
      rewrite !bind_ret_l.
      apply eqit_Tau. cbn.
      rewrite interp_state_tau interp_state_ret.
      reflexivity. }

    iMod ((lheap_write _ _ _ v) with "Hh_t Hf Hx") as "(Hh_t & Hf & Hx)".

    iDestruct (lheap_lookup with "Hh_t Hf Hx") as %Hl_t.
    cbn.

    iSpecialize ("Hl" with "Hx Hd Hf"); iFrame.
    iSplitR "Hl"; cycle 1.
    { by iApply target_red_tau. }

    repeat iExists _; by iFrame.
  Qed.

  Lemma source_local_write
    (x : LLVMAst.raw_id) (v v' : uvalue) L i Φ :
    ⊢ [ x := v' ]s i -∗
      ldomain_src i L -∗
      stack_src i -∗
      ([ x := v ]s i -∗
        ldomain_src i L -∗
          stack_src i -∗
          source_red (η := vir_handler) (Ret tt) Φ) -∗
      source_red (η := vir_handler) (trigger (LocalWrite x v)) Φ.
  Proof.
    setoid_rewrite source_red_unfold at 2.
    iIntros "Hx Hd Hf Hl".
    iLeft.
    iIntros (σ_t σ_s) "SI".

    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & SI)".
    destruct (vlocal σ_s) eqn: Hlocal_s.

    iExists _,
      (update_local (alist_add x v l, l0) σ_s),
      (fun x => Tau (Ret tt)),_.

    iSplitL "".
    { unfold interp_L2. rewrite interp_state_vis.
      cbn.
      rewrite
        /resum /ReSum_inr /cat /Cat_IFun /inr_ /Inr_sum1 /add_tau /case_; cbn.
      rewrite Hlocal_s.
      rewrite bind_bind. rewrite !bind_ret_l.
      iPureIntro.
      setoid_rewrite interp_state_ret. rewrite !bind_tau.
      rewrite !bind_ret_l.
      apply eqit_Tau. cbn.
      rewrite interp_state_tau interp_state_ret.
      reflexivity. }

    iMod ((lheap_write _ _ _ v) with "Hh_s Hf Hx") as "(Hh_s & Hf & Hx)".

    iDestruct (lheap_lookup with "Hh_s Hf Hx") as %Hl_s.
    cbn.

    iSpecialize ("Hl" with "Hx Hd Hf"); iFrame.
    iSplitR "Hl"; cycle 1.
    { by iApply source_red_tau. }

    repeat iExists _; by iFrame.
  Qed.

End proof.

