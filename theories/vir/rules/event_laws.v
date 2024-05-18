(* ======================================================================== *)
(* Primitive laws on instruction-related events. *)
(* ======================================================================== *)

From iris.prelude Require Import options.

From velliris.program_logic Require Import program_logic.
From velliris.vir.lang Require Export lang.

Set Default Proof Using "Type*".

(* ------------------------------------------------------------------------ *)
(* Utility  *)
(* ------------------------------------------------------------------------ *)

Lemma read_logical_view m ptr n b o τ:
  (⊙ m) !! ptr.1 = Some (LBlock n b o) ->
  read m ptr τ = inr (read_in_mem_block b (snd ptr) τ).
Proof.
  intros Hs.
  apply get_logical_block_logical_view in Hs.
  rewrite /read. setoid_rewrite Hs. reflexivity.
Qed.

Definition update_block (b : logical_block) (f : mem_block -> mem_block) : logical_block :=
  match b with
    | LBlock n m i => LBlock n (f m) i
  end.

(* ------------------------------------------------------------------------ *)
Section primitive_rules.

  Context {Σ} `{!vellirisGS Σ}.

  Local Ltac final := src_final; tgt_final; done.

  (* ------------------------------------------------------------------------ *)
  (* Source-side primitive laws on instruction-related events *)
  (* ------------------------------------------------------------------------ *)

  Lemma source_alloca τ `{non_void τ} Ψ S_s i:
    alloca_src i S_s -∗
    stack_src i -∗
    (∀ z,
        ⌜z ∉ S_s⌝ -∗
        z ↦s [ make_empty_logical_block τ ] -∗
        alloca_src i ({[ z ]} ∪ S_s) -∗
        stack_src i -∗
        source_block_size z (Some (N.to_nat (sizeof_dtyp τ))) -∗
        Ψ (Ret (DVALUE_Addr (z, 0))%Z)) -∗
    source_red (η := vir_handler) (trigger (Alloca τ)) Ψ.
  Proof.
    rewrite source_red_unfold.
    iIntros "Hal Hf Hl". iLeft. iIntros (σ_t σ_s) "SI".

    destruct (allocate (vmem σ_s) τ) eqn: Ht.
    { exfalso; eapply non_void_allocate_abs; eauto. }
    destruct p.

    (* Allocation is successful on source and source logical views *)
    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & SI)".

    iCombine "Hal Hf Hh_s" as "Hs".
    iMod (heap_allocate_1 with "Hs") as "(Hh_s & %Hdom & Hal & Hf & Hl_s' & Hbs)"; eauto.
    destruct a; cbn.

    iSpecialize ("Hl" $! _ Hdom with "Hl_s' Hal Hf Hbs").

    iModIntro.
    iExists dvalue, (DVALUE_Addr (z, z0)),(fun x => Tau (Ret x)),
      (update_mem m σ_s).
    iSplitL "".
    { iPureIntro; solve_eq. rewrite Ht. by solve_eq. }

    iFrame; apply allocate_inv in Ht.
    destruct Ht as (?&?&?). inv H0; inv H1.

    iSplitR "Hl"; last final.
    iExists C, S, G; iFrame.

    rewrite -!vir_logical_frame_add_to_frame.
    cbn in *. unfold frames; cbn.
    destruct (vmem σ_s); cbn in *.
    destruct f; cbn -[frame_at]; iFrame.
  Qed.

  Lemma source_load_block ptr τ Ψ q n b o:
    ptr.1 ↦{q}s [ LBlock n b o ] -∗
    (ptr.1 ↦{q}s [ LBlock n b o ] -∗
      Ψ (Ret (read_in_mem_block b (snd ptr) τ))) -∗
    source_red (η := vir_handler) (trigger (Load τ (DVALUE_Addr ptr))) Ψ.
  Proof.
    rewrite source_red_unfold.
    iIntros "Hs Hl". iLeft.
    iIntros (σ_t σ_s) "SI".
    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & SI)".

    iPoseProof (heap_read_st_1 with "Hh_s Hs") as "%lookup".
    cbn in *; eapply (read_logical_view _ _ _ _ _ τ) in lookup.

    iModIntro.
    iExists _,
      (read_in_mem_block b (snd ptr) τ),
      (fun x => Tau (Ret x)),σ_s. iFrame. (* Long processing time *)
    iSpecialize ("Hl" with "Hs").
    iSplitL ""; first iPureIntro.
    { solve_eq. rewrite lookup //=. tau_steps.
      solve_eq. rewrite update_mem_id.
      reflexivity. }
    iSplitR "Hl"; last final; sfinal.
  Qed.

  Corollary source_load_block1 ptr τ Ψ q b:
    ptr.1 ↦{q}s [ b ] -∗
    (ptr.1 ↦{q}s [ b ] -∗
      Ψ (Ret (read_in_mem_block (lb_mem b) (snd ptr) τ))) -∗
    source_red (η := vir_handler) (trigger (Load τ (DVALUE_Addr ptr))) Ψ.
  Proof.
    destruct b; iApply source_load_block.
  Qed.

  Lemma source_load l τ v Ψ q :
    is_supported τ ->
    dvalue_has_dtyp v τ  ->
    l ↦{q}s v -∗
    (l ↦{q}s v -∗ Ψ (Ret (dvalue_to_uvalue v))) -∗
    source_red (η := vir_handler) (trigger (Load τ (# l))) Ψ.
  Proof.
    rewrite source_red_unfold.
    iIntros (Hs Hτ) "Hs Hl". iLeft.
    iIntros (σ_t σ_s) "SI".
    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & %WF & SI)".

    iPoseProof (heap_read with "Hh_s Hs") as "%lookup"; cbn.
    pose proof (read_uvalue_logical_view _ _ _ _ Hs Hτ lookup) as Hread.

    iModIntro;
      iExists _,
      (dvalue_to_uvalue v),
      (fun x => Tau (Ret x)), σ_s. iFrame. (* Long processing time *)
    iSpecialize ("Hl" with "Hs").
    iSplitL ""; first iPureIntro.
    { solve_eq. cbn; rewrite Hread.
      solve_eq. by rewrite update_mem_id. }
    iSplitR "Hl"; last final; sfinal.
  Qed.

  Lemma source_store_block v v' n i Ψ ptr:
    ptr.1 ↦s [ LBlock n v i ] -∗
    (ptr.1 ↦s [ LBlock n (add_all_index (serialize_dvalue v') ptr.2 v) i ] -∗
      Ψ (Ret tt)) -∗
    source_red (η := vir_handler) (trigger (Store (DVALUE_Addr ptr) v')) Ψ.
  Proof.
    rewrite source_red_unfold.
    iIntros "Hs Hl"; iLeft; iIntros (σ_t σ_s) "SI".
    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & SI)".

    iDestruct (heap_read_st_1 with "Hh_s Hs") as %?; auto.
    iPoseProof (heap_write with "Hh_s Hs") as ">(Hh_s & Hs)".
    cbn; destruct ptr; iSpecialize ("Hl" with "Hs").

    iModIntro.
    iExists _,tt,(fun x => Tau(Ret x)),_.
    iSplitL ""; first iPureIntro.
    { solve_eq.
      apply get_logical_block_logical_view in H. rewrite /write.
      rewrite /vir_heap in H. rewrite /get_logical_block /get_logical_block_mem.
      rewrite H; cbn. by solve_eq. }

    iSplitR "Hl"; last final; sfinal.

    cbn; rewrite <- vir_heap_add_logical_block. cbn.
    rewrite /dvalue_to_block.
    cbn in *. rewrite /frames; cbn; eauto.
    destruct_HC "Hh_s".

    assert ({[ z ]} ∪ (vmem σ_s).1.2 = (vmem σ_s).1.2).
    { destruct Hbs. cbn in *.
      specialize (H1 z (ltac:(rewrite lookup_insert; eauto))).
      destruct H1. set_solver. }

    destruct (vmem σ_s); destruct f; cbn in *;
    rewrite H0; sfinal.
  Qed.

  Lemma source_store v v' l Ψ:
    length (serialize_dvalue v) = length (serialize_dvalue v') ->
    l ↦s v -∗
    (l ↦s v' -∗ Ψ (Ret tt)) -∗
    source_red (η := vir_handler) (trigger (Store (# l) v')) Ψ.
  Proof.
    rewrite source_red_unfold.
    iIntros (Hlen) "Hs Hl". iLeft.
    iIntros (σ_t σ_s) "SI".
    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & SI)".

    iDestruct (heap_read with "Hh_s Hs") as %?; auto.
    rewrite mapsto_dval_eq /mapsto_dval_def.
    iPoseProof (heap_write with "Hh_s Hs") as ">(Hh_s & Hs)".
    cbn; iSpecialize ("Hl" with "Hs").

    iModIntro. iExists _,tt,(fun x => Tau (Ret x)),_.
    iSplitL ""; first iPureIntro.
    { solve_eq.
      rewrite /write; rewrite get_logical_block_logical_view in H.
      rewrite H. by solve_eq. }

    iSplitR "Hl"; last final; sfinal.

    cbn; rewrite <- vir_heap_add_logical_block.
    rewrite /dvalue_to_block.
    apply Nat2Z.inj_iff in Hlen. do 2 rewrite <- Zlength_correct in Hlen.

    epose proof (@add_all_index_twice _ _ _ _ _ 0
        (init_block (N.of_nat (length (serialize_dvalue v)))) Hlen).
    apply leibniz_equiv in H0.
    rewrite H0. rewrite !Zlength_correct in Hlen.
    apply Nat2Z.inj in Hlen. rewrite Hlen.
    rewrite /frames; destruct (vmem σ_s) ; cbn in *.

    destruct_HC "Hh_s".

    assert ({[ l ]} ∪ p.2 = p.2).
    { destruct Hbs. cbn in *.
      destruct p. cbn in *.
      specialize (H2 l (ltac:(rewrite lookup_insert; eauto))).
      set_solver. }
    rewrite H1.
    sfinal.
  Qed.

  Corollary source_store_block1 b v' Ψ ptr:
    ptr.1 ↦s [ b ] -∗
    (ptr.1 ↦s [ update_block b
                  (fun v => add_all_index (serialize_dvalue v') ptr.2 v) ] -∗
      Ψ (Ret tt)) -∗
    source_red (η := vir_handler) (trigger (Store (DVALUE_Addr ptr) v')) Ψ.
  Proof.
    destruct b; iApply source_store_block.
  Qed.

  Lemma source_local_read (x : LLVMAst.raw_id) (v : uvalue) i Ψ:
    ⊢ [x := v]s i -∗
      stack_src i -∗
      ([x := v]s i -∗
        stack_src i -∗
        Ψ (Ret v)) -∗
      source_red (η := vir_handler) (trigger (LocalRead x)) Ψ.
  Proof.
    rewrite source_red_unfold.
    iIntros "Hl Hf H"; iLeft; iIntros (σ_t σ_s) "SI".

    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & SI)".

    iDestruct (lheap_lookup with "Hh_s Hf Hl") as %Ht.
    rewrite -alist_find_to_map_Some in Ht.

    iExists _, v, (fun x => Tau(Ret x)), _.

    destruct (vlocal σ_s) eqn: Hσ_s.
    iSplitL ""; first iPureIntro.
    { solve_eq.
      rewrite Hσ_s. cbn. rewrite Ht.
      solve_eq.
      by rewrite -Hσ_s update_local_id. }

    iSpecialize ("H" with "Hl Hf").
    iSplitR "H"; last final.

    repeat iExists _; rewrite Hσ_s; by iFrame.
  Qed.

  Lemma source_local_write_alloc
    (x : LLVMAst.raw_id) (v : uvalue) L i Φ :
    x ∉ L ->
    ⊢ ldomain_src i L -∗
      stack_src i -∗
      ([ x := v ]s i -∗
        ldomain_src i ({[x]} ∪ L) -∗
          stack_src i -∗
          Φ (Ret tt)) -∗
      source_red (η := vir_handler) (trigger (LocalWrite x v)) Φ.
  Proof.
    rewrite source_red_unfold.
    iIntros (Hlen) "Hd Hf Hl"; iLeft; iIntros (σ_t σ_s) "SI".

    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & SI)".
    destruct (vlocal σ_s) eqn: Hlocal_s.

    iExists _,
      (update_local (alist_add x v l, l0) σ_s),
      (fun x => Tau (Ret tt)),_.

    iSplitL ""; first iPureIntro.
    { solve_eq; rewrite Hlocal_s; by solve_eq. }

    iMod ((lheap_domain_alloc _ _ v)
           with "Hd Hf Hh_s") as "(Hh_s & Hp_s & Hf_s & Hd_s)"; [done | ].

    iDestruct (lheap_lookup with "Hh_s Hf_s Hp_s") as %Hl_s; cbn; iFrame.

    iSpecialize ("Hl" with "Hp_s Hd_s Hf_s"); iFrame.
    iSplitR "Hl"; last final; sfinal.
  Qed.

  Lemma source_local_write
    (x : LLVMAst.raw_id) (v v' : uvalue) i Φ :
    ⊢ [ x := v' ]s i -∗
      stack_src i -∗
      ([ x := v ]s i -∗
          stack_src i -∗
          Φ (Ret tt)) -∗
      source_red (η := vir_handler) (trigger (LocalWrite x v)) Φ.
  Proof.
    rewrite source_red_unfold.
    iIntros "Hx Hf Hl"; iLeft; iIntros (σ_t σ_s) "SI".

    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & SI)".
    destruct (vlocal σ_s) eqn: Hlocal_s.

    iExists _,
      (update_local (alist_add x v l, l0) σ_s),
      (fun x => Tau (Ret tt)),_.

    iSplitL ""; first iPureIntro.
    { solve_eq. rewrite Hlocal_s. by solve_eq. }

    iMod ((lheap_write _ _ _ v) with "Hh_s Hf Hx") as "(Hh_s & Hf & Hx)".

    iDestruct (lheap_lookup with "Hh_s Hf Hx") as %Hl_s; cbn.

    iSpecialize ("Hl" with "Hx Hf"); iFrame.
    iSplitR "Hl"; last final; sfinal.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* Target-side primitive laws on instruction-related events *)
  (* ------------------------------------------------------------------------ *)

  Lemma target_alloca τ `{non_void τ} Ψ S_s i:
    alloca_tgt i S_s -∗
    stack_tgt i -∗
    (∀ z,
        ⌜z ∉ S_s⌝ -∗
        z ↦t [ make_empty_logical_block τ ] -∗
        alloca_tgt i ({[ z ]} ∪ S_s) -∗
        stack_tgt i -∗
        target_block_size z (Some (N.to_nat (sizeof_dtyp τ))) -∗
        Ψ (Ret (DVALUE_Addr (z, 0%Z)))) -∗
    target_red (η := vir_handler) (trigger (Alloca τ)) Ψ.
  Proof.
    rewrite target_red_unfold.
    iIntros "Hal Hf Hl". iLeft. iIntros (σ_t σ_s) "SI".

    destruct (allocate (vmem σ_t) τ) eqn: Ht.
    { exfalso; eapply non_void_allocate_abs; eauto. }
    destruct p.

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
    iSplitL ""; iFrame.
    { iPureIntro. solve_eq; rewrite Ht; by solve_eq. }
    iFrame.

    apply allocate_inv in Ht.
    destruct Ht as (?&?&?). inversion H0; subst.
    inversion H1; subst.

    iSplitR "Hl"; last final; cbn.

    iExists C, S, G; iFrame.
    rewrite -!vir_logical_frame_add_to_frame.
    cbn in *. unfold frames; cbn.
    destruct (vmem σ_t); cbn in *.
    destruct f; cbn -[frame_at]; iFrame.
  Qed.

  Lemma target_load_block ptr τ Ψ q n b o:
    ptr.1 ↦{q}t [ LBlock n b o ] -∗
    (ptr.1 ↦{q}t [ LBlock n b o ] -∗
      Ψ (Ret (read_in_mem_block b (snd ptr) τ))) -∗
    target_red (η := vir_handler) (trigger (Load τ (DVALUE_Addr ptr))) Ψ.
  Proof.
    rewrite target_red_unfold.
    iIntros "Ht Hl". iLeft.
    iIntros (σ_t σ_s) "SI".
    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & SI)".

    iPoseProof (heap_read_st_1 with "Hh_t Ht") as "%lookup".
    cbn in *; eapply (read_logical_view _ _ _ _ _ τ) in lookup.

    iModIntro.
    iExists _,
      (read_in_mem_block b (snd ptr) τ),
      (fun x => Tau (Ret x)),σ_t. iFrame. (* Long processing time *)
    iSpecialize ("Hl" with "Ht").
    iSplitL ""; first iPureIntro.
    { solve_eq; rewrite lookup //=. tau_steps.
      solve_eq. rewrite update_mem_id.
      reflexivity. }
    iSplitR "Hl"; last final; sfinal.
  Qed.

  Corollary target_load_block1 ptr τ Ψ q b:
    ptr.1 ↦{q}t [ b ] -∗
    (ptr.1 ↦{q}t [ b ] -∗
      Ψ (Ret (read_in_mem_block (lb_mem b) (snd ptr) τ))) -∗
    target_red (η := vir_handler) (trigger (Load τ (DVALUE_Addr ptr))) Ψ.
  Proof.
    destruct b; iApply target_load_block.
  Qed.

  Lemma target_load l τ v Ψ q :
    is_supported τ ->
    dvalue_has_dtyp v τ  ->
    l ↦{q}t v -∗
    (l ↦{q}t v -∗ Ψ (Ret (dvalue_to_uvalue v))) -∗
    target_red (η := vir_handler) (trigger (Load τ (# l))) Ψ.
  Proof.
    rewrite target_red_unfold.
    iIntros (Hs Hτ) "Ht Hl". iLeft.
    iIntros (σ_t σ_s) "SI".
    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & %WF & SI)".

    iPoseProof (heap_read with "Hh_t Ht") as "%lookup".
    pose proof (read_uvalue_logical_view _ _ _  _ Hs Hτ lookup) as Hread.

    iModIntro.
    iExists _,
      (dvalue_to_uvalue v),
      (fun x => Tau (Ret x)), σ_t. iFrame.
    iSpecialize ("Hl" with "Ht").

    iSplitL ""; first iPureIntro.
    { solve_eq. cbn; rewrite Hread; solve_eq.
      by rewrite update_mem_id. }
    iSplitR "Hl"; last final; sfinal.
  Qed.

  Lemma target_store_block v v' n i Ψ ptr:
    ptr.1 ↦t [ LBlock n v i ] -∗
    (ptr.1 ↦t [ LBlock n (add_all_index (serialize_dvalue v') ptr.2 v) i ] -∗
      Ψ (Ret tt)) -∗
    target_red (η := vir_handler) (trigger (Store (DVALUE_Addr ptr) v')) Ψ.
  Proof.
    rewrite target_red_unfold.
    iIntros "Ht Hl". iLeft.
    iIntros (σ_t σ_s) "SI".
    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & SI)".

    iDestruct (heap_read_st_1 with "Hh_t Ht") as %?; auto.
    iPoseProof (heap_write with "Hh_t Ht") as ">(Hh_t & Ht)".
    cbn. destruct ptr.
    iSpecialize ("Hl" with "Ht").

    iModIntro.
    iExists _,tt,(fun x => Tau(Ret x)),_.
    iSplitL ""; first iPureIntro.
    { solve_eq.
      apply get_logical_block_logical_view in H. rewrite /write.
      rewrite /vir_heap in H. rewrite /get_logical_block /get_logical_block_mem.
      rewrite H; cbn. by solve_eq. }

    iSplitR "Hl"; last final; sfinal.

    cbn; rewrite <- vir_heap_add_logical_block. cbn.
    rewrite /dvalue_to_block.

    destruct (vmem σ_t); cbn in *.

    rewrite /frames; cbn.

    destruct_HC "Hh_t".

    assert ({[ z ]} ∪ p.2 = p.2).
    { destruct Hbs. cbn in *.
      destruct p. cbn in *.
      specialize (H1 z (ltac:(rewrite lookup_insert; eauto))).
      set_solver. }
    rewrite H0. sfinal.
  Qed.

  Lemma target_store v v' l Ψ:
    length (serialize_dvalue v) = length (serialize_dvalue v') ->
    l ↦t v -∗
    (l ↦t v' -∗ Ψ (Ret tt)) -∗
    target_red (η := vir_handler) (trigger (Store (# l) v')) Ψ.
  Proof.
    rewrite target_red_unfold.
    iIntros (Hlen) "Ht Hl". iLeft.
    iIntros (σ_t σ_s) "SI".
    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & SI)".

    iDestruct (heap_read with "Hh_t Ht") as %?; auto.
    rewrite mapsto_dval_eq /mapsto_dval_def.
    iPoseProof (heap_write with "Hh_t Ht") as ">(Hh_t & Ht)".
    cbn.
    iSpecialize ("Hl" with "Ht").

    iModIntro. iExists _,tt,(fun x => Tau(Ret x)),_.
    iSplitL ""; first iPureIntro.
    { solve_eq.
      apply get_logical_block_logical_view in H. rewrite /write.
      rewrite /vir_heap in H. rewrite /get_logical_block /get_logical_block_mem.
      rewrite H; cbn. by solve_eq. }
    iSplitR "Hl"; last final; sfinal.

    cbn; rewrite <- vir_heap_add_logical_block. cbn.
    rewrite /dvalue_to_block.
    apply Nat2Z.inj_iff in Hlen. do 2 rewrite <- Zlength_correct in Hlen.

    epose proof (@add_all_index_twice _ _ _ _ _ 0 (init_block (N.of_nat (length (serialize_dvalue v)))) Hlen).
    apply leibniz_equiv in H0. rewrite H0.
    rewrite !Zlength_correct in Hlen.
    apply Nat2Z.inj in Hlen. rewrite Hlen.
    rewrite /frames.
    destruct (vmem σ_t); cbn in *.

    destruct_HC "Hh_t".

    assert ({[ l ]} ∪ p.2 = p.2).
    { destruct Hbs. cbn in *.
      destruct p. cbn in *.
      specialize (H2 l (ltac:(rewrite lookup_insert; eauto))).
      set_solver. }
    rewrite H1. sfinal.
  Qed.

  Corollary target_store_block1 b v' Ψ ptr:
    ptr.1 ↦t [ b ] -∗
    (ptr.1 ↦t [ update_block b
                  (fun v => add_all_index (serialize_dvalue v') ptr.2 v) ] -∗
      Ψ (Ret tt)) -∗
    target_red (η := vir_handler) (trigger (Store (DVALUE_Addr ptr) v')) Ψ.
  Proof.
    destruct b; iApply target_store_block.
  Qed.

  Lemma target_local_read (x : LLVMAst.raw_id) (v : uvalue) i Ψ:
    ⊢ [x := v]t i -∗
      stack_tgt i -∗
      ([x := v]t i -∗
        stack_tgt i -∗
        Ψ (Ret v)) -∗
      target_red (η := vir_handler) (trigger (LocalRead x)) Ψ.
  Proof.
    rewrite target_red_unfold.
    iIntros "Hl Hf H"; iLeft; iIntros (σ_t σ_s) "SI".
    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & SI)".

    iDestruct (lheap_lookup with "Hh_t Hf Hl") as %Ht.
    rewrite -alist_find_to_map_Some in Ht.

    iExists _, v, (fun x => Tau(Ret x)), σ_t.

    destruct (vlocal σ_t) eqn : Hσ_t.
    iSplitL ""; first iPureIntro.
    { solve_eq.
      rewrite Hσ_t. cbn. rewrite Ht.
      solve_eq. rewrite -Hσ_t.
      by rewrite update_local_id. }

    iSpecialize ("H" with "Hl Hf").
    iSplitR "H"; last final.

    repeat iExists _; rewrite Hσ_t. by iFrame.
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
          Φ (Ret tt)) -∗
      target_red (η := vir_handler) (trigger (LocalWrite x v)) Φ.
  Proof.
    rewrite target_red_unfold .
    iIntros (Hlen) "Hd Hf Hl"; iLeft.
    iIntros (σ_t σ_s) "SI".

    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & SI)".
    destruct (vlocal σ_t) eqn: Hlocal_t.

    iExists _,
      (update_local (alist_add x v l, l0) σ_t),
      (fun x => Tau (Ret tt)),_.

    iSplitL ""; first iPureIntro.
    { solve_eq; rewrite Hlocal_t; by solve_eq. }

    iMod ((lheap_domain_alloc _ _ v)
           with "Hd Hf Hh_t") as "(Hh_t & Hp_t & Hf_t & Hd_t)"; [done | ].

    iDestruct (lheap_lookup with "Hh_t Hf_t Hp_t") as %Hl_t; cbn; iFrame.

    iSpecialize ("Hl" with "Hp_t Hd_t Hf_t"); iFrame.
    iSplitR "Hl"; last final; sfinal.
  Qed.

  Lemma target_local_write
    (x : LLVMAst.raw_id) (v v' : uvalue) i Φ :
    ⊢ [ x := v' ]t i -∗
      stack_tgt i -∗
      ([ x := v ]t i -∗
          stack_tgt i -∗
          Φ (Ret tt)) -∗
      target_red (η := vir_handler) (trigger (LocalWrite x v)) Φ.
  Proof.
    rewrite target_red_unfold.
    iIntros "Hx Hf Hl"; iLeft; iIntros (σ_t σ_s) "SI".

    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & SI)".
    destruct (vlocal σ_t) eqn: Hlocal_t.

    iExists _,
      (update_local (alist_add x v l, l0) σ_t),
      (fun x => Tau (Ret tt)),_.

    iSplitL ""; first iPureIntro.
    { solve_eq. rewrite Hlocal_t. by solve_eq. }

    iMod ((lheap_write _ _ _ v) with "Hh_t Hf Hx") as "(Hh_t & Hf & Hx)".

    iDestruct (lheap_lookup with "Hh_t Hf Hx") as %Hl_t; cbn.

    iSpecialize ("Hl" with "Hx Hf"); iFrame.
    iSplitR "Hl"; last final; sfinal.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* Simulation primitive laws on instruction-related events *)
  (* ------------------------------------------------------------------------ *)

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
    iApply (target_alloca with "Hl_t Hf_t"); [ done | ].
    iIntros (??) "Hl_t Ha_t Hf_t Hb_t".

    iApply source_red_sim_expr.
    iApply (source_alloca with "Hl_s Hf_s"); [ done | ].
    iIntros (??) "Hl_s Ha_s Hf_s Hb_s".
    vfinal; sfinal.
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
    iApply (target_load _ _ _ _ _ Hs Hτ_t with "Hl_t").
    iIntros "Hl_t";

    iApply source_red_sim_expr.
    iApply (source_load _ _ _ _ _ Hs Hτ_s with "Hl_s").
    iIntros "Hl_s"; vfinal.
    by rewrite !uvalue_to_dvalue_of_dvalue_to_uvalue.
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
    iApply (target_store _ _ _ _ Hlen_t with "Hl_t").
    iIntros "Hl_t".

    iApply source_red_sim_expr.
    iApply (source_store _ _ _ _ Hlen_s with "Hl_s").
    iIntros "Hl_s"; vfinal.
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
    iIntros "Ht Hs Hf_t Hf_s".
    iApply target_red_sim_expr.
    iApply (target_local_read with "Ht Hf_t").
    iIntros "Ht Hf_t".

    iApply source_red_sim_expr.
    iApply (source_local_read with "Hs Hf_s").
    iIntros "Hs Hf_s"; vfinal.
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
    iIntros (Ht Hs) "Hl_t Hl_s Hs_t Hs_s".
    iApply target_red_sim_expr.
    iApply (target_local_write_alloc _ _ _ _ _ Ht with "Hl_t Hs_t").
    iIntros "Ht Hl_t Hs_t".

    iApply source_red_sim_expr.
    iApply (source_local_write_alloc _ _ _ _ _ Hs with "Hl_s Hs_s").
    iIntros "Hs Hl_s Hs_s";
    vfinal.
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
    iIntros  "Hs_t Hs_s Ht Hs".
    iApply target_red_sim_expr.
    iApply (target_local_write with "Ht Hs_t").
    iIntros "Ht Hs_t".

    iApply source_red_sim_expr.
    iApply (source_local_write with "Hs Hs_s").
    iIntros "Hs Hs_s"; vfinal.
  Qed.

End primitive_rules.
