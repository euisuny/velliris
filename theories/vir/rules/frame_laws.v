(** *Local environment properties *)

From iris.prelude Require Import options.

From velliris.program_logic Require Import program_logic.
From velliris.vir.lang Require Export lang.

Set Default Proof Using "Type*".
Import uPred.

From Vellvm Require Import Handlers.Handlers.

Import LLVMEvents.

Open Scope nat_scope.

Section local_properties.

  Context {Σ : gFunctors} `{!vellirisGS Σ}.

  (* TODO: Move *)
  (* Difference between this and [free_frame]? *)
  Definition remove_frame
    : language.state vir_lang -> Z -> language.state vir_lang :=
    (fun σ x =>
       apply_mem
         (fun '(m, f) => (delete x m.1, m.2, delete_from_frame_stack f x)) σ).

  (* TODO ? *)
  Definition add_frame (f: frame_stack -> frame_stack) L : vir_state -> vir_state :=
    fun σ =>
      apply_local (fun '(l, ls) => (L, l::ls)) (apply_mem (fun '(m, s) => (m, f s)) σ).

  Lemma alloca_remove_tgt:
    ∀ σ_t σ_s C x v i n,
    x ∈ C ->
     ⊢ state_interp σ_t σ_s
        ∗ alloca_tgt i C
        ∗ x ↦t v
        ∗ stack_tgt i
        ∗ target_block_size x n ==∗
       state_interp (remove_frame σ_t x) σ_s
        ∗ alloca_tgt i (C ∖ {[x]})
        ∗ stack_tgt i.
  Proof.
    iIntros (????????) "[SI [Ha [Hx [Hf Hbs]]]]".
    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & SI)".
    iCombine "Hh_t Hx Ha Hf Hbs" as "HA".
    iDestruct (heap_free with "HA") as ">(Hh_t & Ha & Hcf)"; eauto; iFrame.
    iModIntro; repeat iExists _; iFrame. cbn.
    destruct (vmem σ_t); iFrame.
  Qed.

  Lemma alloca_remove_src:
    ∀ σ_t σ_s C x v i n,
      x ∈ C ->
      ⊢ state_interp σ_t σ_s
        ∗ alloca_src i C
        ∗ x ↦s v
        ∗ stack_src i
        ∗ source_block_size x n ==∗
        state_interp σ_t (remove_frame σ_s x)
        ∗ alloca_src i (C ∖ {[x]})
        ∗ stack_src i.
  Proof.
    iIntros (????????) "[SI [Ha [Hx [Hf Hbs]]]]".
    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & SI)".
    iCombine "Hh_s Hx Ha Hf Hbs" as "HA".
    iDestruct (heap_free with "HA") as ">(Hh_s & Ha & Hcf)"; eauto; iFrame.
    iModIntro; repeat iExists _; iFrame.
    cbn ;destruct (vmem σ_s); iFrame.
  Qed.

  Definition vir_free_frame m : vir_state -> vir_state :=
    fun σ => update_mem m (apply_local (fun '(l, ls) => (List.hd l ls, List.tl ls)) σ).

  Lemma alloca_free_frame_source:
    forall (σ_t σ_s : vir_state) A i m' (FA : gmap loc val),
    1 < length i ->
    free_frame (vmem σ_s) = inr m' ->
    state_interp σ_t σ_s
      ∗ alloca_src i A ∗
        ⌜dom FA ≡ A⌝
      ∗ ([∗ map] l ↦ v ∈ FA,
          l ↦s [ v ] ∗ source_block_size l (Some (logical_block_size v)))
      ∗ stack_src i ==∗
    state_interp σ_t (vir_free_frame m' σ_s)
      ∗ stack_src (tl i).
  Proof.
    iIntros (?????? Hlen Hfree) "(SI & HA & Hd & Hp & HS)".
    iDestruct "SI" as (???)
      "(Hh_s & Hh_t & H_c & Hbij & Hg)".

    iCombine "HS Hh_s HA Hd Hp" as "H".
    destruct m'. cbn.
    destruct (vmem σ_s).
    cbn -[state_interp].
    iDestruct
      (vir_state.free_frame _ _ _ _ _ _ _ _ _ _ _ Hlen Hfree with "H") as
      ">(Hh & H)".
    iFrame. cbn.
    cbn in Hfree. destruct f0; inv Hfree.
    destruct (vlocal σ_s); cbn; destruct p; cbn;
    iExists C, S, G; by iFrame.
  Qed.

  Lemma alloca_free_frame_target:
    forall (σ_t σ_s : vir_state) A i m' (FA : gmap loc val),
    1 < length i ->
    free_frame (vmem σ_t) = inr m' ->
    state_interp σ_t σ_s
      ∗ alloca_tgt i A ∗
        ⌜dom FA ≡ A⌝
      ∗ ([∗ map] l ↦ v ∈ FA,
          l ↦t [ v ] ∗ target_block_size l (Some (logical_block_size v)))
      ∗ stack_tgt i ==∗
    state_interp (vir_free_frame m' σ_t) σ_s
      ∗ stack_tgt (tl i).
  Proof.
    iIntros (?????? Hlen Hfree) "(SI & HA & Hd & Hp & HS)".
    iDestruct "SI" as (???)
      "(Hh_s & Hh_t & H_c & Hbij & Hg)".

    iCombine "HS Hh_t HA Hd Hp" as "H".
    destruct m'. cbn.
    destruct (vmem σ_t).
    cbn -[state_interp].
    iDestruct
      (vir_state.free_frame _ _ _ _ _ _ _ _ _ _ _ Hlen Hfree with "H") as
      ">(Hh_t & H)".
    iFrame. destruct f0; inv Hfree.
    destruct (vlocal σ_t); cbn; destruct p; cbn;
      repeat iExists _; by iFrame.
  Qed.

  Lemma alloca_free_frame
    (σ_t σ_s : vir_state) C_t C_s i_t i_s m_t' m_s' (FA_t FA_s : gmap loc val):
    1 < length i_t ->
    1 < length i_s ->
    free_frame (vmem σ_t) = inr m_t' ->
    free_frame (vmem σ_s) = inr m_s' ->
    state_interp σ_t σ_s
      ∗ alloca_tgt i_t C_t
      ∗ alloca_src i_s C_s
      ∗ ⌜dom FA_t ≡ C_t⌝
      ∗ ⌜dom FA_s ≡ C_s⌝
      ∗ ([∗ map] l ↦ v ∈ FA_t,
          l ↦t [ v ] ∗ target_block_size l (Some (logical_block_size v)))
      ∗ ([∗ map] l ↦ v ∈ FA_s,
          l ↦s [ v ] ∗ source_block_size l (Some (logical_block_size v)))
      ∗ stack_tgt i_t
      ∗ stack_src i_s ==∗
    state_interp (vir_free_frame m_t' σ_t) (vir_free_frame m_s' σ_s)
      ∗ stack_tgt (tl i_t)
      ∗ stack_src (tl i_s).
  Proof.
    iIntros (Hlen_t Hlen_s Hf_t Hf_s)
      "(SI & HA_t & HA_s & Hdom_t & Hdom_s & Hl_t & Hl_s & HS_t & HS_s)".
    iCombine "SI HA_t Hdom_t Hl_t HS_t" as "H_t".
    iDestruct (alloca_free_frame_target _ _ _ _ _ _ Hlen_t Hf_t with "H_t")
      as ">(SI & H)".
    iCombine "SI HA_s Hdom_s Hl_s HS_s" as "H_s".
    iDestruct (alloca_free_frame_source _ _ _ _ _ _ Hlen_s Hf_s with "H_s")
      as ">(SI_s & H_s)".
    by iFrame.
  Qed.

  Lemma frames_add_to_frame_stack l v m f:
    frames (add_to_frame (add_logical_block l v (m, f)) l) = add_to_frame_stack f l.
  Proof.
    rewrite /frames /add_to_frame /add_to_frame_stack; cbn.
    destruct f; eauto.
  Qed.

  Lemma alloca_push_target:
    ∀ (σ_t σ_s : vir_state) C i l v,
      (⊙ vmem σ_t) !! l = None ->
      l ∉ vir_dyn (vmem σ_t) ->
      state_interp σ_t σ_s
        ∗ alloca_tgt i C
        ∗ stack_tgt i ==∗
      state_interp
        (apply_mem
          (fun m => add_to_frame (add_logical_block l v (vmem σ_t)) l) σ_t)
        σ_s
      ∗ l ↦t [ v ]
      ∗ alloca_tgt i ({[ l ]} ∪ C)
      ∗ stack_tgt i
      ∗ target_block_size l (Some (logical_block_size v)).
  Proof.
    iIntros (????????) "(SI & HA)".
    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & Hg)".

    iCombine "Hh_t HA" as "H".
    iDestruct (allocaS_push with "H") as ">(H_t & Hl & HA & Hs & Hbs)";
      eauto.
    iFrame; repeat iExists _; iFrame; cbn.
    destruct (vmem σ_t), (vlocal σ_t). rewrite !frames_add_to_frame_stack; auto; cbn.
    destruct f; eauto.
  Qed.

  Lemma alloca_push_source:
    ∀ σ_t σ_s C i l v,
      (⊙ vmem σ_s) !! l = None ->
      l ∉ vir_dyn (vmem σ_s) ->
      state_interp σ_t σ_s
        ∗ alloca_src i C
        ∗ stack_src i
      ==∗
      state_interp
        σ_t
        (apply_mem
          (fun m => add_to_frame (add_logical_block l v m) l) σ_s)
      ∗ l ↦s [ v ]
      ∗ alloca_src i ({[ l ]} ∪ C)
      ∗ stack_src i
      ∗ source_block_size l (Some (logical_block_size v)).
  Proof.
    iIntros (????????) "(SI & HA)".
    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & Hg)".

    iCombine "Hh_s HA" as "H".
    iDestruct (allocaS_push with "H") as ">(H_s & Hl & HA & Hs & Hbs)";
      eauto.
    iFrame; repeat iExists _; iFrame; cbn.
    destruct (vmem σ_s), (vlocal σ_s); rewrite !frames_add_to_frame_stack; auto; cbn.
    rewrite /vir_dyn; cbn.
    destruct f; eauto.
  Qed.

  Lemma allocaS_push:
    ∀ σ_t σ_s C_t C_s i l_t l_s v_t v_s,
      (⊙ vmem σ_t) !! l_t = None ->
      (⊙ vmem σ_s) !! l_s = None ->
      l_t ∉ vir_dyn (vmem σ_t) ->
      l_s ∉ vir_dyn (vmem σ_s) ->
      state_interp σ_t σ_s
        ∗ alloca_tgt i C_t
        ∗ alloca_src i C_s
        ∗ stack_tgt i
        ∗ stack_src i ==∗
      state_interp
        (apply_mem
          (fun m => add_to_frame (add_logical_block l_t v_t m) l_t) σ_t)
        (apply_mem
          (fun m => add_to_frame (add_logical_block l_s v_s m) l_s) σ_s)
      ∗ l_t ↦t [ v_t ]
      ∗ l_s ↦s [ v_s ]
      ∗ alloca_tgt i ({[ l_t ]} ∪ C_t)
      ∗ alloca_src i ({[ l_s ]} ∪ C_s)
      ∗ stack_tgt i
      ∗ stack_src i
      ∗ target_block_size l_t (Some (logical_block_size v_t))
      ∗ source_block_size l_s (Some (logical_block_size v_s)).
  Proof.
    iIntros (?????????????) "(SI & HA_t & HA_s & Hf_t & Hf_s)".
    iCombine "SI HA_t Hf_t" as "H_t".
    iDestruct (alloca_push_target _ _ _ _ _ _ H with "H_t") as ">(SI & Hl_t & HA_t & Hf_t & Hbs)"; eauto.
    iCombine "SI HA_s Hf_s" as "H_s".
    iDestruct (alloca_push_source _ _ _ _ _ _ H0 with "H_s") as ">(SI & Hl_s & HA_s & Hf_s & Hbt)"; eauto.
    by iFrame.
  Qed.

  Lemma can_free_frame_target F (σ_t σ_s : vir_state):
    1 < length F ->
    stack_tgt F -∗
    state_interp σ_t σ_s -∗
    ∃ m', ⌜free_frame (vmem σ_t) = inr m'⌝.
  Proof.
    iIntros (Hsize) "Hf SI".

    iDestruct "SI" as (???)
       "(Hh_s & Hh_t & H_c & Hbij & SI)".

    iDestruct (can_free_frame _ _ _ _ _ _ _ Hsize with "Hf Hh_t") as %H.
    destruct H. iPureIntro.

    rewrite /free_frame in H. rewrite /frames in H.
    destruct (vmem σ_t).
    destruct f; inversion H; subst. eexists _; done.
  Qed.

  Lemma can_free_frame_source F (σ_t σ_s : vir_state):
    1 < length F ->
    stack_src F -∗
    state_interp σ_t σ_s -∗
    ∃ m', ⌜free_frame (vmem σ_s) = inr m'⌝.
  Proof.
    iIntros (Hsize) "Hf SI".

    iDestruct "SI" as (???)
       "(Hh_s & Hh_t & H_c & Hbij & SI)".

    iDestruct (can_free_frame _ _ _ _ _ _ _ Hsize with "Hf Hh_s") as %H.
    destruct H. iPureIntro.

    rewrite /free_frame in H. rewrite /frames in H.
    destruct (vmem σ_s).
    destruct f; inversion H; subst. eexists _; done.
  Qed.

  From velliris.vir Require Import bij_laws.

  Open Scope nat_scope.

  Notation "m ∖' f"  := (free_frame_memory f m) (at level 20).
  Notation "m ∖'' f"  := (free_locations_from_frame m f) (at level 20).

  (* LATER: Move to Utils *)
  Lemma list_subseteq_remove mf mf' a:
    a ∉ mf ->
    NoDup mf ->
    NoDup mf' ->
    a :: mf ⊆ mf' ->
    mf ⊆ remove Z.eq_dec a mf'.
  Proof.
    repeat intro.
    revert mf a H H0 H1 H2 H3.
    induction mf'.
    { cbn. intros. destruct mf; set_solver. }
    intros.

    apply NoDup_cons in H1; destruct H1.
    destruct (decide (a0 = a)); subst.
    { rewrite remove_cons.
      assert (mf ⊆ mf').
      { repeat intro. do 2 red in H2.
        assert (x0 ∈ a :: mf) by set_solver.
        specialize (H2 _ H6). set_solver. }
      assert (x <> a) by set_solver.
      apply elem_of_list_In.
      apply Util.remove_not_In; eauto.
      apply elem_of_list_In. set_solver. }

    cbn. destruct (Z.eq_dec a0 a); try done.
    assert (x ∈ a0 :: mf) by set_solver.
    pose proof (H2' := H2).
    specialize (H2 _ H5).
    rewrite elem_of_cons in H2.
    apply elem_of_cons.
    destruct H2; eauto.
    destruct (decide (x = a)); eauto.
    right. apply elem_of_list_In.
    destruct (decide (x = a0)); subst; eauto.
    { set_solver. }
    eapply Util.remove_not_In; eauto.
    by apply elem_of_list_In.
  Qed.

  (* LATER: Move to Utils *)
  Lemma difference_distr_free_frame:
    ∀ (mf mf' : mem_frame) (h : gmap Z logical_block * gset Z),
      NoDup mf -> NoDup mf' →
      mf ⊆ mf' →
      (h ∖' mf) ∖' (mf' ∖'' mf) = h ∖' mf'.
  Proof.
    intros mf mf' h ???.

    rewrite /free_frame_memory; cbn. f_equiv.
    revert h mf' H H0 H1.
    induction mf; cbn.
    { intros; induction mf'; eauto. }
    { intros; cbn.
      rewrite !fold_left_delete_comm.
      apply NoDup_cons in H; destruct H.

      rewrite IHmf; eauto; cycle 1.
      { apply util.NoDup_remove; eauto; set_solver. }
      { eapply (list_subseteq_remove _ _ a) in H1; eauto. }
      rewrite -fold_left_delete_comm.
      rewrite (fold_delete_distr a mf' h.1);
        eauto; [ | set_solver ].
      by rewrite fold_left_delete_comm. }
  Qed.

  Lemma state_interp_dom_disjoint_bij_and_own (mf_t mf_s : mem_frame)
    (L_t L_s : gmap Z val) C σ_t σ_s:
    ⊢ ([∗ list] l_t0;l_s0 ∈ mf_t;mf_s,
         (l_t0, 0%Z) ↔h (l_s0, 0%Z) ∗ ⌜C !! (l_t0, l_s0) = None⌝) -∗
     checkout C -∗
    ([∗ map] l↦v ∈ L_t, l ↦t [v] ∗ target_block_size l (Some (logical_block_size v))) -∗
    ([∗ map] l↦v ∈ L_s, l ↦s [v] ∗ source_block_size l (Some (logical_block_size v))) -∗
    state_interp σ_t σ_s ==∗
    ⌜dom L_t ## list_to_set mf_t /\ dom L_s ## list_to_set mf_s⌝ ∗
    ([∗ list] l_t0;l_s0 ∈ mf_t;mf_s,
         (l_t0, 0%Z) ↔h (l_s0, 0%Z) ∗ ⌜C !! (l_t0, l_s0) = None⌝) ∗
     checkout C ∗
    ([∗ map] l↦v ∈ L_t, l ↦t [v] ∗ target_block_size l (Some (logical_block_size v))) ∗
    ([∗ map] l↦v ∈ L_s, l ↦s [v] ∗ source_block_size l (Some (logical_block_size v))) ∗
    state_interp σ_t σ_s.
  Proof.
    iIntros "Hl HC Hl_t Hl_s SI".
    iDestruct "SI" as (???) "(Hh_t&Hh_s&CI&Hbij&SI_rem)".
    iDestruct (ghost_var_agree with "HC CI") as "%HC"; subst.

    iInduction mf_t as [ | ] "IH" forall (mf_s L_t L_s S C0).
    { iDestruct (big_sepL2_nil_inv_l with "Hl") as "%Hl"; subst. iFrame.
      iSplitL ""; first (iPureIntro; set_solver).
      rewrite /state_interp; cbn. iExists C0, S, G; by iFrame. }
    { iDestruct (big_sepL2_cons_inv_l with "Hl") as (???) "(H & #Hl)".
      iDestruct "H" as "(#Ha & %HC)". subst; cbn.
      rewrite !disjoint_union_r.

      remember (_ /\ _)%I as H.
      assert (
        H <->
        (dom L_t ## {[a]} ∧ dom L_s ## {[x2]}) ∧
        (dom L_t ## list_to_set mf_t /\ dom L_s ## list_to_set l2'))%I.
      { subst; intros.
        red. split; intros;
        destruct H as ((?&?)&?&?); repeat (split; eauto). }
      rewrite H0; clear H0.

      cbn; destruct (decide (x2 ∈ dom L_s)) eqn: Ha.
      { (* Derive contradiction by accessing the heap bijection *)
        clear Ha.
        apply elem_of_dom in e. destruct e.
        rewrite -(insert_delete L_s x2 x); eauto.
        rewrite big_opM_insert; cycle 1.
        { by rewrite lookup_delete. }
        iDestruct "Hl_s" as "((Has & Hb) & Hl_s)".

        iDestruct "Ha" as "(Ha & %H1)"; cbn.
        iDestruct (heapbij_access with "Hbij Ha") as
          "(%Hin & Halloc & Hclose)".

        iPoseProof (heap_read_st_1 with "Hh_t Has") as "%Hread".

        iPoseProof (alloc_rel_remove_frac_None
                     with "Halloc Hh_s Hh_t") as "H"; eauto.
        iMod "H".
        iDestruct "H" as (??) "(Ht & Hs & _)".
        iClear "HC Hb Hl_t Hl_s CI Hclose Ht IH Ha".
        iExFalso.
        iPoseProof (heap_mapsto_combine_0 with "Has Hs") as "H".
        iDestruct (vir_state.mapsto_valid with "H") as %Hi.
        done. }

      cbn; destruct (decide (a ∈ dom L_t)) eqn: Hat.
      { (* Derive contradiction by accessing the heap bijection *)
        clear Hat.
        apply elem_of_dom in e. destruct e.
        rewrite -(insert_delete L_t a x); eauto.
        rewrite big_opM_insert; cycle 1.
        { by rewrite lookup_delete. }
        iDestruct "Hl_t" as "((Hat & Hb) & Hl_t)".

        iDestruct "Ha" as "(Ha & %H1)"; cbn.
        iDestruct (heapbij_access with "Hbij Ha") as
          "(%Hin & Halloc & Hclose)".

        iPoseProof (heap_read_st_1 with "Hh_s Hat") as "%Hread".

        iPoseProof (alloc_rel_remove_frac_None_tgt
                     with "Halloc Hh_s Hh_t") as "H"; eauto.
        iMod "H".
        iDestruct "H" as (??) "(Ht & Hs & _)".
        iClear "HC Hb Hl_t Hl_s CI Hclose Hs IH Ha".
        iExFalso.
        iPoseProof (heap_mapsto_combine_0 with "Hat Ht") as "H".
        iDestruct (vir_state.mapsto_valid with "H") as %Hi.
        done. }

      iSpecialize ("IH" with "Hl HC Hl_t Hl_s Hh_t Hh_s CI Hbij SI_rem").
      iMod "IH".
      iDestruct "IH" as "(%Hl' & HC & Hm_t & Hm_s & SI)"; iFrame.
      iSplitL "".
      { iPureIntro. by split; first set_solver. }
      iSplitL ""; first done. by iPureIntro. }
  Qed.

  Lemma frame_remove_bij_and_own (mf_t mf_s : mem_frame)
      (A_t A_s : gset _) (L_t L_s : gmap Z val) mf_t' mf_s'
    i_t i_s g_t g_s l_t l_s h_t h_s f_t f_s C:
    1 < length i_t ->
    1 < length i_s ->
    list_to_set mf_t ∪ dom L_t = A_t ->
    list_to_set mf_s ∪ dom L_s = A_s ->
    NoDup mf_t ->
    NoDup mf_s ->
    checkout C -∗
    ([∗ list] k ↦ l_t; l_s ∈ mf_t; mf_s,
       (l_t, 0%Z) ↔h (l_s, 0%Z) ∗ ⌜C !! (l_t, l_s) = None ⌝) -∗
    ([∗ map] l ↦ v ∈ L_t,
        l ↦t [ v ] ∗ target_block_size l (Some (logical_block_size v))) -∗
    ([∗ map] l ↦ v ∈ L_s,
        l ↦s [ v ] ∗ source_block_size l (Some (logical_block_size v))) -∗
    stack_tgt i_t -∗
    stack_src i_s -∗
    alloca_tgt i_t A_t -∗
    alloca_src i_s A_s -∗
    state_interp
      {| vglobal := g_t;
         vlocal := l_t;
         vmem := (h_t, Snoc f_t mf_t') |}
      {| vglobal := g_s;
         vlocal := l_s;
         vmem := (h_s, Snoc f_s mf_s') |} ==∗
    checkout C ∗
    stack_tgt (tail i_t) ∗
    stack_src (tail i_s) ∗
    state_interp
      {| vglobal := g_t;
         vlocal := (hd l_t.1 l_t.2, tail l_t.2);
         vmem := (free_frame_memory mf_t' h_t, f_t) |}
      {| vglobal := g_s;
         vlocal := (hd l_s.1 l_s.2, tail l_s.2);
         vmem := (free_frame_memory mf_s' h_s, f_s) |}.
  Proof.
    iIntros (Hlen_t Hlen_s Hf_t Hf_s Hnodup_t Hnodup_s)
      "HC #Hl Ht Hs Hs_t Hs_s Ha_t Ha_s SI".
    iPoseProof (state_interp_WF with "SI") as "%WF".
    iPoseProof (state_interp_alloca_agree with "Hs_t Hs_s Ha_t Ha_s SI") as "%HAg".

    iPoseProof (state_interp_dom_disjoint_bij_and_own with "Hl HC Ht Hs SI") as
      ">(%Hdj & _ & HC & Ht & Hs & SI)".
    destruct Hdj as (Hdj1 & Hdj2).

    iPoseProof
      (frame_mem_remove_bij with "HC Hl Hs_t Hs_s Ha_t Ha_s SI")
      as ">Hrem"; eauto; [ set_solver | set_solver |].
    iDestruct "Hrem" as "(HC & Hs_t & Hs_s & Ha_t & Ha_s & SI)".

    iAssert (⌜dom L_t ≡ A_t ∖ list_to_set mf_t⌝)%I as "Hdom_t".
    { rewrite -Hf_t. iPureIntro. set_solver. }

    iCombine "SI Ha_t Hdom_t Ht Hs_t" as "Ht_a".
    iPoseProof (alloca_free_frame_target with "Ht_a") as
      ">(SI & Ht)"; eauto.

    iAssert (⌜dom L_s ≡ A_s ∖ list_to_set mf_s⌝)%I as "Hdom_s".
    { rewrite -Hf_s. iPureIntro. set_solver. }
    iCombine "SI Ha_s Hdom_s Hs Hs_s" as "Hs_a".
    iPoseProof (alloca_free_frame_source with "Hs_a") as
      ">(SI & Hs)"; eauto.

    rewrite /vir_free_frame.

    cbn -[state_interp].

    cbn in HAg; destruct HAg.
    assert (mf_t ⊆ mf_t') by set_solver.
    assert (mf_s ⊆ mf_s') by set_solver.
    assert (NoDup mf_t').
    { destruct WF as (?&Hsf&?);
        apply NoDup_app in Hsf; destruct Hsf; auto. }
    assert (NoDup mf_s').
    { destruct WF as (?&?&?&Hsf&?).
        apply NoDup_app in Hsf; destruct Hsf; auto. }

    rewrite !difference_distr_free_frame; eauto. cbn.
      destruct l_s, l_t; cbn. by iFrame.
  Qed.

  Lemma frame_stack_and_mem_pop (mf_t mf_s : mem_frame) A_t A_s mf_t' mf_s'
    i_t i_s h_t h_s f_t f_s C σ_t σ_s:
    1 < length i_t ->
    1 < length i_s ->
    vmem σ_t = (h_t, Snoc f_t mf_t') ->
    vmem σ_s = (h_s, Snoc f_s mf_s') ->
    list_to_set mf_t = A_t ->
    list_to_set mf_s = A_s ->
    NoDup mf_t ->
    NoDup mf_s ->
    checkout C -∗
    ([∗ list] k ↦ l_t; l_s ∈ mf_t; mf_s,
       (l_t, 0%Z) ↔h (l_s, 0%Z) ∗ ⌜C !! (l_t, l_s) = None ⌝) -∗
    stack_tgt i_t -∗
    stack_src i_s -∗
    alloca_tgt i_t A_t -∗
    alloca_src i_s A_s -∗
    state_interp σ_t σ_s ==∗
    checkout C ∗
    stack_tgt (tail i_t) ∗
    stack_src (tail i_s) ∗
    state_interp
      {| vglobal := vglobal σ_t;
         vlocal := (hd (vlocal σ_t).1 (vlocal σ_t).2, tail (vlocal σ_t).2);
         vmem := (free_frame_memory mf_t h_t, f_t) |}
      {| vglobal := vglobal σ_s;
         vlocal := (hd (vlocal σ_s).1 (vlocal σ_s).2, tail (vlocal σ_s).2);
         vmem := (free_frame_memory mf_s h_s, f_s) |}.
  Proof.
    iIntros (Hlen_t Hlen_s Hmem_t Hmem_s Hf_t Hf_s Hnodup_t Hnodup_s)
      "HC #Hl Hs_t Hs_s Ha_t Ha_s SI".
    iDestruct (state_interp_alloca_agree with "Hs_t Hs_s Ha_t Ha_s SI") as %HA.
    destruct HA as (HA_t&HA_s); cbn in HA_t, HA_s.
    rewrite /free_frame_memory.

    iInduction mf_s as [ | ] "IH" forall
      (σ_t σ_s mf_t mf_t' mf_s' f_t f_s h_t h_s A_s A_t HA_t HA_s Hf_s Hf_t Hnodup_t
      Hmem_t Hmem_s);
                                    cbn -[state_interp] in *.
    { rewrite Hmem_t Hmem_s in HA_t HA_s.
      iDestruct (big_sepL2_nil_inv_r with "Hl") as %Hl; subst.
      cbn.

      iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & %HWF & SI)".
      destruct mf_t'; last set_solver.

      iDestruct (ghost_var_agree with "HC H_c") as "%HC". subst.
      cbn in *.
      iCombine "Hs_t Hh_t Ha_t" as "Hs_t".
      destruct mf_s'; [ | set_solver ]. rewrite Hmem_t Hmem_s; cbn.
      iPoseProof (free_frame_empty1 with "Hs_t") as
        ">(Hh_t & Hs_t & Ha_t)"; eauto.
      iFrame.

      iCombine "Hs_s Hh_s Ha_s" as "Hs_s".
      iPoseProof (free_frame_empty1 with "Hs_s") as
        ">(Hh_s & Hs_s & Ha_s)"; eauto.
      iFrame.

      iExists C0, S, G; iFrame.
      cbn; iFrame.
      rewrite /vir_heap /vir_dyn; cbn.
      set_solver. }

    { iDestruct (big_sepL2_cons_inv_r with "Hl") as (???) "(Hla & Hl_tl)";
        iClear "Hl"; subst; cbn -[state_interp].
      rewrite Hmem_t Hmem_s; cbn -[state_interp].
      rewrite Hmem_t in Hf_t; rewrite Hmem_s in Hf_s.
      assert (Ha: a ∈ (list_to_set mf_s' : gset _)).
      { set_solver. }
      assert (Hf_s': list_to_set mf_s' = {[a]} ∪ (list_to_set mf_s' ∖ {[ a ]}: gset _)).
      { apply union_difference_L. set_solver. }
      iDestruct (state_interp_WF with "SI") as %HWF.

      cbn in HWF.
      remember (fix _aux (m : frame_stack) (acc : mem_frame) {struct m} : list Z :=
                match m with
                | Mem.Singleton m0 => m0 ++ acc
                | Snoc m0 f => f ++ _aux m0 acc
                end) as Haux.
      destruct HWF as (Hnd_lt&Hnd_t'&Hnd_ls&Hnd_s'&Hdt&Hds).

      apply NoDup_cons in Hnodup_t, Hnodup_s.
      destruct Hnodup_t as (Hnx1 & Hnodup_l1').
      destruct Hnodup_s as (Ha_fs & Hnd_fs).
      rewrite Hmem_t Hmem_s in Hdt, Hds, Hnd_s', Hnd_t'. cbn in *.
      apply NoDup_app in Hnd_s'; destruct Hnd_s' as (Hnd_s' & _).
      apply NoDup_app in Hnd_t'; destruct Hnd_t' as (Hnd_t' & _).

      assert (Heq: list_to_set mf_s = (list_to_set mf_s' ∖ {[a]} : gset _)).
      { set_solver. }
      rewrite -list_to_set_delete_from_frame in Heq.
      rewrite Heq.

      symmetry in Heq.
      iSpecialize ("IH" $! Hnd_fs _ _ _ _ _ _ _ _ _ _ _ _ _  Heq _ Hnodup_l1' _ _
                    with "Hl_tl").

      assert (Ha_free: list_to_set (a :: delete_from_frame mf_s' a) =
                (list_to_set mf_s' : gset _)).
      { cbn. rewrite list_to_set_delete_from_frame.
        set_solver. }
      iDestruct "Hla" as "(Hla & %HC)".

      iPoseProof (state_interp_free with
          "Hla HC Hs_t Hs_s Ha_t Ha_s SI") as "H"; eauto; [ set_solver | .. ].
      { rewrite -elem_of_dom.
        rewrite -Hds. set_solver. }
      iMod "H".

      iDestruct "H" as "(HC & Hs_t & Hs_s & Ha_t & Ha_s & SI)".

      iSpecialize ("IH" with "HC Hs_t Hs_s Ha_t").

      assert (list_to_set mf_s' ∖ {[a]} = (list_to_set mf_s : gset _)).
      { set_solver. }
      rewrite H; clear H.

      iSpecialize ("IH" with "Ha_s SI"); cbn.
      iMod "IH".
      iDestruct "IH" as "(HC & Hs_t & Hs_s & SI)".
      iFrame "HC Hs_t Hs_s".
      Unshelve. (* TODO Cleanup *)
      2 : exact (remove Z.eq_dec x1 mf_t').
      2 : exact (remove Z.eq_dec a mf_s').
      2 : exact f_t.
      2 : exact f_s.
      2 : exact (delete x1 h_t.1, h_t.2).
      2 : exact (delete a h_s.1, h_s.2).
      all : eauto.
      2 : set_solver.
      cbn.
      by apply list_to_set_remove. }
  Qed.

  Open Scope nat_scope.
  Lemma frame_mem_pop1 (mf_t mf_s : mem_frame) A_t A_s mf_t' mf_s'
    i_t i_s g_t g_s l_t l_s h_t h_s f_t f_s C:
    1 < length i_t ->
    1 < length i_s ->
    list_to_set mf_t = A_t ->
    list_to_set mf_s = A_s ->
    NoDup mf_t ->
    NoDup mf_s ->
    checkout C -∗
    ([∗ list] k ↦ l_t; l_s ∈ mf_t; mf_s,
       (l_t, 0%Z) ↔h (l_s, 0%Z) ∗ ⌜C !! (l_t, l_s) = None ⌝) -∗
    stack_tgt i_t -∗
    stack_src i_s -∗
    alloca_tgt i_t A_t -∗
    alloca_src i_s A_s -∗
    state_interp
      {| vglobal := g_t;
         vlocal := l_t;
         vmem := (h_t, Snoc f_t mf_t') |}
      {| vglobal := g_s;
         vlocal := l_s;
         vmem := (h_s, Snoc f_s mf_s') |} ==∗
    checkout C ∗
    state_interp
      {| vglobal := g_t;
         vlocal := l_t;
         vmem := (free_frame_memory mf_t h_t, Snoc f_t nil) |}
      {| vglobal := g_s;
         vlocal := l_s;
         vmem := (free_frame_memory mf_s h_s, Snoc f_s nil) |}.
  Proof.
    iIntros (Hlen_t Hlen_s Hf_t Hf_s Hnodup_t Hnodup_s) "HC #Hl Hs_t Hs_s Ha_t Ha_s SI".
    iDestruct (state_interp_alloca_agree with "Hs_t Hs_s Ha_t Ha_s SI") as %HA.
    destruct HA as (HA_t&HA_s); cbn in HA_t, HA_s.
    rewrite /free_frame_memory.

    iInduction mf_s as [ | ] "IH" forall (mf_t mf_t' mf_s' f_t f_s h_t h_s A_s A_t HA_t HA_s Hf_s
                                       Hf_t Hnodup_t);
                                    cbn -[state_interp] in *.
    { destruct mf_s'; [ | set_solver].
      iDestruct (big_sepL2_nil_inv_r with "Hl") as %Hl; subst.
      cbn.

      iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & %HWF & SI)".
      destruct mf_t'; last set_solver.

      iDestruct (ghost_var_agree with "HC H_c") as "%HC". subst.
      destruct l_s, l_t.
      iCombine "Hs_t Hh_t Ha_t" as "Hs_t".
      iPoseProof (free_frame_empty with "Hs_t") as
        ">(Hh_t & Hs_t & Ha_t)"; eauto.
      iFrame.

      iCombine "Hs_s Hh_s Ha_s" as "Hs_s".
      iPoseProof (free_frame_empty with "Hs_s") as
        ">(Hh_s & Hs_s & Ha_s)"; eauto.
      iFrame.

      iExists C0, S, G; iFrame.
      cbn; iFrame.
      rewrite /vir_heap /vir_dyn; cbn.
      set_solver. }

    { iDestruct (big_sepL2_cons_inv_r with "Hl") as (???) "(Hla & Hl_tl)";
        iClear "Hl"; subst; cbn -[state_interp].
      assert (Ha: a ∈ (list_to_set mf_s' : gset _)).
      { set_solver. }
      assert (Hf_s': list_to_set mf_s' = {[a]} ∪ (list_to_set mf_s' ∖ {[ a ]}: gset _)).
      { apply union_difference_L. set_solver. }
      iDestruct (state_interp_WF with "SI") as %HWF.

      cbn in HWF.
      remember (fix _aux (m : frame_stack) (acc : mem_frame) {struct m} : list Z :=
                match m with
                | Mem.Singleton m0 => m0 ++ acc
                | Snoc m0 f => f ++ _aux m0 acc
                end) as Haux.
      destruct HWF as (Hnd_lt&Hnd_t'&Hnd_ls&Hnd_s'&Hdt&Hds).

      apply NoDup_cons in Hnodup_t, Hnodup_s.
      destruct Hnodup_t as (Hnx1 & Hnodup_l1').
      destruct Hnodup_s as (Ha_fs & Hnd_fs).
      apply NoDup_app in Hnd_s'; destruct Hnd_s' as (Hnd_s' & _).
      apply NoDup_app in Hnd_t'; destruct Hnd_t' as (Hnd_t' & _).

      assert (Heq: list_to_set mf_s = (list_to_set mf_s' ∖ {[a]} : gset _)).
      { set_solver. }
      rewrite -list_to_set_delete_from_frame in Heq.
      rewrite Heq.

      (* LATER: Move out helper lemma *)
      assert
        (Hcomm_delete:
          forall a mf_s' (h_s : heap * gset Z),
          a ∈ (list_to_set mf_s' : gset Z) ->
          NoDup mf_s' ->
          fold_left (fun m key => delete key m) mf_s' h_s.1 =
          delete a (fold_left (fun m key => delete key m) (delete_from_frame mf_s' a) h_s.1)).
      { clear. intros * Ha Hnd_s'. rewrite -fold_left_delete_comm.
        rewrite /delete_from_frame.
        revert a h_s Ha.
        induction mf_s'.
        { set_solver. }
        { intros. cbn in Ha; cbn.

          apply NoDup_cons in Hnd_s'. destruct Hnd_s' as (?&Hnd_s').
          apply elem_of_union in Ha.
          destruct Ha.
          { assert (a0 = a) by set_solver.
            subst. destruct (Z.eq_dec a a); last done.
            f_equiv; eauto.
            rewrite notin_remove; eauto.
            intros Hfalse. apply elem_of_list_In in Hfalse.
            set_solver. }
          { assert (a0 <> a).
            { intro; apply H. subst. set_solver. }
            destruct (Z.eq_dec a0 a); first done.
            cbn. rewrite fold_left_delete_comm.
            setoid_rewrite fold_left_delete_comm at 1.
            f_equiv.
            apply IHmf_s'; eauto. } } }

      symmetry in Heq.
      iSpecialize ("IH" $! Hnd_fs _ _ _ _ _ _ _ _ _ _ _ Heq _ Hnodup_l1'
                    with "Hl_tl").

      assert (Ha_free: list_to_set (a :: delete_from_frame mf_s' a) =
                (list_to_set mf_s' : gset _)).
      { cbn. rewrite list_to_set_delete_from_frame.
        set_solver. }
      iDestruct "Hla" as "(Hla & %HC)".

      iPoseProof (state_interp_free with
          "Hla HC Hs_t Hs_s Ha_t Ha_s SI") as "H"; eauto; [ set_solver | .. ].
      { rewrite -elem_of_dom.
        rewrite -Hds. set_solver. }
      iMod "H".

      iDestruct "H" as "(HC & Hs_t & Hs_s & Ha_t & Ha_s & SI)".

      iSpecialize ("IH" with "HC Hs_t Hs_s Ha_t").

      assert (list_to_set mf_s' ∖ {[a]} = (list_to_set mf_s : gset _)).
      { set_solver. }
      rewrite H; clear H.
      Unshelve.
      8-10: try set_solver.
      2 : exact (remove Z.eq_dec x1 mf_t').
      2-6: shelve.

      iSpecialize ("IH" with "Ha_s SI").
      iMod "IH".
      iDestruct "IH" as "(HC & SI)"; iFrame. by cbn -[state_interp].
      Unshelve.
      { clear -Hnd_t'.

        revert x1.
        induction mf_t'; first set_solver.
        cbn.
        apply NoDup_cons in Hnd_t'. destruct Hnd_t' as (?&?).
        intros.
        specialize (IHmf_t' H0). cbn in IHmf_t'.
        destruct (decide (x1 = a)); subst.
        { destruct (Z.eq_dec a a); try done.
          rewrite difference_union_distr_l_L.
          rewrite difference_diag_L.
          rewrite union_empty_l_L. eapply IHmf_t'. }

        { destruct (Z.eq_dec x1 a); try done.
          rewrite difference_union_distr_l_L.
          cbn. rewrite IHmf_t'. set_solver. } } }
  Qed.

  Lemma sim_pop_frame_bij i_t i_s A_t A_s mf_t mf_s C:
    (length i_s > 1 -> length i_t > 1) ->
      list_to_set mf_t = A_t ->
      NoDup mf_t ->
      list_to_set mf_s = A_s ->
      NoDup mf_s ->
    ⊢ stack_tgt i_t -∗
      stack_src i_s -∗
      alloca_tgt i_t A_t -∗
      alloca_src i_s A_s -∗
      checkout C -∗
      ([∗ list] k ↦ l_t; l_s ∈ mf_t; mf_s,
         (l_t, 0%Z) ↔h (l_s, 0%Z) ∗ ⌜C !! (l_t, l_s) = None⌝) -∗
    (r <- trigger LLVMEvents.StackPop ;;
     Tau (trigger MemPop)) ⪯
    (r <- trigger LLVMEvents.StackPop ;;
     Tau (trigger MemPop))
    [{ (x, y), checkout C
          ∗ stack_tgt (List.tl i_t)
          ∗ stack_src (List.tl i_s) }].
  Proof.
    iIntros (Hlen Hs_t Hnd_t Hs_s Hnd_s)
      "HF_t HF_s HA_t HA_s HC #Hbij".
    rewrite sim_expr_eq /sim_expr_.

    iIntros (σ_t σ_s) "SI".
    iDestruct (state_interp_WF with "SI") as %Hwf.

    iDestruct (stack_count_WF_src with "SI HF_s") as "%Hwf_s".
    iDestruct (stack_count_WF_tgt with "SI HF_t") as "%Hwf_t".
    cbn in Hwf_s, Hwf_t.
    destruct Hwf_s as (Hwf_s & Hl_s).
    destruct Hwf_t as (Hwf_t & Hl_t).
    iDestruct (state_interp_alloca_agree with "HF_t HF_s HA_t HA_s SI") as %Hag.
    destruct Hag.

    unfold interp_L2.
    iApply sim_coind_Proper.
    { rewrite bind_trigger.
      solve_eq. cbn. rewrite bind_tau. done. }
    { rewrite bind_trigger.
      solve_eq. cbn. rewrite bind_tau. done. }
    iApply sim_coind_tau.

    destruct (vlocal σ_s) eqn: Hleq_s. cbn -[state_interp].
    destruct l0 eqn: Hl2_s.
    { iApply sim_coind_Proper; [ reflexivity | .. ].
      { do 2 setoid_rewrite bind_vis.
        reflexivity. }
      iApply sim_coind_exc. }

    assert (Hsize_s : length i_s > 1).
    { cbn in *. destruct i_s; subst; cbn in *; try lia. }

    destruct l0.
    { cbn in *.
      destruct i_s; cbn in *; try lia.
      subst. inv Hl2_s. }

    inv Hl2_s. cbn -[state_interp] in *.

    specialize (Hlen Hsize_s).
    destruct (vlocal σ_t) eqn: Hleq_t; cbn -[state_interp].

    destruct l3.
    { cbn in *; destruct i_t; cbn in *; try lia. }

    rewrite !bind_ret_l; iApply sim_coind_tau.
    (* MemPop *)
    destruct (vmem σ_t) eqn: Hmσ_t; destruct (vmem σ_s) eqn: Hmσ_s.
    cbn -[state_interp] in *.
    destruct f.
    { cbn in Hwf_t. lia. }
    destruct f0.
    { cbn in Hwf_s. lia. }

    iPoseProof (frame_stack_and_mem_pop
                  _ _ _ _ _ _ i_t i_s _ _ _ _ _ _ _
                               (ltac:(lia)) (ltac:(lia)) _ _ _ _ Hnd_t Hnd_s
                               (* Hs_t Hs_s Hnd_t Hnd_s *)
                               with "HC Hbij HF_t HF_s HA_t HA_s") as "Ha".
    iDestruct ("Ha" with "SI") as ">(CI & Hst & Hss & SI)".

    cbn -[state_interp].
    rewrite !StateFacts.interp_state_tau.
    iApply sim_coind_tau.
    rewrite !StateFacts.interp_state_vis !bind_tau !bind_bind.
    cbn -[state_interp]. rewrite /free_frame. rewrite Hmσ_t Hmσ_s;
      cbn -[state_interp].
    rewrite !bind_ret_l.
    do 2 iApply sim_coind_tau.
    rewrite !StateFacts.interp_state_ret.

    iApply sim_coind_base.
    cbn -[state_interp].
    iSplitL "SI".
    { iModIntro. Unshelve.
      2 : exact f1.
      2 : exact f2.
      2 : exact p.
      2 : exact p0.
      2: exact f.
      2: exact f0.
      all : eauto.
      rewrite Hleq_s Hleq_t.
      cbn in Hwf. destruct Hwf as (?&?&?&?&?).
      apply NoDup_app in H2, H4. destruct H2, H4.
      rewrite (free_frame_memory_proper f1 mf_t); eauto.
      rewrite (free_frame_memory_proper f2 mf_s); eauto. }
    iFrame. iExists _, _; done.
  Qed.

  Lemma sim_pop_frame_bij_and_own i_t i_s A_t A_s mf_t mf_s C L_t L_s:
    (length i_s > 1 -> length i_t > 1) ->
      list_to_set mf_t ∪ dom L_t = A_t ->
      list_to_set mf_s ∪ dom L_s = A_s ->
      NoDup mf_t ->
      NoDup mf_s ->
      checkout C -∗
      ([∗ list] k ↦ l_t; l_s ∈ mf_t; mf_s,
        (l_t, 0%Z) ↔h (l_s, 0%Z) ∗ ⌜C !! (l_t, l_s) = None ⌝) -∗
      ([∗ map] l ↦ v ∈ L_t,
          l ↦t [ v ] ∗ target_block_size l (Some (logical_block_size v))) -∗
      ([∗ map] l ↦ v ∈ L_s,
          l ↦s [ v ] ∗ source_block_size l (Some (logical_block_size v))) -∗
      stack_tgt i_t -∗
      stack_src i_s -∗
      alloca_tgt i_t A_t -∗
      alloca_src i_s A_s -∗
    (r <- trigger LLVMEvents.StackPop ;;
     Tau (trigger MemPop)) ⪯
    (r <- trigger LLVMEvents.StackPop ;;
     Tau (trigger MemPop))
    [{ (x, y), checkout C
          ∗ stack_tgt (List.tl i_t)
          ∗ stack_src (List.tl i_s) }].
  Proof.
    iIntros (Hlen Hs_t Hs_s Hnd_t Hnd_s)
      "HC #Hl Ht Hs HF_t HF_s HA_t HA_s".
    rewrite sim_expr_eq /sim_expr_.

    iIntros (σ_t σ_s) "SI".
    iDestruct (state_interp_WF with "SI") as %Hwf.

    iDestruct (stack_count_WF_src with "SI HF_s") as "%Hwf_s".
    iDestruct (stack_count_WF_tgt with "SI HF_t") as "%Hwf_t".
    cbn in Hwf_s, Hwf_t.
    destruct Hwf_s as (Hwf_s & Hl_s).
    destruct Hwf_t as (Hwf_t & Hl_t).
    iDestruct (state_interp_alloca_agree with "HF_t HF_s HA_t HA_s SI") as %Hag.
    destruct Hag.

    unfold interp_L2.
    iApply sim_coind_Proper.
    { rewrite bind_trigger.
      rewrite StateFacts.interp_state_vis; cbn. rewrite /add_tau. cbn.
      rewrite bind_tau bind_bind.
      reflexivity. }
    { rewrite bind_trigger.
      rewrite StateFacts.interp_state_vis; cbn. rewrite /add_tau. cbn.
      rewrite bind_tau bind_bind.
      reflexivity. }
    iApply sim_coind_tau.

    destruct (vlocal σ_s) eqn: Hσ_s; cbn -[state_interp].
    destruct l0 eqn: Hl2_s.
    { iApply sim_coind_Proper; [ reflexivity | .. ].
      { cbn. do 2 setoid_rewrite bind_vis.
        reflexivity. }
      iApply sim_coind_exc. }

    assert (Hsize_s : length i_s > 1).
    { cbn in *. destruct i_s; subst; cbn in *; try lia. }

    destruct l0.
    { cbn in *.
      destruct i_s; cbn in *; try lia.
      subst. inv Hl2_s. }

    inv Hl2_s. cbn -[state_interp] in *.
    destruct (vlocal σ_t) eqn: Hσ_t; cbn -[state_interp] in *.
    destruct l3.
    { destruct i_t; cbn in *; try lia. }
    rewrite !bind_ret_l; iApply sim_coind_tau.
    specialize (Hlen Hsize_s).
    cbn.
    (* MemPop *)
    destruct (vmem σ_t) eqn: Hmσ_t; destruct (vmem σ_s) eqn: Hmσ_s.
    cbn -[state_interp] in *.
    destruct f.
    { cbn in Hwf_t. lia. }
    destruct f0.
    { cbn in Hwf_s. lia. }

    iPoseProof (frame_remove_bij_and_own
                  _ _ _ _ _ _ _ _ i_t i_s _ _ _ _ _ _ _ _ _
                  (ltac:(lia)) (ltac:(lia)) _ _ 
                  Hnd_t Hnd_s
                  with "HC Hl Ht Hs HF_t HF_s HA_t HA_s") as "Ha".
    iDestruct ("Ha" with "SI") as ">(CI & Hst & Hss & SI)".

    cbn -[state_interp].
    rewrite !StateFacts.interp_state_tau.
    iApply sim_coind_tau.
    rewrite !StateFacts.interp_state_vis !bind_tau !bind_bind.
    cbn. rewrite Hmσ_t Hmσ_s; cbn.
    rewrite !bind_ret_l.
    do 2 iApply sim_coind_tau.
    rewrite !StateFacts.interp_state_ret.

    iApply sim_coind_base.
    cbn -[state_interp].
    iFrame.
    iSplitL "SI".
    { cbn. rewrite Hσ_t Hσ_s; by iFrame. }
    iExists _, _; by iFrame.
    Unshelve. all : set_solver.
  Qed.

  Lemma alloca_new_frame_target σ_t σ_s i LN:
    NoDup LN.*1 ->
    state_interp σ_t σ_s ∗ stack_tgt i ==∗
    ∃ j,
      state_interp
        (add_frame (fun f => Snoc f []) LN σ_t)
        σ_s
      ∗ stack_tgt (j :: i)
      ∗ alloca_tgt (j :: i) ∅
      ∗ ldomain_tgt (j :: i) (list_to_set LN.*1)
      ∗ ([∗ list] '(l, v) ∈ LN, ![ l := v]t (j :: i)).
  Proof.
    iIntros (Hnodup) "(SI & Hf_t)".
    iDestruct "SI" as (???)
      "(Hh_s & Hh_t & H_c & Hbij & Hg)".

    iCombine "Hh_t Hf_t" as "H".

    iDestruct (allocaS_new_frame with "H") as
      ">(%j & Hh_t & Hf_t & Hs_t & Hd_t & Hl)" ; first done.

    iExists j.

    iFrame.

    rewrite /add_frame;cbn.
    destruct (vmem σ_t).
    destruct (vlocal σ_t).
    repeat iExists _. iFrame.
    cbn; by iFrame.
  Qed.

  Lemma alloca_new_frame_source σ_t σ_s i LN:
    NoDup LN.*1 ->
    state_interp σ_t σ_s ∗ stack_src i ==∗
    ∃ j,
      state_interp
        σ_t
        (add_frame (fun f => Snoc f []) LN σ_s)
      ∗ stack_src (j :: i)
      ∗ alloca_src (j :: i) ∅
      ∗ ldomain_src (j :: i) (list_to_set LN.*1)
      ∗ ([∗ list] '(l, v) ∈ LN, ![ l := v]s (j :: i)).
  Proof.
    iIntros (Hnodup) "(SI & Hf_s)".
    iDestruct "SI" as (???)
      "(Hh_s & Hh_t & H_c & Hbij & Hg)".

    iCombine "Hh_s Hf_s" as "H".

    iDestruct (allocaS_new_frame with "H") as
      ">(%j & Hh_s & Hf_s & Hs_s & Ha_s & Hld_s)"; first done.

    iExists j.

    iFrame.

    rewrite /add_frame;cbn.
    destruct (vmem σ_s).
    destruct (vlocal σ_s).
    repeat iExists _. iFrame.
    cbn; by iFrame.
  Qed.

  Lemma alloca_new_frame σ_t σ_s i_t i_s LN_t LN_s:
    NoDup LN_t.*1 ->
    NoDup LN_s.*1 ->
    state_interp σ_t σ_s
      ∗ stack_tgt i_t
      ∗ stack_src i_s ==∗
    ∃ j_t j_s,
      let i_t' := j_t :: i_t in
      let i_s' := j_s :: i_s in
      state_interp
        (add_frame (fun f => Snoc f []) LN_t σ_t)
        (add_frame (fun f => Snoc f []) LN_s σ_s)
      ∗ stack_tgt i_t'
      ∗ stack_src i_s'
      ∗ alloca_tgt i_t' ∅
      ∗ alloca_src i_s' ∅
      ∗ ldomain_tgt i_t' (list_to_set LN_t.*1)
      ∗ ([∗ list] '(l, v) ∈ LN_t, ![ l := v]t i_t')
      ∗ ldomain_src i_s' (list_to_set LN_s.*1)
      ∗ ([∗ list] '(l, v) ∈ LN_s, ![ l := v]s i_s').
  Proof.
    iIntros (Hnodup_t Hnodup_s) "(SI & Hf_t & Hf_s)".
    iCombine "SI Hf_t" as "H_t".
    iDestruct (alloca_new_frame_target with "H_t")
      as ">(%j & SI & Hf_t & Hs_t & Ha_t & Hd_t)";
      first apply Hnodup_t.

    iCombine "SI Hf_s" as "H_s".
    iDestruct (alloca_new_frame_source with "H_s")
      as ">(%j' & SI & Hf_s & Hs_s & Ha_s & Hd_s)";
      first apply Hnodup_s.

    iExists j, j'.
    by iFrame.
  Qed.

  Lemma sim_push_frame' i_t i_s bs_t bs_s:
    NoDup bs_t.*1 ->
    NoDup bs_s.*1 ->
    stack_tgt i_t
      ∗ stack_src i_s -∗
     r <- trigger MemPush ;;
      _ <- Tau (Ret r);;
      trigger (LLVMEvents.StackPush bs_t) ⪯
     r <- trigger MemPush ;;
      _ <- Tau (Ret r);;
      trigger (LLVMEvents.StackPush bs_s)
    [{ (x, y), ∃ j_t j_s,
       let j_t' := j_t :: i_t in
       let j_s' := j_s :: i_s in
      stack_tgt j_t'
      ∗ stack_src j_s'
      ∗ alloca_tgt j_t' ∅
      ∗ alloca_src j_s' ∅
      ∗ ldomain_tgt j_t' (list_to_set bs_t.*1)
      ∗ ldomain_src j_s' (list_to_set bs_s.*1)
      ∗ ([∗ list] '(l,v) ∈ bs_t, ![ l := v]t j_t')
      ∗ ([∗ list] '(l,v) ∈ bs_s, ![ l := v]s j_s')
    }].
  Proof.
    rewrite sim_expr_eq /sim_expr_.

    (* Some pre-processing *)
    iIntros (Hnodup_t Hnodup_s) "H".
    rewrite /interp_L2.
    iIntros (??) "SI".

    iApply sim_coind_Proper.
    { rewrite bind_trigger. solve_eq. cbn. solve_eq.
      rewrite bind_tau.
      reflexivity. }
    { rewrite bind_trigger. solve_eq. cbn. solve_eq.
      rewrite bind_tau.
      reflexivity. }
    iApply sim_coind_tau.
    rewrite !bind_bind !bind_ret_l.
    iApply sim_coind_tau.
    iApply sim_coind_Proper; [ by solve_eq | by solve_eq | ].
    iApply sim_coind_tau.

    destruct (vlocal σ_t) eqn: Hσ_t.
    destruct (vlocal σ_s) eqn: Hσ_s.
    iApply sim_coind_Proper;
      [ solve_eq; cbn; by solve_eq | solve_eq; cbn; by solve_eq |].
    rewrite !bind_tau Hσ_t Hσ_s.

    iApply sim_coind_tau.
    iApply sim_coind_Proper.
    { cbn; solve_eq. rewrite bind_bind !bind_ret_l; by cbn. }
    { cbn; solve_eq. rewrite bind_bind !bind_ret_l; by cbn. }
    iApply sim_coind_tau.

    iApply sim_coind_Proper;
      [ solve_eq; cbn; by solve_eq | solve_eq; cbn; by solve_eq |].
    iApply sim_coind_base.

    iCombine "SI H" as "H".
    iDestruct (alloca_new_frame with "H") as
      ">(%j_t & %j_s & SI & Hf_t & Hf_s & Ha_t & Ha_s & Hd_t & Hd_s & Hl_t & Hl_s)";
      [apply Hnodup_t | apply Hnodup_s | ]; iFrame.
    rewrite /add_frame. cbn -[state_interp].

    rewrite !foldr_local_env; eauto.
    iModIntro; iFrame.
    iSplitL "SI".
    { cbn. rewrite Hσ_t Hσ_s; cbn.
      destruct (vmem σ_t), (vmem σ_s); cbn. iFrame. }
    iExists _,_; repeat (iSplit; try done).
    iExists _,_; repeat (iSplit; try done); iFrame.
  Qed.

  Lemma sim_push_frame i_t i_s bs_t bs_s:
    NoDup bs_t.*1 ->
    NoDup bs_s.*1 ->
    stack_tgt i_t
      ∗ stack_src i_s -∗
     _ <- trigger MemPush ;;
      trigger (LLVMEvents.StackPush bs_t) ⪯
     _ <- trigger MemPush ;;
      trigger (LLVMEvents.StackPush bs_s)
    [{ (x, y), ∃ j_t j_s,
       let j_t' := j_t :: i_t in
       let j_s' := j_s :: i_s in
      stack_tgt j_t'
      ∗ stack_src j_s'
      ∗ alloca_tgt j_t' ∅
      ∗ alloca_src j_s' ∅
      ∗ ldomain_tgt j_t' (list_to_set bs_t.*1)
      ∗ ldomain_src j_s' (list_to_set bs_s.*1)
      ∗ ([∗ list] '(l, v) ∈ bs_t, ![ l := v]t j_t')
      ∗ ([∗ list] '(l, v) ∈ bs_s, ![ l := v]s j_s')
    }].
  Proof.
    rewrite sim_expr_eq /sim_expr_.

    (* Some pre-processing *)
    iIntros (Hnodup_t Hnodup_s) "H".
    rewrite /interp_L2.
    iIntros (??) "SI".

    iApply sim_coind_Proper.
    { rewrite bind_trigger. solve_eq. cbn. solve_eq.
      rewrite bind_tau.
      reflexivity. }
    { rewrite bind_trigger. solve_eq. cbn. solve_eq.
      rewrite bind_tau.
      reflexivity. }
    iApply sim_coind_tau.
    rewrite !bind_bind !bind_ret_l.
    iApply sim_coind_tau.
    iApply sim_coind_Proper; [ by solve_eq | by solve_eq | ].

    destruct (vlocal σ_t) eqn: Hσ_t.
    destruct (vlocal σ_s) eqn: Hσ_s.
    iApply sim_coind_Proper;
      [ solve_eq; cbn; by solve_eq | solve_eq; cbn; by solve_eq |].
    rewrite !bind_tau Hσ_t Hσ_s.

    iApply sim_coind_tau.
    iApply sim_coind_Proper.
    { cbn; solve_eq. rewrite bind_bind !bind_ret_l; by cbn. }
    { cbn; solve_eq. rewrite bind_bind !bind_ret_l; by cbn. }
    iApply sim_coind_tau.

    iApply sim_coind_Proper;
      [ solve_eq; cbn; by solve_eq | solve_eq; cbn; by solve_eq |].
    iApply sim_coind_base.

    iCombine "SI H" as "H".
    iDestruct (alloca_new_frame with "H") as
      ">(%j_t & %j_s & SI & Hf_t & Hf_s & Ha_t & Ha_s & Hd_t & Hd_s & Hl_t & Hl_s)";
      [apply Hnodup_t | apply Hnodup_s | ]; iFrame.
    rewrite /add_frame. cbn -[state_interp].


    rewrite !foldr_local_env; eauto. iFrame.
    cbn; rewrite Hσ_t Hσ_s; iFrame.
    do 2 sfinal.
  Qed.

End local_properties.
