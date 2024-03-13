(** * Primitive Laws with bijection on locations. *)

From iris.algebra Require Import auth.
From iris.proofmode Require Export proofmode.
From iris.prelude Require Import options.
From iris.program_logic Require Export weakestpre total_weakestpre.
From iris.base_logic.lib Require Export gen_heap gen_inv_heap.
From iris.base_logic Require Export lib.own.

From simuliris.base_logic Require Export gen_sim_prog.
From simuliris.simulation Require Import slsls simulation weakbisim reduction.
From simuliris.vir Require Export vir heap spec primitive_laws.

From ITree Require Import ITree Eq.Eqit Eq.EqAxiom Events.State
     Events.StateFacts Extra.IForest.
From Vellvm Require Import Semantics.LLVMEvents Handlers.Handlers
     Utils.NoFailure Syntax.LLVMAst.

Open Scope Z_scope.
From Equations Require Import Equations.
Set Default Proof Using "Type*".

Section proof.

  Context {Σ} `{!sheapGS Σ, !checkedoutGS Σ, !heapbijGS Σ}.

  (* 4.3.1. Primitive laws using checked-out sets *)
  Lemma sim_bij_return_Some {R1 R2} l_t l_s C (e_t:_ R1) (e_s:_ R2) Φ (q q' qd: Qp) v_t v_s:
    (Qp.le q' 1)%Qp ->
    (q' - q = Some qd)%Qp ->
     C !! (l_t.1, l_s.1) = Some q' ->
     l_t ↔h l_s -∗
     checkout C -∗
     l_t.1 ↦{q}t [v_t] -∗
     l_s.1 ↦{q}s [v_s] -∗
     lb_rel v_t v_s -∗
     (checkout (<[(l_t.1, l_s.1):=qd]> C) -∗ sim_expr Φ e_t e_s) -∗
     sim_expr Φ e_t e_s.
  Proof.
    iIntros (Hle Hb Hc) "Hbij HC Ht Hs Hv H".

    iApply sim_update_si_strong.
    iIntros (??) "SI".

    iDestruct "SI" as (???) "(Hh_s & Hh_t & HC' & Hinv & %WF & SI)".

    iDestruct (ghost_var_agree with "HC HC'") as "%H". subst.
    destruct l_t, l_s; cbn in *.
    iDestruct "Hbij" as "(Hbij & %H1)"; cbn in *; subst.
    iDestruct (heapbij_access with "Hinv Hbij") as "(%Hin & Halloc & Hclose)".

    iDestruct (ghost_var_update_halves with "HC HC'") as ">[HC HC']".

    iPoseProof (heap_read_st_1 with "Hh_s Hs") as "%Hs".

    iFrame.

    iDestruct "Hv" as "#Hv".

    iSplitL "Hh_t Hh_s HC Hclose Halloc Ht Hs"; last first.
    { iApply "H"; iFrame. by iModIntro. }

    (* Re-instate state interpretation *)
    iPoseProof (alloc_rel_add_frac _ _ _ _ _ _ _ _ _ _ _ _ _ Hle Hb Hc with "Halloc Ht Hs Hv Hh_s") as ">Hrem".

    iDestruct "Hrem" as "(Halloc & Hσ_s)".
    iModIntro.

    iExists _, _, _. iFrame.
    iSplitR "".
    { iApply "Hclose"; try done.
      { iPureIntro. intros.
        rewrite lookup_insert_ne; auto. } }
    iPureIntro. set_solver.
  Qed.

  Lemma sim_bij_checkout_Some (q q': Qp) l_t l_s C  {R1 R2} (e_t:st_exprO R1) (e_s: st_exprO R2) Φ
    (σ_t σ_s : vir_state) v_s:
     ✓ q ->
     (q' < 1)%Qp ->
     (q + q' ≤ 1)%Qp ->
     C !! (l_t.1, l_s.1) = Some q' ->
     (vir_heap (σ_s.2)) !! l_s.1 = Some v_s →
     l_t ↔h l_s -∗
     checkout C -∗
     state_interp σ_t σ_s -∗
      (∀ v_s v_t,
          l_t.1 ↦{q}t [ v_t ] -∗
          l_s.1 ↦{q}s [ v_s ] -∗
           lb_rel v_t v_s -∗
          checkout (<[(l_t.1, l_s.1) := (q + q')%Qp]> C) -∗
          state_interp σ_t σ_s ==∗
          sim_coind Φ e_t e_s) ==∗
      sim_coind Φ e_t e_s.
  Proof.
    iIntros (Hle Hq Hq'q Hc Hr) "Hbij HC SI H".

    iDestruct "SI" as (???) "(Hh_s & Hh_t & HC' & Hinv & %WF & SI)".

    iDestruct (ghost_var_agree with "HC HC'") as "%H". subst.
    destruct l_t, l_s.

    iDestruct "Hbij" as "(Hbij & %H1)"; cbn -[state_interp] in *; subst.
    iDestruct (heapbij_access with "Hinv Hbij") as "(%Hin & Halloc & Hclose)".

    iPoseProof
      (alloc_rel_remove_frac _ _ _ _ _ _ _ _ _ _ _ _ _ Hc with "Halloc Hh_s") as
      ">Hrem".
    Unshelve. 2 : exact q. all: eauto.

    iDestruct "Hrem" as (?) "(Hl_t & Hl_s & #Hl & Halloc & Hh_s)".
    iDestruct (ghost_var_update_halves with "HC HC'") as ">[HC HC']".
    iSpecialize ("H" with "Hl_t Hl_s Hl HC").
    iApply "H".

    (* Re-instate state interpretation *)

    repeat iExists _. iFrame.

    iSplitR "".
    { iApply "Hclose"; try done.
      { iPureIntro. intros.
        rewrite lookup_insert_ne; auto. }
      by rewrite Qp.add_comm. }
    iPureIntro. set_solver.
  Qed.

  Lemma sim_bij_return_all {R1 R2} l_t l_s C (e_t:_ R1) (e_s:_ R2) Φ (q : Qp) v_t v_s:
    C !! (l_t.1, l_s.1) = Some q ->
    l_t.1 ↦{q}t [v_t] -∗
    l_s.1 ↦{q}s [v_s] -∗
    lb_rel v_t v_s -∗
     l_t ↔h l_s -∗
     checkout C -∗
    (checkout (base.delete (l_t.1, l_s.1) C) -∗
      e_t ⪯ e_s [{ Φ }]) -∗
      e_t ⪯ e_s [{ Φ }].
  Proof.
    iIntros (Hc) "Hl_t Hl_s Hlr #Hbij HC H".

    iApply sim_update_si_strong.
    iIntros (??) "SI".

    iDestruct "SI" as (???) "(Hh_s & Hh_t & HC' & Hinv & %WF & SI)".

    iDestruct (ghost_var_agree with "HC HC'") as "%H". subst.
    cbn in *. destruct l_t, l_s; cbn in *.

    iDestruct "Hbij" as "(Hbij & %H1)"; cbn in *; subst.
    iDestruct (heapbij_access with "Hinv Hbij") as "(%Hin & Halloc & Hclose)".

    iPoseProof (alloc_rel_add_frac_None q with "Halloc Hl_t Hl_s Hlr") as ">Hrem"; eauto.

    iDestruct (ghost_var_update_halves with "HC HC'") as ">[HC HC']".
    iModIntro. iSpecialize ("H" with "HC"). iFrame.

    repeat iExists _. iFrame.

    iSplitR "".
    { iApply "Hclose"; try done.
      { iPureIntro. intros.
        rewrite lookup_delete_ne; auto. } }
    iPureIntro. set_solver.
  Qed.

  Global Instance lb_rel_persistent v_t v_s :
    Persistent (lb_rel v_t v_s).
  Proof. apply _. Qed.

  From simuliris.utils Require Import tactics.
  Import DenoteTactics.

  Lemma interp_L2_load τ l σ:
    ⟦ load τ (DVALUE_Addr l) ⟧ σ ≅
      let '(g, p, (g0, g1, f)) := σ in
        Tau
          (r <-
            match read (g0, g1, f) l τ with
            | inl s => raiseUB s
            | inr v => Ret (g0, g1, f, v)
            end;;
            Tau (Ret (g, p, r.1, r.2))).
  Proof.
    rewrite /interp_L2.
    setoid_rewrite interp_state_vis.
    setoid_rewrite interp_state_ret.
    setoid_rewrite bind_tau; cbn.
    destruct σ as ((?&?)&(?&?)&?) eqn: H; cbn.
    rewrite bind_bind. apply eqit_Tau.
    eapply eq_itree_clo_bind; first done.
    intros; subst. destruct u2 as (?&?); eauto.
    by setoid_rewrite bind_ret_l; cbn.
  Qed.

  Lemma sim_bij_load_None l_t l_s C τ:
    C !! (l_t.1, l_s.1) = None ->
    l_t ↔h l_s -∗
    checkout C -∗
    load τ (DVALUE_Addr l_t) ⪯ load τ (DVALUE_Addr l_s)
    [{ (v_t, v_s), ∃ v_t v_s q,
        l_t.1 ↦{q}t [ v_t ] ∗ l_s.1 ↦{q}s [ v_s ] ∗
          lb_rel v_t v_s ∗ checkout (<[(l_t.1,l_s.1) := q%Qp]> C) }].
  Proof.
    iIntros (Hc) "#Hl HC".

    rewrite sim_expr_eq /sim_expr_.
    iIntros (σ_t σ_s) "SI".
    cbn -[state_interp].
    rewrite !interp_L2_load.

    destruct σ_t as ((?&?)&(?&?)&?) eqn: Ht; cbn.
    destruct σ_s as ((?&?)&(?&?)&?) eqn: Hs; cbn.

    destruct (read (g3, g4, f0) l_s τ) eqn : Hread.
    (* UB case *)
    { iApply sim_coind_tau.
      rewrite bind_bind bind_vis.
      iApply sim_coind_ub. }

    (* Non-UB : can access the location *)
    apply can_read_allocated in Hread.
    red in Hread; cbn in Hread.
    apply elem_of_dom in Hread.
    destruct Hread as (x & Hread).

    (* Begin CHECKOUT reasoning *)
    iDestruct "SI" as (???) "(Hh_s & Hh_t & HC' & Hinv & %WF & SI)".

    iDestruct (ghost_var_agree with "HC HC'") as "%H". subst.
    cbn in *. destruct l_t, l_s; cbn in *.

    iDestruct "Hl" as "(Hbij & %H1)"; cbn in *; subst.
    iDestruct (heapbij_access with "Hinv Hbij") as
      "(%Hin & Halloc & Hclose)".

    iPoseProof
      (alloc_rel_remove_frac_None1 1 _ _ _ _ _ _ _ _ _ _ _ Hc with "Halloc Hh_s") as ">Hrem"; eauto.

    iDestruct "Hrem" as (??) "(Hl_t & Hl_s & #Hl & Halloc & Hh_s)".
    iDestruct (ghost_var_update_halves with "HC HC'") as ">[HC HC']".

    iDestruct (heap_read_st_1 with "Hh_t Hl_t") as "%Ht".
    iDestruct (heap_read_st_1 with "Hh_s Hl_s") as "%Hs".
    cbn in *.

    destruct v_t, v_s.
    iApply sim_coind_tau.
    rewrite /read; cbn.
    rewrite /get_logical_block /get_logical_block_mem.
    cbn. rewrite Ht.

    rewrite !bind_ret_l; cbn.
    iApply sim_coind_tau.

    iApply sim_coind_base. iFrame.

    iSplitR "Hl_t Hl_s HC"; cycle 1.
    { iExists _, _; do 2 (iSplitL ""; [ done | ]); iFrame.
      iExists (LBlock size bytes concrete_id), _, 1%Qp; by iFrame. }

    repeat iExists _; iFrame.

    iSplitR "".
    { iApply "Hclose"; try done.
      { iPureIntro. intros.
        rewrite lookup_insert_ne; auto. } }
    iPureIntro. set_solver.
    Unshelve. all : eauto.
  Qed.

  Lemma sim_bij_load_None1 l_t l_s C τ:
    dtyp_WF τ ->
    C !! (l_t.1, l_s.1) = None ->
    l_t ↔h l_s -∗
    checkout C -∗
    load τ (DVALUE_Addr l_t) ⪯ load τ (DVALUE_Addr l_s)
    [{ (v_t, v_s), uval_rel v_t v_s ∗ checkout C }].
  Proof.
    iIntros (Hsupp Hc) "#Hl HC".
    iApply sim_null_bij; iIntros "#Hn".
    pose proof (dtyp_WF_size_nonzero _ Hsupp) as Hsz.

    rewrite sim_expr_eq /sim_expr_.
    iIntros (σ_t σ_s) "SI".
    cbn -[state_interp].
    rewrite !interp_L2_load.

    destruct σ_t as ((?&?)&(?&?)&?) eqn: Ht; cbn.
    destruct σ_s as ((?&?)&(?&?)&?) eqn: Hs; cbn.

    destruct (read (g3, g4, f0) l_s τ) eqn : Hread.
    (* UB case *)
    { iApply sim_coind_tau.
      rewrite bind_bind bind_vis.
      iApply sim_coind_ub. }

    assert (Hread_u := Hread).

    (* Non-UB : can access the location *)
    apply can_read_allocated in Hread.
    red in Hread; cbn in Hread.
    apply elem_of_dom in Hread.
    destruct Hread as (x & Hread).

    (* Begin CHECKOUT reasoning *)
    iDestruct "SI" as (???) "(Hh_s & Hh_t & HC' & Hinv & %WF & SI)".

    iDestruct (ghost_var_agree with "HC HC'") as "%H". subst.
    cbn in *. destruct l_t, l_s; cbn in *.

    iDestruct "Hl" as "(Hbij & %H1)"; cbn in *; subst.
    iDestruct (heapbij_access with "Hinv Hbij") as
      "(%Hin & Halloc & Hclose)".

    iPoseProof
      (alloc_rel_remove_frac_None with "Halloc Hh_t Hh_s") as
      ">Hrem"; eauto.

    iDestruct "Hrem" as (??) "(Hl_t & Hl_s & #Hl & Halloc & Hh_t & Hh_s)".
    iDestruct (ghost_var_update_halves with "HC HC'") as ">[HC HC']".

    iPoseProof (alloc_rel_add_frac_None with "Halloc Hl_t Hl_s Hl")
        as "H".
    { by rewrite lookup_insert. }
    iMod "H".
    iModIntro.
    cbn in H.

    cbn in *.

    destruct v_t, x.
    rewrite /read; cbn.
    rewrite /get_logical_block /get_logical_block_mem.
    cbn. rewrite H.

    rewrite !bind_ret_l.
    do 2 iApply sim_coind_tau; cbn.
    iApply sim_coind_base. iFrame.
    iSplitR ""; cycle 1.
    { iExists _, _; do 2 (iSplitL ""; [ done | ]). cbn.
      rewrite /lb_rel.
      iPoseProof (mem_byte_rel_implies_read_rel with "Hn Hl") as "Hrel".
      rewrite /mem_read_rel.
      iSpecialize ("Hrel" $! τ _ Hsupp). cbn.
      rewrite /read in Hread_u. cbn in Hread_u.
      setoid_rewrite Hread in Hread_u; inversion Hread_u.
      iApply "Hrel". }

    repeat iExists _; iFrame.
    iSplitR "".
    { iApply "Hclose"; try done.
      rewrite delete_insert; eauto. }
    iPureIntro. set_solver.
  Qed.

  Lemma sim_bij_load_Some l_t l_s C τ q:
    dtyp_WF τ ->
    (q < 1)%Qp ->
    C !! (l_t.1, l_s.1) = Some q ->
    l_t ↔h l_s -∗
    checkout C -∗
    load τ (DVALUE_Addr l_t) ⪯ load τ (DVALUE_Addr l_s)
    [{ (v_t, v_s), uval_rel v_t v_s ∗ checkout C }].
  Proof.
    iIntros (Hsupp Hq Hc) "#Hl HC".
    iApply sim_null_bij; iIntros "#Hn".
    pose proof (dtyp_WF_size_nonzero _ Hsupp) as Hsz.

    iApply sim_update_si_strong.
    iIntros (??) "SI". iFrame.

    rewrite sim_expr_eq /sim_expr_. clear σ_t σ_s.
    iModIntro. iIntros (σ_t σ_s) "SI".
    rewrite /interp_L2.
    rewrite !interp_state_vis.
    destruct_state σ_s; destruct_state σ_t.
    cbn -[state_interp]. rewrite /add_tau.
    cbn -[state_interp]. rewrite {2}/read.
    destruct (get_logical_block (p, f) l_s.1)
      eqn: Hread; rewrite Hread; cycle 1.
    { cbn. rewrite !bind_tau !bind_bind !bind_vis.
      iApply sim_coind_tau. iApply sim_coind_ub. }

    destruct l3; cbn -[state_interp].
    assert (Hql := Hq).
    rewrite Qp.lt_sum in Hq. destruct Hq.

    iApply (sim_bij_checkout_Some with "Hl HC SI"); eauto; cycle 2.
    Unshelve. 4 : exact x%Qp.
    2 : { rewrite frac_valid.
      rewrite H. apply Qp.le_add_r. }
    2 : { rewrite Qp.add_comm. rewrite H. reflexivity. }

    iIntros (??) "Hl_t Hl_s Hb HC SI".
    iDestruct "SI" as (???) "(Hh_s & Hh_t & HC' & Hinv & %WF & SI)".

    iDestruct (heap_read_st_1 with "Hh_t Hl_t") as "%Ht".
    iDestruct (heap_read_st_1 with "Hh_s Hl_s") as "%Hs".

    rewrite get_logical_block_logical_view in Hs; rewrite Hs in Hread;
      inversion Hread; subst.
    cbn in *.
    destruct v_t.

    rewrite /read /get_logical_block /get_logical_block_mem.
    rewrite Ht. cbn.

    repeat rewrite !bind_ret_l.
    rewrite !bind_tau. iApply sim_coind_tau.
    rewrite !bind_ret_l. iApply sim_coind_tau.
    rewrite !interp_state_ret.

    iDestruct "Hl" as "(Hbij & %H1)"; cbn in *; subst.
    iDestruct (heapbij_access with "Hinv Hbij") as "(%Hin & Halloc & Hclose)".

    iPoseProof "Hb" as "#Hb'".
    iPoseProof "Hb'" as "#Hb".

    iDestruct (ghost_var_agree with "HC HC'") as "%Hceq". subst.
    iPoseProof (alloc_rel_add_frac with "Halloc Hl_t Hl_s Hb Hh_s") as "H";
     [ | | by rewrite lookup_insert | ].
    { rewrite Qp.add_comm -H; reflexivity. }
    { by rewrite Qp.add_comm Qp.add_sub. }
    iDestruct "H" as ">H".
    iDestruct "H" as "(Hrel & Hh_s)".

    iDestruct (ghost_var_update_halves with "HC HC'") as ">[HC HC']".
    iModIntro.
    iApply sim_coind_base. iFrame.
    iSplitR ""; cycle 1.
    { iExists _, _; do 2 (iSplitL ""; [ done | ]). cbn.
      rewrite /lb_rel.
      iPoseProof (mem_byte_rel_implies_read_rel with "Hn Hb") as "Hrel".
      rewrite /mem_read_rel.
      iSpecialize ("Hrel" $! τ l_t.2 Hsupp). rewrite H1; eauto. }

    repeat iExists _; iFrame.
    iSplitR "".
    { iApply "Hclose"; try done.
      { iPureIntro. intros.
        rewrite lookup_insert_ne; auto. }
      rewrite insert_insert insert_id; eauto. }

    iPureIntro. set_solver.
  Qed.

  Open Scope Z_scope.

  Lemma sim_insert_loc_bij {R1 R2} e_t e_s (Φ : _ R1 -> _ R2 -> _) l_t l_s n b_t b_s:
    l_t ↦t [ b_t ] -∗
    l_s ↦s [ b_s ] -∗
    target_block_size l_t n -∗
    source_block_size l_s n -∗
    lb_rel b_t b_s -∗
    ((l_t, 0) ↔h (l_s, 0) -∗ e_t ⪯ e_s [{ Φ }]) -∗
    e_t ⪯ e_s [{ Φ }].
  Proof.
    iIntros "l_t l_s Ht Hs Hlb H".
    iApply sim_update_si.
    iIntros (??) "SI".
    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & %HWF & SI)".
    iPoseProof (heapbij_insert with "Hbij l_t l_s Hlb Ht Hs") as
      ">(Hbij & Hl)".
    iSpecialize ("H" with "Hl"); iFrame.
    iModIntro. repeat iExists _; iFrame.
    iPureIntro; set_solver.
  Qed.

  Lemma interp_L2_store l v σ:
    (⟦ store (DVALUE_Addr l) v ⟧ σ) ≅
      let '(g, p, (g0, g1, f)) := σ in
      Tau
        (r <-
        match write (g0, g1, f) l v with
        | inl x => raise x
        | inr x => Monad.ret x
        end;; Tau (Ret (g, p, r, ()))).
  Proof.
    rewrite /interp_L2.
    setoid_rewrite interp_state_vis.
    setoid_rewrite interp_state_ret.
    setoid_rewrite bind_tau; cbn.
    destruct σ as ((?&?)&(?&?)&?) eqn: H; cbn.
    rewrite !bind_bind.
    do 2 setoid_rewrite bind_ret_l; cbn.
    rewrite /lift_pure_err /lift_err.
    apply eqit_Tau.
    eapply eq_itree_clo_bind; first done.
    intros; subst. destruct u2 as (?&?); eauto.
    done.
  Qed.

  Lemma sim_bij_store l_t l_s C v_t v_s:
    C !! (l_t.1, l_s.1) = None ->
    dval_rel v_t v_s -∗
    l_t ↔h l_s -∗
    checkout C -∗
    store (DVALUE_Addr l_t) v_t ⪯ store (DVALUE_Addr l_s) v_s
    [{ (x_t, x_s), ∃ n_t m_t i_t n_s m_s i_s,
        l_t.1 ↦t [ LBlock n_t (add_all_index (serialize_dvalue v_t) l_t.2 m_t) i_t ] ∗
        l_s.1 ↦s [ LBlock n_s (add_all_index (serialize_dvalue v_s) l_s.2 m_s) i_s ] ∗
          checkout (<[(l_t.1,l_s.1) := 1%Qp]> C) }].
  Proof.
    iIntros (Hc) "#Hval #Hl HC".

    rewrite sim_expr_eq /sim_expr_.
    iIntros (σ_t σ_s) "SI".
    cbn -[state_interp].
    rewrite !interp_L2_store.

    destruct σ_t as ((?&?)&(?&?)&?) eqn: Ht; cbn.
    destruct σ_s as ((?&?)&(?&?)&?) eqn: Hs; cbn.

    destruct (write (g3, g4, f0) l_s v_s) eqn: Hwrite.
    (* ETC case *)
    { iApply sim_coind_tau.
      rewrite bind_bind bind_vis.
      iApply sim_coind_exc. }

    (* Non-EXC: can access the location *)
    pose proof (Hwrite_u := Hwrite).
    apply write_correct in Hwrite.
    destruct Hwrite.

    red in was_allocated0.
    cbn in was_allocated0.
    apply elem_of_dom in was_allocated0.
    destruct was_allocated0 as (x & was_allocated0).

    (* Begin CHECKOUT reasoning *)
    iDestruct "SI" as (???) "(Hh_s & Hh_t & HC' & Hinv & %WF & SI)".

    iDestruct (ghost_var_agree with "HC HC'") as "%H". subst.
    cbn in *. destruct l_t, l_s; cbn in *.
 
    iDestruct "Hl" as "(Hbij & %H1)"; cbn in *; subst.
    iDestruct (heapbij_access with "Hinv Hbij") as
      "(%Hin & Halloc & Hclose)".

    iPoseProof
      (alloc_rel_remove_frac_None1 1 _ _ _ _ _ _ _ _ _ _ _ Hc with "Halloc Hh_s") as ">Hrem"; eauto.

    iDestruct "Hrem" as (??) "(Hl_t & Hl_s & #Hl & Halloc & Hh_s)".

    iDestruct (heap_read_st_1 with "Hh_t Hl_t") as "%Ht".
    iDestruct (heap_read_st_1 with "Hh_s Hl_s") as "%Hs".
    iDestruct (ghost_var_update_halves
                 (<[(l, l1) := 1%Qp]> C0) with "HC HC'")
      as ">[HC HC']".
    destruct v_t0, v_s0.

    iDestruct
      (heap_write1 _ _ _ _ _
          (LBlock size0
             (add_all_index (serialize_dvalue v_s) l2 bytes0) concrete_id0)
                with "Hh_s Hl_s") as ">(Hh_s & Hl_s)".
    iDestruct
      (heap_write1 _ _ _ _ _
          (LBlock size
             (add_all_index (serialize_dvalue v_t) l2 bytes) concrete_id)
        with "Hh_t Hl_t") as ">(Hh_t & Hl_t)".
    cbn in *.

    iApply sim_coind_tau.
    rewrite /write ; cbn.
    rewrite /get_logical_block /get_logical_block_mem.
    cbn. rewrite Ht.

    rewrite !bind_ret_l; cbn.
    iApply sim_coind_tau.

    iApply sim_coind_base.

    rewrite /add_logical_block /add_logical_block_mem.
    iFrame.
    iSplitR "Hl_t Hl_s"; cycle 1.
    { iExists _, _; do 2 (iSplitL ""; [ done | ]); iFrame.
      repeat iExists _; by iFrame. }

    cbn; destruct p0, p; cbn.
    rewrite /write in Hwrite_u. cbn in Hwrite_u.
    setoid_rewrite Hs in Hwrite_u; inversion Hwrite_u; subst.
    rewrite /add_logical_block /add_logical_block_mem; cbn.
    repeat iExists _; iFrame.

    iSplitR "".
    { iApply "Hclose"; try done.
      { iPureIntro. intros.
        rewrite lookup_insert_ne; auto. } }
    iPureIntro. set_solver.
    Unshelve. all : eauto.
  Qed.

  Lemma sim_bij_store1 l_t l_s C v_t v_s τ:
    dtyp_WF τ ->
    dvalue_has_dtyp v_s τ ->
    dvalue_has_dtyp v_t τ ->
    C !! (l_t.1, l_s.1) = None ->
    dval_rel v_t v_s -∗
    l_t ↔h l_s -∗
    checkout C -∗
    store (DVALUE_Addr l_t) v_t ⪯ store (DVALUE_Addr l_s) v_s
    [{ (x_t, x_s), checkout C }].
  Proof.
    iIntros (Hsupp Htyp Hlen Hc) "#Hval #Hl HC".

    rewrite sim_expr_eq /sim_expr_.
    iIntros (σ_t σ_s) "SI".
    cbn -[state_interp].
    rewrite !interp_L2_store.

    destruct σ_t as ((?&?)&(?&?)&?) eqn: Ht; cbn.
    destruct σ_s as ((?&?)&(?&?)&?) eqn: Hs; cbn.

    destruct (write (g3, g4, f0) l_s v_s) eqn: Hwrite.
    (* ETC case *)
    { iApply sim_coind_tau.
      rewrite bind_bind bind_vis.
      iApply sim_coind_exc. }

    (* Non-EXC: can access the location *)
    pose proof (Hwrite_u := Hwrite).
    apply write_correct in Hwrite.
    destruct Hwrite.

    red in was_allocated0.
    cbn in was_allocated0.
    apply elem_of_dom in was_allocated0.
    destruct was_allocated0 as (x & was_allocated0).

    (* Begin CHECKOUT reasoning *)
    iDestruct "SI" as (???) "(Hh_s & Hh_t & HC' & Hinv & %WF & SI)".

    iDestruct (ghost_var_agree with "HC HC'") as "%H". subst.
    cbn in *. destruct l_t, l_s; cbn in *.
 
    iDestruct "Hl" as "(Hbij & %H1)"; cbn in *; subst.
    iDestruct (heapbij_access with "Hinv Hbij") as
      "(%Hin & Halloc & Hclose)".

    iPoseProof
      (alloc_rel_remove_frac_None1 1 _ _ _ _ _ _ _ _ _ _ _ Hc with "Halloc Hh_s") as ">Hrem"; eauto.

    iDestruct "Hrem" as (??) "(Hl_t & Hl_s & #Hl & Halloc & Hh_s)".

    iDestruct (heap_read_st_1 with "Hh_t Hl_t") as "%Ht".
    iDestruct (heap_read_st_1 with "Hh_s Hl_s") as "%Hs".
    iDestruct (ghost_var_update_halves C0 with "HC HC'")
      as ">[HC HC']".
    destruct v_t0, v_s0.

    iDestruct
      (heap_write1 _ _ _ _ _
          (LBlock size0
             (add_all_index (serialize_dvalue v_s) l2 bytes0) concrete_id0)
                with "Hh_s Hl_s") as ">(Hh_s & Hl_s)".
    iDestruct
      (heap_write1 _ _ _ _ _
          (LBlock size
             (add_all_index (serialize_dvalue v_t) l2 bytes) concrete_id)
        with "Hh_t Hl_t") as ">(Hh_t & Hl_t)".
    cbn in *.

    iApply sim_coind_tau.
    rewrite /write ; cbn.
    rewrite /get_logical_block /get_logical_block_mem.
    cbn. rewrite Ht.

    rewrite !bind_ret_l; cbn.
    iApply sim_coind_tau.

    iApply sim_coind_base.

    iPoseProof (mem_byte_rel_write_stable with "Hl Hval")
                 as "Hrel".
    iPoseProof (alloc_rel_add_frac_None with
                 "Halloc Hl_t Hl_s Hrel") as "H"; eauto.
    { by rewrite lookup_insert. }
    iDestruct "H" as ">H".
    rewrite delete_insert; eauto.

    rewrite /add_logical_block /add_logical_block_mem.
    iFrame.
    iSplitR ""; cycle 1.
    { cbn. iExists _, _; eauto. }

    cbn; destruct p0, p; cbn.
    rewrite /write in Hwrite_u. cbn in Hwrite_u.
    setoid_rewrite Hs in Hwrite_u; inversion Hwrite_u; subst.
    rewrite /add_logical_block /add_logical_block_mem; cbn.
    repeat iExists _; iFrame.

    iSplitR "".
    { iApply "Hclose"; try done. }
    iPureIntro. set_solver.
    Unshelve. all : eauto.
  Qed.

  Lemma sim_new_blocks_loc_bij {R1 R2}
    e_t e_s (Φ : _ R1 -> _ R2 -> _) l_t l_s n dt:
    l_t ↦t [ make_empty_logical_block dt ] -∗
    l_s ↦s [ make_empty_logical_block dt ] -∗
    target_block_size l_t n -∗
    source_block_size l_s n -∗
    ((l_t, 0) ↔h (l_s, 0) -∗ e_t ⪯ e_s [{ Φ }]) -∗
    e_t ⪯ e_s [{ Φ }].
  Proof.
    iIntros "l_t l_s Ht Hs H".
    iApply sim_update_si.
    iIntros (??) "SI".
    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & %HWF & SI)".
    iPoseProof (lb_rel_empty_blocks dt) as "Hempty".
    iPoseProof (heapbij_insert with "Hbij l_t l_s Hempty Ht Hs") as
      ">(Hbij & Hl)".
    iSpecialize ("H" with "Hl"); iFrame.
    iModIntro. repeat iExists _; iFrame.
    iPureIntro; set_solver.
  Qed.

  Lemma call_readonly C dt args_t args_s u_t u_s i_t i_s:
    attribute_interp (ExternalCall dt u_t args_t [FNATTR_Readonly])
                   (ExternalCall dt u_s args_s [FNATTR_Readonly]) C ->
    frame_WF i_t i_s -∗
    stack_tgt i_t -∗
    stack_src i_s -∗
    checkout C -∗
    dval_rel u_t u_s -∗
    ([∗ list] x;y ∈ args_t; args_s, uval_rel x y) -∗
    trigger (ExternalCall dt u_t args_t [FNATTR_Readonly]) ⪯
    trigger (ExternalCall dt u_s args_s [FNATTR_Readonly])
    [{ (v_t,v_s), stack_tgt i_t ∗ stack_src i_s ∗ uval_rel v_t v_s ∗ checkout C }].
  Proof.
    intros Hcall.
    iIntros "#WF Hs_t Hs_s Hc #Haddr Hargs".
    rewrite sim_expr_eq /sim_expr_.

    iIntros (σ_t σ_s) "SI".
    unfold interp_L2.
    iApply sim_coindF_Proper.
    { eapply lift_expr_rel_Φ_Proper. }
    - setoid_rewrite interp_state_vis.
      setoid_rewrite interp_state_ret. reflexivity.
    - setoid_rewrite interp_state_vis.
      setoid_rewrite interp_state_ret. reflexivity.
    - iApply sim_coindF_coind_bind.
      iApply sim_coindF_vis. iRight.
      iFrame.
      iModIntro. cbn -[attribute_interp].
      rewrite /resum /ReSum_id /id_ /Id_IFun.
      simp handle_call_events.
      cbn -[attribute_interp]. simp vir_call_ev.
      iRight.
      iDestruct "Hargs" as "#Hargs".
      iExists (C, i_t, i_s); iFrame.
      iSplitL "Hc Hs_t Hs_s".
      { simp vir_call_ev; iFrame; do 5 (iSplitL ""; eauto); iFrame. }
      iIntros (??). destruct v_t, v_s; simp vir_call_ans.
      iIntros "H"; iFrame.
      iApply sim_coindF_base. cbn.
      iApply sim_coindF_tau.
      iApply sim_coindF_base.
      iModIntro.
      cbn. unfold lift_expr_rel.
      iExists _,_,_,_.
      do 2 (iSplitL ""; [ auto | ]).
      unfold state_interp. cbn.
      simp vir_call_ans.
      iDestruct "H" as "(H1&H2&Hst&Hss&Hv)"; iFrame.
      iExists _,_; repeat (iSplitL""; first done); iFrame.
  Qed.

  Lemma call_readonly_internal C dt args_t args_s u_t u_s i_t i_s:
    attribute_interp (ExternalCall dt u_t args_t [FNATTR_Readonly])
                     (ExternalCall dt u_s args_s [FNATTR_Readonly]) C ->
    frame_WF i_t i_s -∗
    stack_tgt i_t -∗
    stack_src i_s -∗
    checkout C -∗
    dval_rel u_t u_s -∗
    ([∗ list] x;y ∈ args_t; args_s, uval_rel x y) -∗
    trigger (ExternalCall dt u_t args_t [FNATTR_Internal; FNATTR_Readonly]) ⪯
    trigger (ExternalCall dt u_s args_s [FNATTR_Internal; FNATTR_Readonly])
    [{ (v_t,v_s), stack_tgt i_t ∗ stack_src i_s ∗ uval_rel v_t v_s ∗ checkout C }].
  Proof.
    intros Hcall.
    iIntros "#WF Hst Hss Hc #Haddr Hargs".
    rewrite sim_expr_eq /sim_expr_.

    iIntros (σ_t σ_s) "SI".
    unfold interp_L2.
    iApply sim_coindF_Proper.
    { eapply lift_expr_rel_Φ_Proper. }
    - setoid_rewrite interp_state_vis.
      setoid_rewrite interp_state_ret. reflexivity.
    - setoid_rewrite interp_state_vis.
      setoid_rewrite interp_state_ret. reflexivity.
    - iApply sim_coindF_coind_bind.
      iApply sim_coindF_vis. iRight.
      iFrame.
      iModIntro. cbn -[attribute_interp].
      rewrite /resum /ReSum_id /id_ /Id_IFun.
      simp handle_call_events.
      cbn -[attribute_interp]. simp vir_call_ev.
      iRight. iExists (C, i_t, i_s); iFrame.
      iDestruct "Hargs" as "#Hargs".
      iSplitL "Hc Hst Hss".
      { simp vir_call_ev. iFrame. repeat (iSplitL ""; eauto). }
      iIntros (??). destruct v_t, v_s; simp vir_call_ans.
      iIntros "H"; iFrame.
      iApply sim_coindF_base. cbn.
      iApply sim_coindF_tau.
      iApply sim_coindF_base.
      iModIntro.
      cbn. unfold lift_expr_rel.
      iExists _,_,_,_.
      do 2 (iSplitL ""; [ auto | ]).
      unfold state_interp. cbn.
      simp vir_call_ans.
      iDestruct "H" as "(H1&H2)"; iFrame.
      iDestruct "H2" as "(HC & Hst & Hss & Hv)".
      iExists _,_; repeat (iSplitL""; first done); iFrame.
  Qed.


  Import DenoteTactics.

  Lemma stack_count_WF_src σ_t σ_s F:
    state_interp σ_t σ_s -∗
    stack_src F -∗
    ⌜frame_count σ_s.2.2 = (length F) /\ length (vir_local_stack σ_s) = length (tail F)⌝.
  Proof.
    iIntros "SI Hs".
    iDestruct "SI" as (???) "(Hh_s & _)".
    destruct_HC "Hh_s".

    iDestruct (ghost_var_agree with "HCF Hs") as %H; subst.
    iDestruct (big_sepL2_length with "HSA") as %H'.

    iPureIntro.
    destruct Hwf as (?&?&?&?); eauto.
  Qed.

  Lemma stack_count_WF_tgt σ_t σ_s F:
    state_interp σ_t σ_s -∗
    stack_tgt F -∗
    ⌜frame_count σ_t.2.2 = (length F) /\ length (vir_local_stack σ_t) = length (tail F)⌝.
  Proof.
    iIntros "SI Ht".
    iDestruct "SI" as (???) "(_ & Hh_t & _)".
    destruct_HC "Hh_t".

    iDestruct (ghost_var_agree with "HCF Ht") as %H; subst.
    iDestruct (big_sepL2_length with "HSA") as %H'.

    iPureIntro.
    destruct Hwf as (?&?&?&?); eauto.
  Qed.

  Lemma state_interp_alloca_agree
      i_t i_s mf_t mf_s A_t A_s g_t g_s l_t l_s h_t h_s:
    stack_tgt i_t -∗
    stack_src i_s -∗
    alloca_tgt i_t A_t -∗
    alloca_src i_s A_s -∗
    state_interp (g_t, l_t, (h_t, mf_t))
                 (g_s, l_s, (h_s, mf_s)) -∗
    ⌜list_to_set (peek_frame mf_t) = A_t /\
      list_to_set (peek_frame mf_s) = A_s⌝.
  Proof.
    iIntros "Hs_t Hs_s Ha_t Ha_s SI".

    iDestruct "SI" as (???) "(Hh_s & Hh_t & _)".
    iDestruct (heap_ctx_alloca_agree with "Hs_t Ha_t Hh_t") as %Ha_t.
    iDestruct (heap_ctx_alloca_agree with "Hs_s Ha_s Hh_s") as %Ha_s.
    done.
  Qed.

  Lemma state_interp_free i_t i_s g_t g_s l_t l_s
    (h_t h_s : heap * gset Z) f_t f_s C
    (mf_t' mf_s' : list Z) (l_t0 l_s0 : Z):
    l_t0 ∈ (list_to_set mf_t' : gset _) ->
    l_s0 ∈ (list_to_set mf_s' : gset _) ->
    is_Some (h_s.1 !! l_s0) ->
    C !! (l_t0, l_s0) = None ->
    (l_t0, 0) ↔h (l_s0, 0) -∗
    checkout C -∗
    stack_tgt i_t -∗
    stack_src i_s -∗
    alloca_tgt i_t (list_to_set mf_t') -∗
    alloca_src i_s (list_to_set mf_s') -∗
    state_interp
      (g_t, l_t, (h_t, Snoc f_t mf_t'))
      (g_s, l_s, (h_s, Snoc f_s mf_s')) ==∗
    checkout C ∗
    stack_tgt i_t ∗
    stack_src i_s ∗
    alloca_tgt i_t (list_to_set mf_t' ∖ {[ l_t0 ]}) ∗
    alloca_src i_s (list_to_set mf_s' ∖ {[ l_s0 ]}) ∗
    state_interp
      (g_t, l_t,
        ((delete l_t0 h_t.1, h_t.2), Snoc f_t (remove Z.eq_dec l_t0 mf_t')))
      (g_s, l_s,
        ((delete l_s0 h_s.1, h_s.2), Snoc f_s (remove Z.eq_dec l_s0 mf_s'))).
  Proof.
    iIntros (Hin_t Hin_s Hsome Hc)
      "#Hbij HC Hs_t Hs_s Ha_t Ha_s SI".
    iDestruct "SI" as (???) "(Hh_s & Hh_t & HC' & Hinv & %WF & SI)".
    iDestruct (ghost_var_agree with "HC HC'") as "%H". subst.

    iDestruct "Hbij" as "(Hbij & %H1)"; cbn in *; subst.
    iDestruct (heapbij_access with "Hinv Hbij") as "(%Hin & Halloc & Hclose)".

    iDestruct
      (alloc_rel_free with "Hs_t Hs_s Ha_t Ha_s Halloc Hh_t Hh_s") as
      ">(Halloc & Hs_t & Hs_s & Ha_t & Ha_s & Hh_t & Hh_s)";
      eauto.
    iFrame.
    destruct l_s, l_t; cbn.

    repeat iExists _; iFrame.
    iSplitR "".
    { iApply "Hclose"; eauto. }
    set_solver.
  Qed.

  Lemma free_frame_empty γ i (m m' : memory) (mf mf': frame_stack) g L S :
    (1 < length i)%nat ->
      free_frame (m, mf) = inr (m', mf') ->
      heap.stack γ i
      ∗ heap_ctx γ (⊙ (m, mf), vir_dyn (m, mf)) mf g L S
      ∗ allocaS γ (current_frame i) ∅
      ==∗
    heap_ctx γ (⊙ (m, mf), vir_dyn (m, mf)) mf g L S ∗
      heap.stack γ i
        ∗ allocaS γ (current_frame i) ∅.
  Proof.
    iIntros (Hlen Hf) "(HFr & Hσ & Ha)".
    rewrite /free_frame in Hf.
    destruct mf; inversion Hf; subst; cbn -[frame_at].
    destruct_HC "Hσ".

    (* Update allocaS set *)
    rewrite allocaS_eq /allocaS_def.

    iDestruct (ghost_var_agree with "HFr HCF") as %H'; subst.
    iDestruct (ghost_var_agree with "HA Ha") as %H'; subst.

    cbn in H'. destruct f eqn: Hf_; last set_solver.
    pose proof (Hwf' := Hwf).
    destruct Hwf. cbn in H0. inversion H0; clear H0. clear Hf.

    iFrame.

    cbn.
    iExists cf, hF; iFrame.
    cbn. iFrame.

    iPureIntro; split; eauto; split; eauto.
  Qed.

  Lemma state_interp_WF
      g_t l_t h_t f_t g_s l_s h_s f_s lenv_t lenv_s:
    state_interp (g_t, (l_t, lenv_t), (h_t, f_t))
                 (g_s, (l_s, lenv_s), (h_s, f_s)) -∗
    ⌜NoDup l_t.*1 /\ NoDup (flatten_frame_stack f_t) /\
      NoDup l_s.*1 /\ NoDup (flatten_frame_stack f_s) /\
      list_to_set (flatten_frame_stack f_t) = dom h_t.1 /\
      list_to_set (flatten_frame_stack f_s) = dom h_s.1⌝.
  Proof.
    iDestruct 1 as (???) "(Hh_s & Hh_t & H_c & Hbij & %HWF & SI)".
    destruct_HC "Hh_s".
    cbn in Hbs. rewrite /vir_heap /vir_dyn in Hbs Hwf.
    cbn in Hbs, Hwf.
    cbn in Hdup.
    destruct Hwf as (?&?&?).

    iDestruct "Hh_t" as (cf' hF')
      "(Hσ_t&Hb_t&HCF_t&HA_t&HL_t&HD_t&HSA_t&HG_t&%Hdup_t&%Hbs_t&
        %Hwf)".
    iPureIntro.
    cbn in Hbs_t. rewrite /vir_heap /vir_dyn in Hbs_t Hwf.
    cbn in Hbs_t, Hwf.
    cbn in Hdup_t.
    destruct Hwf as (?&?&?); auto.
    repeat (split; eauto).
  Qed.

  Open Scope nat_scope.

  Lemma frame_mem_remove_bij (mf_t mf_s : mem_frame) A_t A_s mf_t' mf_s'
    i_t i_s g_t g_s l_t l_s h_t h_s f_t f_s C:
    1 < length i_t ->
    1 < length i_s ->
    list_to_set mf_t ⊆ A_t ->
    list_to_set mf_s ⊆ A_s ->
    NoDup mf_t ->
    NoDup mf_s ->
    checkout C -∗
    ([∗ list] k ↦ l_t; l_s ∈ mf_t; mf_s,
       (l_t, 0%Z) ↔h (l_s, 0%Z) ∗ ⌜C !! (l_t, l_s) = None ⌝) -∗
    stack_tgt i_t -∗
    stack_src i_s -∗
    alloca_tgt i_t A_t -∗
    alloca_src i_s A_s -∗
    state_interp (g_t, l_t, (h_t, Snoc f_t mf_t'))
                 (g_s, l_s, (h_s, Snoc f_s mf_s')) ==∗
    checkout C ∗
    stack_tgt i_t ∗
    stack_src i_s ∗
    alloca_tgt i_t (A_t ∖ list_to_set mf_t) ∗
    alloca_src i_s (A_s ∖ list_to_set mf_s) ∗
    state_interp
      (g_t, l_t, (free_frame_memory mf_t h_t, Snoc f_t
                  (free_locations_from_frame mf_t' mf_t)))
      (g_s, l_s, (free_frame_memory mf_s h_s,
                   Snoc f_s
                  (free_locations_from_frame mf_s' mf_s))).
  Proof.
    iIntros (Hlen_t Hlen_s Hf_t Hf_s Hnodup_t Hnodup_s) "HC #Hl Hs_t Hs_s Ha_t Ha_s SI".
    iDestruct (state_interp_alloca_agree with "Hs_t Hs_s Ha_t Ha_s SI") as %HA.
    destruct HA as (HA_t&HA_s); cbn in HA_t, HA_s.
    rewrite /free_frame_memory.

    iInduction mf_s as [ | ] "IH" forall
        (mf_t mf_t' mf_s' f_t f_s h_t h_s A_s A_t
           HA_t HA_s Hf_s Hf_t Hnodup_t);
      cbn -[state_interp] in *.
    { iDestruct (big_sepL2_nil_inv_r with "Hl") as %Hl; subst.
      iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & %HWF & SI)".
      iDestruct (ghost_var_agree with "HC H_c") as "%HC". subst.
      rewrite !difference_empty_L.
      iFrame. iExists C0, S, G; iFrame.
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

      assert (Heq: list_to_set mf_s ⊆ (list_to_set mf_s' ∖ {[a]} : gset _)).
      { set_solver. }
      rewrite -list_to_set_delete_from_frame in Heq.

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
      Unshelve.
      8-10: try set_solver.
      2 : exact (remove Z.eq_dec x1 mf_t').
      6 : by apply list_to_set_remove.
      2-5: shelve.

      rewrite list_to_set_remove; auto.
      iSpecialize ("IH" with "Ha_s SI").
      iMod "IH".
      iDestruct "IH" as
        "(HC & Hs_t & Hs_s & Ha_t & Ha_s & SI)"; iFrame.
      cbn -[state_interp].
      rewrite /free_locations_from_frame.
      assert (Hat :
          list_to_set mf_t' ∖ {[x1]} ∖ list_to_set l1' =
          list_to_set mf_t' ∖ ({[x1]} ∪ (list_to_set l1' : gset _))).
      { set_solver. }
      rewrite Hat; clear Hat.

      assert (Has : list_to_set mf_s' ∖ {[a]} ∖ list_to_set mf_s =
        list_to_set mf_s' ∖ ({[a]} ∪ (list_to_set mf_s : gset _))).
      { set_solver. }
      rewrite Has; clear Has. by iFrame. }
  Qed.

  Corollary frame_mem_remove_bij_all
    (mf_t mf_s : mem_frame) A_t A_s mf_t' mf_s'
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
    state_interp (g_t, l_t, (h_t, Snoc f_t mf_t'))
                 (g_s, l_s, (h_s, Snoc f_s mf_s')) ==∗
    checkout C ∗
    stack_tgt i_t ∗
    stack_src i_s ∗
    alloca_tgt i_t ∅ ∗
    alloca_src i_s ∅ ∗
    state_interp
      (g_t, l_t, (free_frame_memory mf_t' h_t, Snoc f_t nil))
      (g_s, l_s, (free_frame_memory mf_s' h_s, Snoc f_s nil)).
  Proof.
    iIntros (Hlen_t Hlen_s Hf_t Hf_s Hnodup_t Hnodup_s) "HC #Hl Hs_t Hs_s Ha_t Ha_s SI".
    iPoseProof (state_interp_WF with "SI") as "%HWF".
    iPoseProof (state_interp_alloca_agree with
                 "Hs_t Hs_s Ha_t Ha_s SI") as "%Hag".
    iPoseProof
      (frame_mem_remove_bij with
        "HC Hl Hs_t Hs_s Ha_t Ha_s SI") as ">H";
      eauto; [ set_solver | set_solver | ].
    assert (HAt: A_t ∖ list_to_set mf_t = ∅).
    { set_solver. }
    rewrite HAt.

    assert (HAs: A_s ∖ list_to_set mf_s = ∅).
    { set_solver. }
    rewrite HAs.
    cbn in Hag. destruct Hag.

    destruct HWF as (_&?&_&?&_).
    cbn in H1; apply NoDup_app in H1, H2; destruct H1, H2.
    subst. rewrite !free_locations_from_frame_all; auto.
    rewrite (free_frame_memory_proper mf_s mf_s'); eauto.
    rewrite (free_frame_memory_proper mf_t mf_t'); eauto.
  Qed.

  Lemma free_frame_empty1 γ i (m : memory) (mf : frame_stack) g L S :
    (1 < length i)%nat ->
      heap.stack γ i
      ∗ heap_ctx γ (⊙ (m, Snoc mf nil), vir_dyn (m, Snoc mf nil)) (Snoc mf nil) g L S
      ∗ allocaS γ (current_frame i) ∅
      ==∗
    heap_ctx γ (⊙ (free_frame_memory [] m, mf), vir_dyn (free_frame_memory [] m, mf)) mf g
    (hd L S) (tl S) ∗
      heap.stack γ (tail i)
        ∗ allocaS γ (current_frame i) ∅.
  Proof.
    iIntros (Hlen) "(HFr & Hσ & Ha)".
    destruct_HC "Hσ".

    (* Update allocaS set *)
    rewrite allocaS_eq /allocaS_def.

    iDestruct (ghost_var_agree with "HFr HCF") as %H'; subst.
    iDestruct (ghost_var_agree with "HA Ha") as %H'; subst.

    cbn in H'.

    iFrame.
    destruct cf.
    { cbn in Hlen. lia. }

    destruct cf.
    { cbn in Hlen. lia. }

    iDestruct (ghost_var_update_halves (f0 :: cf) with "HFr HCF") as ">[HFr HCF]".
    iFrame.

    cbn.
    iExists (f0 :: cf), _; iFrame.
    iPoseProof (big_sepL2_cons_inv_l with "HSA") as "HSA".
    iDestruct "HSA" as (???) "((Hf & Hd & Hdup & Ha) & HSA)"; subst.

    cbn. iFrame.

    destruct Hwf. cbn in *.
    destruct H0 as (?&?&?&?).
    iPureIntro; split; eauto; split; eauto.
    cbn; repeat (split; eauto).
    intros. specialize (H3 (S n) (ltac:(lia))).
    cbn in H3. done.
  Qed.


End proof.
