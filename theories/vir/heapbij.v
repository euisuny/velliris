(** * Library for defining a bijection between source and target heaps

    This file provides the ghost state for establishing a bijection
    between source and target heaps.  *)

From iris.algebra Require Import auth.
From iris.base_logic.lib Require Import ghost_map ghost_var gset_bij.
From iris.algebra.lib Require Import gset_bij.

From Vellvm Require Import Syntax.DynamicTypes Utils.Util.

From velliris.base_logic Require Import gen_sim_heap gen_sim_prog.
From velliris.program_logic Require Import program_logic.
From velliris.vir Require Export vir vir_state base val_rel.

From iris.prelude Require Import options.
Set Default Proof Using "Type*".
Import uPred.

Open Scope Z_scope.

Class sheapGS (Σ: gFunctors) := SHeapGS {
  sheapG_heapG :> heapG Σ | 1;
  sheapG_heap_target : heap_names;
  sheapG_heap_source : heap_names;
}.

Class sheapGpreS (Σ: gFunctors) := SHeapGpreS {
  sbij_pre_heapG :> heapG Σ | 10;
}.
Definition sheapΣ := #[heapΣ].
#[global] Instance subG_sheapΣ Σ :
  subG sheapΣ Σ -> sheapGpreS Σ.
Proof. solve_inG. Qed.

Lemma sheap_init `{sheapGpreS Σ} gs_t gs_s:
  ⊢@{iPropI Σ} |==>
    ∃ (_: sheapGS Σ),
      heap_ctx sheapG_heap_target (gmap_empty, gset_empty)
        (Handlers.MemTheory.Mem.Singleton []) gs_t [] [] ∗
      heap_ctx sheapG_heap_source (gmap_empty, gset_empty)
        (Handlers.MemTheory.Mem.Singleton []) gs_s [] [] ∗
      own (sheapG_heap_target.(heap_name))
        (◯ (to_heap (gmap_empty : heap))) ∗
      ([∗ map] k↦v ∈ (gmap_empty : gmap loc (option nat)),
        k ↪[heap_block_size_name sheapG_heap_target] v) ∗
      own (globals_name sheapG_heap_target)
        (to_agree (gs_t) : agreeR (leibnizO global_env)) ∗
      own (sheapG_heap_source.(heap_name))
        (◯ (to_heap (gmap_empty : heap))) ∗
      ([∗ map] k↦v ∈ (gmap_empty : gmap loc (option nat)),
        k ↪[heap_block_size_name sheapG_heap_source] v) ∗
      own (globals_name sheapG_heap_source)
        (to_agree (gs_s) : agreeR (leibnizO global_env)) ∗
      (∃ γf : frame_names,
          ghost_var (stack_name sheapG_heap_target) (1 / 2) [γf] ∗
          ([∗ map] k↦v ∈ gmap_empty, k ↪[local_name γf] v) ∗
          ghost_var (ldomain_name γf) (1 / 2)
            (gset_empty : gset local_loc) ∗
          ghost_var (allocaS_name γf) (1 / 2)
            (gset_empty : gset Z)) ∗
      (∃ γf : frame_names,
          ghost_var (stack_name sheapG_heap_source) (1 / 2) [γf] ∗
          ([∗ map] k↦v ∈ gmap_empty, k ↪[local_name γf] v) ∗
          ghost_var (ldomain_name γf) (1 / 2)
            (gset_empty : gset local_loc) ∗
          ghost_var (allocaS_name γf) (1 / 2)
            (gset_empty : gset Z)).
Proof.
  iMod (heap_init gs_t) as (??) "(?&?&H&?&H1)".
  iMod (heap_init gs_s) as (??) "(?&?&H'&?&H2)".
  iExists (SHeapGS _ _ γ γ0); iFrame.
  iSplitL "H".
  { cbn. iModIntro; done. }
  iSplitL "H'".
  { cbn. iModIntro; done. }
  iSplitL "H1".
  { iModIntro. iExists γf. cbn.
    iDestruct "H1" as "(?&?&?&?)"; by iFrame. }
  iModIntro. iExists γf0. cbn.
    iDestruct "H2" as "(?&?&?&?)"; by iFrame.
Qed.

(* ------------------------------------------------------------------------ *)

Notation "l ↦s v" := (mapsto_dval sheapG_heap_source l 1 v)
                      (at level 20, format "l  ↦s  v") : bi_scope.
Notation "l ↦t v" := (mapsto_dval sheapG_heap_target l 1 v)
                      (at level 20, format "l  ↦t  v") : bi_scope.
Notation "l ↦{ q }s v" := (mapsto_dval sheapG_heap_source l q v)
                      (at level 20, format "l  ↦{ q }s  v") : bi_scope.
Notation "l ↦{ q }t v" := (mapsto_dval sheapG_heap_target l q v)
                            (at level 20, format "l  ↦{ q }t  v") : bi_scope.

Notation "l ↦s [ b ]" := (vir_state.mapsto sheapG_heap_source l 1 b)
                      (at level 20, format "l  ↦s  [ b ]") : bi_scope.
Notation "l ↦t [ b ]" := (vir_state.mapsto sheapG_heap_target l 1 b)
                      (at level 20, format "l  ↦t  [ b ]") : bi_scope.

Notation "l ↦{ q }s [ b ]" := (vir_state.mapsto sheapG_heap_source l q b)
                      (at level 20, format "l  ↦{ q }s  [ b ]") : bi_scope.
Notation "l ↦{ q }t [ b ]" := (vir_state.mapsto sheapG_heap_target l q b)
                      (at level 20, format "l  ↦{ q }t  [ b ]") : bi_scope.

Notation "[ l := v ]s i" := (lmapsto sheapG_heap_source (current_frame i) l v)
                      (at level 20, format "[  l  :=  v  ]s  i") : bi_scope.
Notation "[ l := v ]t i" := (lmapsto sheapG_heap_target (current_frame i) l v)
                      (at level 20, format "[  l  :=  v  ]t  i") : bi_scope.

Notation target_block_size l := (heap_block_size sheapG_heap_target l 1).
Notation source_block_size l := (heap_block_size sheapG_heap_source l 1).

Notation target_globals := (globals sheapG_heap_target).
Notation source_globals := (globals sheapG_heap_source).

Notation ldomain_tgt i := (ldomain sheapG_heap_target (current_frame i)).
Notation ldomain_src i := (ldomain sheapG_heap_source (current_frame i)).

Notation alloca_tgt i := (allocaS sheapG_heap_target (current_frame i)).
Notation alloca_src i := (allocaS sheapG_heap_source (current_frame i)).

Notation stack_tgt := (stack sheapG_heap_target).
Notation stack_src := (stack sheapG_heap_source).

(* ------------------------------------------------------------------------ *)
(** *Checked out resources *)

Class checkedoutGS (Σ : gFunctors) := CheckedOutGS {
  checkedoutG :> ghost_varG Σ (gmap (loc * loc) frac);
  checkedoutG_bij_name : gname;
}.
Class checkedoutGpreS (Σ: gFunctors) := CheckedOutGpreS {
  scheckedout_pre_progG :> ghost_varG Σ (gmap (loc * loc) frac);
}.
Definition checkedoutΣ := #[ghost_varΣ (gmap (loc * loc) frac)].
Global Instance subG_checkedoutΣ (Σ: gFunctors):
  subG checkedoutΣ Σ → checkedoutGpreS Σ.
Proof. solve_inG. Qed.

Section checkedout.

  Context {Σ : gFunctors}.

  Definition checkout `{checkedoutGS Σ} (C : gmap (loc * loc) frac) :=
    ghost_var checkedoutG_bij_name (1/2) C.

End checkedout.

Lemma checkedout_init `{!checkedoutGpreS Σ} C:
  ⊢@{iPropI Σ} |==> ∃ _: checkedoutGS Σ, checkout C ∗ checkout C.
Proof.
  iMod (ghost_var_alloc C) as (γ) "H".
  iModIntro.
  iExists (CheckedOutGS _ _ γ); iFrame.
  rewrite -Qp.half_half.
  iPoseProof (ghost_var_split with "H") as "[H1 H2]"; iFrame.
Qed.

(* ------------------------------------------------------------------------ *)

Class vellirisGS (Σ : gFunctors) := VellirisGS {
  velliris_heapbijGS :> heapbijGS Σ;
  velliris_sheapGS :> sheapGS Σ;
  velliris_checkedoutGS :> checkedoutGS Σ;
}.

Class vellirisGpreS Σ := {
  velliris_pre_heapbijG :> heapbijGpreS Σ;
  velliris_pre_sheapG :> sheapGpreS Σ;
  velliris_pre_checkedoutG :> checkedoutGpreS Σ;
}.

Definition vellirisΣ := #[heapbijΣ; sheapΣ; checkedoutΣ].

(* ------------------------------------------------------------------------ *)
Section heapbij_definition.

  Context `{!sheapGS Σ, !heapbijGS Σ}.

  (* Refinement of values *)
  Definition lb_rel (v_t v_s : logical_block) : iPropI Σ :=
    mem_byte_rel (lb_mem v_t) (lb_mem v_s).
  (* Treat memory blocks as if it is an array storing [dvalue] elements, where
      index [i] of the array has value [v] written to it.

      If it is contained in the checkout set [C], the blocks are leaked to an
      external source. *)
  Definition alloc_rel (l_t l_s : loc) (C : gmap (loc * loc) frac) : iProp Σ :=
    (∃ n v_t v_s,
        (match n with
        | Some _ =>
          ∃ (q : option frac), ⌜C !! (l_t, l_s) = q⌝ ∗
          match q with
            | Some q =>
                match (1 - q)%Qp with
                  | Some q' =>
                      l_t ↦{q'}t [ v_t ] ∗
                      l_s ↦{q'}s [ v_s ] ∗
                      lb_rel v_t v_s
                  | None => True
                end
            | None =>
                l_t ↦t [ v_t ] ∗
                l_s ↦s [ v_s ] ∗
                lb_rel v_t v_s
          end
        | None => True
        end) ∗
        target_block_size l_t n ∗
        source_block_size l_s n).

  Definition heapbij_interp (L : gset (loc * loc)) C :=
    (heapbij_auth L ∗ [∗ set] p ∈ L, let '(b_t, b_s) := p in alloc_rel b_t b_s C)%I.

End heapbij_definition.

Lemma heapbij_init `{!heapbijGpreS Σ, !sheapGS Σ} P:
  ⊢ |==> ∃ `(heapbijGS Σ), heapbij_interp ∅ P.
Proof.
  iMod (gset_bij_own_alloc ∅) as (γbij) "[Hbij _]".
  { apply: gset_bijective_empty. }
  iIntros "!>". iExists (HeapBijGS _ _ γbij).
  rewrite /heapbij_interp /heapbij_auth /heapbijG_bij_name; iFrame.
  iSplitL "Hbij"; [ iApply "Hbij" | ].
  iApply big_sepS_empty. done.
Qed.

From Vellvm Require Import Handlers.Handlers.
Import LLVMEvents.


Section alloc_rel_properties.

  Context `{!vellirisGS Σ}.

  (* Simple properties of [lb_rel] *)
  Lemma empty_mem_block_lookup τ k n:
    lookup k (make_empty_mem_block τ) = Some n -> n = SUndef.
  Proof.
    rewrite /make_empty_mem_block.
    remember (sizeof_dtyp τ); clear Heqn0.
    destruct n0; [ done | ]; cbn.
    remember (BinPosDef.Pos.to_nat (p - 1)); clear Heqn0.
    clear τ p.
    revert k n.
    induction n0; cbn; eauto.
    { intros; subst; cbn in *.
      destruct (decide (0 = k)) eqn: Hk.
      { subst; rewrite lookup_insert in H; by inversion H. }
      { rewrite lookup_insert_ne in H; eauto.
        done. } }
    { intros.
      destruct (decide ((S n0 : Z) = k)%Z) eqn: Hk.
      { subst; rewrite lookup_insert in H; by inversion H. }
      { rewrite lookup_insert_ne in H; eauto. } }
  Qed.

  Remark lb_rel_empty_blocks τ:
    ⊢ lb_rel (make_empty_logical_block τ) (make_empty_logical_block τ).
  Proof.
    rewrite /lb_rel.
    cbn. rewrite /mem_byte_rel.
    iSplit; [ | done].
    iIntros (???); iExists _; iSplit; [ done | ].
    apply empty_mem_block_lookup in H; by subst.
  Qed.

  (* Properties about [alloc_rel] *)
  Lemma alloc_rel_read_None C b_t b_s σ_s σ_t v G mf L LS :
    σ_s.1 !! b_s = Some v →
    C !! (b_t, b_s) = None ->
    alloc_rel b_t b_s C -∗
    heap_ctx sheapG_heap_source σ_s mf G L LS -∗
    heap_ctx sheapG_heap_target σ_t mf G L LS -∗
    ∃ v', ⌜σ_t.1 !! b_t = Some v'⌝ ∗ lb_rel v' v.
  Proof.
    iIntros (? HP).
    iDestruct 1 as (? vs_t vs_s) "(Hl_s & Hb_t & Hb_s)" .
    iIntros "Hσ_s Hσ_t".
    iDestruct (heap_ctx_block_size with "Hσ_s Hb_s") as %Hb; eauto.
    destruct n; inversion Hb; last done; clear Hb H0.

    iDestruct "Hl_s" as (??) "Hl_s"; subst.
    rewrite HP.
    iDestruct "Hl_s" as "(Hl_t & Hl_s & Hl)".
    iDestruct (heap_read_st_1 with "Hσ_s Hl_s") as %Hl_s.
    iDestruct (heap_read_st_1 with "Hσ_t Hl_t") as %Hl_t.
    simplify_eq/=. rewrite H in Hl_s; inversion Hl_s; subst.
    iExists _. iFrame. done.
  Qed.

  Lemma alloc_rel_read b_t b_s σ_s σ_t v G q q' mf L LS C:
    σ_s.1 !! b_s = Some v →
    C !! (b_t, b_s) = Some q ->
    (1 - q = Some q')%Qp ->
    alloc_rel b_t b_s C -∗
    heap_ctx sheapG_heap_source σ_s mf G L LS -∗
    heap_ctx sheapG_heap_target σ_t mf G L LS -∗
    ∃ v', ⌜σ_t.1 !! b_t = Some v'⌝ ∗ lb_rel v' v.
  Proof.
    iIntros (? HP).
    iDestruct 1 as (? vs_t vs_s) "(Hl_s & Hb_t & Hb_s)".

    iIntros "Hσ_s Hσ_t".
    iDestruct (heap_ctx_block_size with "Hσ_s Hb_s") as %Hb; eauto.
    destruct n; inversion Hb; last done; clear Hb H1.

    iDestruct "Hl_s" as (??) "Hl_s"; subst.
    rewrite HP. rewrite H0.
    iDestruct "Hl_s" as "(Hl_t & Hl_s & Hl)".
    iDestruct (heap_read_st_1 with "Hσ_s Hl_s") as %Hl_s.
    iDestruct (heap_read_st_1 with "Hσ_t Hl_t") as %Hl_t.
    simplify_eq/=. rewrite H in Hl_s; inversion Hl_s; subst.
    iExists _. iFrame. done.
  Qed.

  Lemma alloc_rel_write C b_t b_s σ_s σ_t v v_s' v_t' mf G L LS:
    σ_s.1 !! b_s = Some v →
    C !! (b_t, b_s) = None ->
    alloc_rel b_t b_s C -∗
    heap_ctx sheapG_heap_source σ_s mf G L LS -∗
    heap_ctx sheapG_heap_target σ_t mf G L LS -∗
    lb_rel v_t' v_s' ==∗
    alloc_rel b_t b_s C ∗
    heap_ctx sheapG_heap_source (<[b_s := v_s']> σ_s.1, σ_s.2) mf G L LS ∗
    heap_ctx sheapG_heap_target (<[b_t := v_t']> σ_t.1, σ_t.2) mf G L LS.
  Proof.
    iIntros (? HP).
    iDestruct 1 as (n vs_t vs_s) "(Hl_s & Hb_t & Hb_s)".
    iIntros "Hσ_s Hσ_t Hval".
    iDestruct (heap_ctx_block_size with "Hσ_s Hb_s") as %Hb; eauto.
    destruct n; inversion Hb; last done; clear Hb H0.

    iDestruct "Hl_s" as (??) "Hl_s".
    rewrite H0 in HP; subst. rewrite HP; cbn.
    iDestruct "Hl_s" as "(Hl_t & Hl_s & Hv)".

    iDestruct (heap_read_st_1 with "Hσ_s Hl_s") as %Hl_s.
    iDestruct (heap_read_st_1 with "Hσ_t Hl_t") as %Hl_t.
    simplify_eq/=.

    iMod (heap_write with "Hσ_s Hl_s") as "[$ Hl_s]".
    iMod (heap_write with "Hσ_t Hl_t") as "[$ Hl_t]".
    iModIntro.
    iExists _, _, _; iFrame.
    iExists _; iSplitL ""; [ done | ]. cbn. iFrame.
  Qed.

  Lemma alloc_rel_remove_frac q qr b_t b_s σ_s v_s C mf G L LS:
    (qr + q ≤ 1)%Qp ->
    σ_s.1 !! b_s = Some v_s →
    C !! (b_t, b_s) = Some q ->
    alloc_rel b_t b_s C -∗
    heap_ctx sheapG_heap_source σ_s mf G L LS
    ==∗
    ∃ v_t,
      b_t↦{qr}t [ v_t ] ∗
      b_s↦{qr}s [ v_s ] ∗ lb_rel v_t v_s ∗
      alloc_rel b_t b_s (<[(b_t, b_s) := (q + qr)%Qp]>C) ∗
      heap_ctx sheapG_heap_source σ_s mf G L LS.
  Proof.
    iIntros (Hq Hc).
    iDestruct 1 as (vs_t vs_s q'') "(Hl & Hb_t & Hb_s)".
    iIntros "Hσ_s".
    iDestruct (heap_ctx_block_size with "Hσ_s Hb_s") as %Hb; eauto.
    destruct vs_t; inversion Hb; last done; clear Hb H0.

    iDestruct "Hl" as (? HC) "Hl".
    rewrite HC in H. subst. rewrite H.
    apply add_le_sub_r_Some' in Hq.
    destruct Hq as [Hq | Hq].
    { destruct Hq as (?&Hq); rewrite Hq.

      iDestruct "Hl" as "(Hl_t & Hl_s & #Hv)".
      iDestruct (heap_read_st_1 with "Hσ_s Hl_s") as %?; simplify_eq/=.
      rewrite Hc in H0; inversion H0; subst.

      iExists _. iFrame.
      iDestruct "Hl_t" as "(Hl_t1 & Hl_t2)".
      iDestruct "Hl_s" as "(Hl_s1 & Hl_s2)".
      iModIntro; iFrame. iSplitL ""; [done | ].
      iExists (Some n), vs_s, q''.
      rewrite lookup_insert; iFrame.
      iExists _; iSplit; [done|]; cbn; iFrame.

      assert (1 - (q + qr) = Some x0)%Qp.
      { rewrite Qp.sub_Some in Hq; rewrite Hq.
        rewrite Qp.add_assoc.
        rewrite Qp.add_comm.
        apply Qp.add_sub. }
      rewrite H1; by iFrame. }

    { rewrite Hq Qp.add_sub.

      iDestruct "Hl" as "(Hl_t & Hl_s & #Hv)".
      iDestruct (heap_read_st_1 with "Hσ_s Hl_s") as %?; simplify_eq/=.
      rewrite Hc in H0; inversion H0; subst.

      iExists _. iFrame.
      iModIntro; iFrame. iSplitL ""; [done | ].
      iExists (Some n), vs_s, vs_s.
      rewrite lookup_insert; iFrame.
      rewrite -Hq; iFrame.
      iExists _; iSplit; [done|]; cbn; iFrame.

      assert (1 - (q + qr) = None)%Qp.
      { rewrite Qp.add_comm. rewrite -Hq. apply Qp.sub_None.
        reflexivity. }
      by rewrite H1. }
  Qed.

  Lemma alloc_rel_remove_frac_None1 q b_t b_s σ_s C mf G L LS v_s:
    (Qp.le q 1)%Qp ->
    σ_s.1 !! b_s = Some v_s →
    C !! (b_t, b_s) = None ->
    alloc_rel b_t b_s C -∗
    heap_ctx sheapG_heap_source σ_s mf G L LS
    ==∗
    ∃ v_t v_s,
      b_t↦{q}t [ v_t ] ∗
      b_s↦{q}s [ v_s ] ∗ lb_rel v_t v_s ∗
      alloc_rel b_t b_s (<[(b_t, b_s) := q]>C) ∗
      heap_ctx sheapG_heap_source σ_s mf G L LS.
  Proof.
    iIntros (Hq Hσ Hc).
    iDestruct 1 as (? vs_t vs_s) "(Hl & Hb_t & Hb_s)".
    iIntros "Hσ_s".
    iDestruct (heap_ctx_block_size with "Hσ_s Hb_s") as %Hb; eauto.
    destruct n; inversion Hb; last done; clear Hb H.

    iDestruct "Hl" as (q'' HC) "Hl".

    rewrite Hc in HC. subst.
    iDestruct "Hl" as "(Hl_t & Hl_s & #Hv)".
    iDestruct (heap_read_st_1 with "Hσ_s Hl_s") as %?; simplify_eq/=.

    iExists _, _. iFrame.

    apply Qp.le_lteq in Hq. destruct Hq; subst; iFrame; cycle 1.
    { iSplitL ""; [ done | ].
      repeat iExists _.
      rewrite lookup_insert; iFrame.
      iModIntro. iExists _; iSplit; [done|]; cbn; iFrame.
      by rewrite Qp.sub_diag. }

    destruct (1 - q)%Qp eqn : Hq; cycle 1.
    { apply Qp.sub_None in Hq.
      apply Qp.lt_nge in H0. done. }
    apply Qp.sub_Some in Hq; rewrite Hq.
    iDestruct "Hl_t" as "(Hl_t1 & Hl_t2)".
    iDestruct "Hl_s" as "(Hl_s1 & Hl_s2)".
    iModIntro; iFrame.
    iSplitL ""; [ done | ].
    repeat iExists _.
    rewrite lookup_insert; iFrame.
    rewrite -Hq; iFrame.
    iExists _; iSplit; [done|]; cbn; iFrame.

    apply Qp.sub_Some in Hq; rewrite Hq; by iFrame.
    Unshelve. all : eauto.
  Qed.

  Lemma alloc_rel_remove_frac_None q b_t b_s σ_t σ_s v_s C mf G L LS mf_t G_t L_t LS_t:
    (Qp.le q 1)%Qp ->
    σ_s.1 !! b_s = Some v_s →
    C !! (b_t, b_s) = None ->
    alloc_rel b_t b_s C -∗
    heap_ctx sheapG_heap_target σ_t mf_t G_t L_t LS_t -∗
    heap_ctx sheapG_heap_source σ_s mf G L LS
    ==∗
      ∃ v_t, ⌜σ_t.1 !! b_t = Some v_t⌝ ∗
      b_t↦{q}t [ v_t ] ∗
      b_s↦{q}s [ v_s ] ∗ lb_rel v_t v_s ∗
      alloc_rel b_t b_s (<[(b_t, b_s) := q]>C) ∗
      heap_ctx sheapG_heap_target σ_t mf_t G_t L_t LS_t ∗
      heap_ctx sheapG_heap_source σ_s mf G L LS.
  Proof.
    iIntros (Hq Hlu1 Hc).
    iDestruct 1 as (? vs_t vs_s) "(Hl & Hb_t & Hb_s)".
    iIntros "Hσ_t Hσ_s".
    iDestruct (heap_ctx_block_size with "Hσ_s Hb_s") as %Hb; eauto.
    destruct n; inversion Hb; last done; clear Hb H x.

    iDestruct "Hl" as (q'' HC) "Hl".

    rewrite Hc in HC. subst.
    iDestruct "Hl" as "(Hl_t & Hl_s & #Hv)".
    iDestruct (heap_read_st_1 with "Hσ_s Hl_s") as %?; simplify_eq/=.
    iDestruct (heap_read_st_1 with "Hσ_t Hl_t") as %?; simplify_eq/=.
    rewrite H in Hlu1; inversion Hlu1; subst.

    iFrame.
    iExists _; iSplitL ""; first done.

    apply Qp.le_lteq in Hq. destruct Hq; subst; iFrame; cycle 1.
    { iSplitL ""; [ done | ].
      rewrite /heap_ctx.
      repeat iExists _.
      rewrite lookup_insert; iFrame.
      iModIntro. iExists _; iSplit; [done|]; cbn; iFrame.
      by rewrite Qp.sub_diag. }

    destruct (1 - q)%Qp eqn : Hq; cycle 1.
    { apply Qp.sub_None in Hq.
      apply Qp.lt_nge in H1. done. }
    apply Qp.sub_Some in Hq; rewrite Hq.
    iDestruct "Hl_t" as "(Hl_t1 & Hl_t2)".
    iDestruct "Hl_s" as "(Hl_s1 & Hl_s2)".
    iModIntro; iFrame.
    iSplitL ""; [ done | ].
    repeat iExists _.
    rewrite lookup_insert; iFrame.
    rewrite -Hq; iFrame.
    iExists _; iSplit; [done|]; cbn; iFrame.

    apply Qp.sub_Some in Hq; rewrite Hq; by iFrame.
    Unshelve. all : eauto.
  Qed.

  Lemma alloc_rel_remove_frac_None_tgt
    q b_t b_s σ_t σ_s v_t C mf G L LS mf_t G_t L_t LS_t:
    (Qp.le q 1)%Qp ->
    σ_t.1 !! b_t = Some v_t →
    C !! (b_t, b_s) = None ->
    alloc_rel b_t b_s C -∗
    heap_ctx sheapG_heap_target σ_t mf_t G_t L_t LS_t -∗
    heap_ctx sheapG_heap_source σ_s mf G L LS
    ==∗
      ∃ v_s, ⌜σ_s.1 !! b_s = Some v_s⌝ ∗
      b_t↦{q}t [ v_t ] ∗
      b_s↦{q}s [ v_s ] ∗ lb_rel v_t v_s ∗
      alloc_rel b_t b_s (<[(b_t, b_s) := q]>C) ∗
      heap_ctx sheapG_heap_target σ_t mf_t G_t L_t LS_t ∗
      heap_ctx sheapG_heap_source σ_s mf G L LS.
  Proof.
    iIntros (Hq Hlu1 Hc).
    iDestruct 1 as (? vs_t vs_s) "(Hl & Hb_t & Hb_s)".
    iIntros "Hσ_t Hσ_s".
    iDestruct (heap_ctx_block_size with "Hσ_t Hb_t") as %Hb; eauto.
    destruct n; inversion Hb; last done; clear Hb H x.

    iDestruct "Hl" as (q'' HC) "Hl".

    rewrite Hc in HC. subst.
    iDestruct "Hl" as "(Hl_t & Hl_s & #Hv)".
    iDestruct (heap_read_st_1 with "Hσ_s Hl_s") as %?; simplify_eq/=.
    iDestruct (heap_read_st_1 with "Hσ_t Hl_t") as %?; simplify_eq/=.
    rewrite H0 in Hlu1; inversion Hlu1; subst.

    iFrame.
    iExists _; iSplitL ""; first done.

    apply Qp.le_lteq in Hq. destruct Hq; subst; iFrame; cycle 1.
    { iSplitL ""; [ done | ].
      rewrite /heap_ctx.
      repeat iExists _.
      rewrite lookup_insert; iFrame.
      iModIntro. iExists _; iSplit; [done|]; cbn; iFrame.
      by rewrite Qp.sub_diag. }

    destruct (1 - q)%Qp eqn : Hq; cycle 1.
    { apply Qp.sub_None in Hq.
      apply Qp.lt_nge in H1. done. }
    apply Qp.sub_Some in Hq; rewrite Hq.
    iDestruct "Hl_t" as "(Hl_t1 & Hl_t2)".
    iDestruct "Hl_s" as "(Hl_s1 & Hl_s2)".
    iModIntro; iFrame.
    iSplitL ""; [ done | ].
    repeat iExists _.
    rewrite lookup_insert; iFrame.
    rewrite -Hq; iFrame.
    iExists _; iSplit; [done|]; cbn; iFrame.

    apply Qp.sub_Some in Hq; rewrite Hq; by iFrame.
    Unshelve. all : eauto.
  Qed.

  Lemma alloc_rel_free σ_s σ_t b_t b_s C mf_t G_t L_t LS_t mf_s G_s L_s LS_s
        mf_t' mf_s' i_t i_s:
    b_t ∈ (list_to_set mf_t' : gset _) ->
    b_s ∈ (list_to_set mf_s' : gset _) ->
    is_Some (σ_s.1 !! b_s) ->
    C !! (b_t, b_s) = None ->
    stack_tgt i_t -∗
    stack_src i_s -∗
    alloca_tgt i_t (list_to_set mf_t') -∗
    alloca_src i_s (list_to_set mf_s') -∗
    alloc_rel b_t b_s C -∗
    heap_ctx sheapG_heap_target σ_t mf_t G_t L_t LS_t -∗
    heap_ctx sheapG_heap_source σ_s mf_s G_s L_s LS_s
    ==∗
    alloc_rel b_t b_s C ∗
    stack_tgt i_t ∗
    stack_src i_s ∗
    alloca_tgt i_t (list_to_set mf_t' ∖ {[ b_t ]}) ∗
    alloca_src i_s (list_to_set mf_s' ∖ {[ b_s ]}) ∗
    heap_ctx sheapG_heap_target (delete b_t σ_t.1, σ_t.2)
        (delete_from_frame_stack mf_t b_t) G_t L_t LS_t ∗
    heap_ctx sheapG_heap_source (delete b_s σ_s.1, σ_s.2)
        (delete_from_frame_stack mf_s b_s) G_s L_s LS_s.
  Proof.
    iIntros (Hin_t Hin_s ? HP) "Hs_t Hs_s Ha_t Ha_s".
    iDestruct 1 as (? vs_t vs_s) "(Hl_s & Hb_t & Hb_s)" .
    iIntros "Hσ_t Hσ_s".
    iDestruct (heap_ctx_block_size with "Hσ_s Hb_s") as %Hb; eauto.
    destruct n; inversion Hb; last done; clear Hb H0.

    iDestruct "Hl_s" as (??) "Hl_s"; subst.
    rewrite HP.
    iDestruct "Hl_s" as "(Hl_t & Hl_s & Hl)".
    destruct vs_t.
    iCombine "Hσ_t Hl_t Ha_t Hs_t Hb_t" as "H".
    iMod (heap_free1 with "H") as "(Hfree_t & Hh_t & Ha_t & Hs_t)"; auto.
    iCombine "Hσ_s Hl_s Ha_s Hs_s Hb_s" as "H".
    iMod (heap_free1 with "H") as "(Hfree_s & Hh_s & Ha_s & Hs_s)"; auto.
    iFrame.
    rewrite /alloc_rel.
    iExists None, (LBlock size bytes concrete_id), vs_s; by iFrame.
  Qed.

  Lemma alloc_rel_add_frac (q : Qp) q' qd b_t b_s σ_s v_s v_t C mf G L LS:
    (Qp.le q' 1)%Qp ->
    (q' - q = Some qd)%Qp ->
    C !! (b_t, b_s) = Some q' ->
    alloc_rel b_t b_s C -∗
    b_t ↦{q}t [ v_t ] -∗
    b_s ↦{q}s [ v_s ] -∗
    lb_rel v_t v_s -∗
    heap_ctx sheapG_heap_source σ_s mf G L LS ==∗
    alloc_rel b_t b_s (<[(b_t, b_s) := qd]> C)
      ∗ heap_ctx sheapG_heap_source σ_s mf G L LS.
  Proof.
    intros Hb bounds1.
    iDestruct 1 as (? vs_t vs_s) "(Hl & Hb_t & Hb_s)".
    iIntros "Hl_t Hl_s Hv Hσ_s".
    destruct n.
    { iDestruct "Hl" as (qd' HC) "Hl".

      iDestruct (heap_read_st_1 with "Hσ_s Hl_s") as %Hl_s.
      rewrite H in HC; inversion HC; subst. cbn.

      iFrame. rewrite /alloc_rel.
      destruct (1 - q')%Qp eqn: Hq'.
      { iDestruct "Hl" as "(Hp1 & Hp2 & Hv')".
        iDestruct (mapsto_bytes_agree with "[$Hp1 $Hl_t]") as %->.
        iDestruct (mapsto_bytes_agree with "[$Hp2 $Hl_s]") as %->.

        iExists _, _, _. rewrite lookup_insert; iFrame.
        iModIntro; iExists _; iSplitL ""; [ done | ]. cbn.

        rewrite bounds1.
        assert (1 - qd = Some (q + q0))%Qp.
        { rewrite Qp.sub_Some. rewrite Qp.sub_Some in Hq'.
          rewrite Hq'. rewrite Qp.sub_Some in bounds1.
          rewrite bounds1.
          rewrite Qp.add_assoc.
          rewrite (Qp.add_comm q qd).
          by rewrite -Qp.add_assoc. }
        rewrite H1.

        iDestruct (heap_mapsto_combine_0 with "Hl_t Hp1") as "$". iFrame.
        iDestruct (heap_mapsto_combine_0 with "Hl_s Hp2") as "$". }

      { iExists _, _, _. rewrite lookup_insert; iFrame.
        iModIntro; iExists _; iSplitL ""; [ done | ]. cbn.

        assert (1 - qd = Some q)%Qp.
        { rewrite Qp.sub_Some. rewrite Qp.sub_None in Hq'.
          rewrite Qp.sub_Some in bounds1. rewrite bounds1 in Hq'.
          rewrite Qp.add_comm.
          apply Qp.le_lteq in Hq'.
          destruct Hq'.
          { rewrite bounds1 in Hb.
            exfalso.
            by apply Qp.le_ngt in Hb. }
          done. }
        rewrite bounds1 H1; iFrame. } }
    { iModIntro; iFrame.
      iExists None; by iFrame. }
  Qed.

  Lemma alloc_rel_add_frac_None
    (q : Qp) b_t b_s C v_t v_s:
    C !! (b_t, b_s) = Some q ->
    alloc_rel b_t b_s C -∗
    b_t ↦{q}t [ v_t ] -∗
    b_s ↦{q}s [ v_s ] -∗
    lb_rel v_t v_s ==∗
    alloc_rel b_t b_s (base.delete (b_t, b_s) C).
  Proof.
    intros Hb.
    iDestruct 1 as (? vs_t vs_s) "(Hl & Hb_t & Hb_s)".
    destruct n.
    { iDestruct "Hl" as (q'' HC) "Hl".

      iIntros "Hl_t Hl_s Hrel".
      rewrite HC in Hb; inversion Hb; subst.

      iFrame. rewrite /alloc_rel.
      destruct (1 - q)%Qp eqn: Hq'; eauto.
      { iDestruct "Hl" as "(Hp1 & Hp2 & Hv')".
        iDestruct (mapsto_bytes_agree with "[$Hp1 $Hl_t]") as %->.
        iDestruct (mapsto_bytes_agree with "[$Hp2 $Hl_s]") as %->.

        iExists _, _, _. rewrite lookup_delete; iFrame.
        iModIntro; iExists _; iSplitL ""; [ done | ]. cbn.

        iDestruct (heap_mapsto_combine_0 with "Hl_t Hp1") as "Hl_t".
        iDestruct (heap_mapsto_combine_0 with "Hl_s Hp2") as "Hl_s".
        apply Qp.sub_Some in Hq'. rewrite -Hq'. iFrame. }

      { iExists _, _, _. rewrite lookup_delete; iFrame.
        iModIntro; iExists _; iSplitL ""; [ done | ]. cbn.
        iDestruct (mapsto_valid with "Hl_t") as %Ht.
        rewrite frac_valid in Ht.
        assert (q = 1)%Qp.
        { apply Qp.sub_None in Hq'. by apply le_eq. }
        rewrite H0; iFrame. } }
    { iIntros "Ht Hs Hb". iExists None; by iFrame. }
  Qed.

  Lemma alloc_rel_mono C C' b_t b_s:
    (∀ q, C !! (b_t, b_s) = q → C' !! (b_t, b_s) = q) →
    alloc_rel b_t b_s C -∗
    alloc_rel b_t b_s C'.
  Proof.
    iIntros (HP).
    iDestruct 1 as (? vs_t vs_s) "(Hl & Hb_t & Hb_s)".
    destruct n.
    { iDestruct "Hl" as (q'' HC) "Hl".
      iExists _, _, _. iFrame.
      iExists _; iFrame.
      iPureIntro; by apply HP. }
    { iExists _, _, _. by iFrame. }
    Unshelve. all: eauto.
  Qed.

End alloc_rel_properties.

Section laws.
  Context `{!heapbijGS Σ, !sheapGS Σ, !checkedoutGS Σ}.
  Implicit Types (b_t b_s : loc) (l_t l_s : loc).

  Lemma heapbij_access L C b_t b_s:
    heapbij_interp L C -∗
    block_rel b_t b_s -∗
    ⌜(b_t, b_s) ∈ L⌝ ∗
    alloc_rel b_t b_s C ∗
    (∀ C',
        ⌜∀ b_t' b_s', (b_t', b_s') ≠ (b_t, b_s) ->
            C !! (b_t', b_s') = C' !! (b_t', b_s')⌝ -∗
        alloc_rel b_t b_s C' -∗ heapbij_interp L C').
  Proof.
    iIntros "Hinv Hrel". iDestruct "Hinv" as "(Hauth & Hheap)".
    iDestruct (gset_bij_elem_of with "Hauth Hrel") as %Hin.
    iPoseProof (big_sepS_delete with "Hheap") as "[He Hheap]"; first done.
    iDestruct (gset_bij_own_valid with "Hauth") as %[_ Hbij].
    iFrame. iSplit; [done|].
    iIntros (P' HP) "Halloc". iFrame.
    iApply big_sepS_delete; first done. iFrame.
    iApply (big_sepS_impl with "Hheap").
    iIntros "!>" ([??] Hin2) "Halloc".
    iApply (alloc_rel_mono with "Halloc") => ?? /=.
    set_unfold. destruct Hin2 as [Hin2 Hneq].
    have ?:= gset_bijective_eq_iff _ _ _ _ _ _ Hin Hin2.
    rewrite -HP; eauto.
  Qed.

  Lemma heapbij_insert L C l_t l_s v_t v_s n:
    heapbij_interp L C -∗
    l_t ↦t [ v_t ] -∗
    l_s ↦s [ v_s ] -∗
    lb_rel v_t v_s -∗
    target_block_size l_t n -∗
    source_block_size l_s n ==∗
    heapbij_interp ({[(l_t, l_s)]} ∪ L) C ∗
    (l_t, 0) ↔h (l_s, 0).
  Proof.
    iIntros "Hinv Ht Hs Hrel Ha_t Ha_s".
    iDestruct "Hinv" as "(Hauth & Hheap)".

    iAssert ((¬ ⌜set_Exists (λ '(b_t', b_s'), l_t = b_t') L⌝)%I) as "%Hext_t".
    { iIntros (([b_t' b_s'] & Hin & <-)).
      iPoseProof (big_sepS_elem_of with "Hheap") as "Hr"; first by apply Hin.
      iDestruct "Hr" as (? v_t' v_s') "(Hr_t & Ha_t' & Ha_s')".
      by iApply (heap_block_size_excl with "Ha_t Ha_t'"). }

    iAssert ((¬ ⌜set_Exists (λ '(b_t', b_s'), l_s = b_s') L⌝)%I) as "%Hext_s".
    { iIntros (([b_t' b_s'] & Hin & <-)).
      iPoseProof (big_sepS_elem_of with "Hheap") as "Hr"; first by apply Hin.
      iDestruct "Hr" as (? v_t' v_s') "(Hr_t & Ha_t' & Ha_s')".
      by iApply (heap_block_size_excl with "Ha_s Ha_s'").
    }

    iMod ((gset_bij_own_extend l_t l_s) with "Hauth") as "[Hinv #Helem]"; eauto.
    { intros b_s' Hb_s'. apply Hext_t. by exists (l_t, b_s'). }
    { intros b_t' Hb_t'. apply Hext_s. by exists (b_t', l_s). }

    iModIntro.
    iSplitL; first last. { iSplitL; first done. iPureIntro; done. }
    iFrame. iApply big_sepS_insert.
    { intro. eapply Hext_s. exists (l_t, l_s); eauto. }
    iFrame.
    destruct (C !! (l_t, l_s)) eqn : HC.
    { iExists n, v_t, v_s; iFrame.
      destruct n; eauto.
      iExists _; iSplit; cbn; try done; iFrame.
      cbn. destruct (1-q)%Qp eqn: H; auto.
      iFrame. rewrite Qp.sub_Some in H.
      iDestruct (heap_mapsto_split with "Ht") as "(?&?)"; [ done | iFrame].
      iDestruct (heap_mapsto_split with "Hs") as "(?&?)"; [ done | iFrame]. }
    { iExists n, v_t, v_s; iFrame.
      destruct n; eauto.
      iExists _; iSplit; cbn; try done; iFrame. }
  Qed.

  Lemma heapbij_insert_ctx
      L C l_t l_s v_t v_s n
      m_t mf_t GS_t LS_t LsS_t
      m_s mf_s GS_s LS_s LsS_s
      i_t i_s A_t A_s :
    ⌜l_t ∈ A_t⌝ -∗
    ⌜l_s ∈ A_s⌝ -∗
    heapbij_interp L C -∗
    stack_tgt i_t -∗
    stack_src i_s -∗
    alloca_tgt i_t A_t -∗
    alloca_src i_s A_s -∗
    heap_ctx sheapG_heap_target
      m_t mf_t GS_t LS_t LsS_t -∗
    heap_ctx sheapG_heap_source
      m_s mf_s GS_s LS_s LsS_s -∗
    l_t ↦t [ v_t ] -∗
    l_s ↦s [ v_s ] -∗
    lb_rel v_t v_s -∗
    target_block_size l_t n -∗
    source_block_size l_s n ==∗
    heapbij_interp ({[(l_t, l_s)]} ∪ L) C
    ∗ (l_t, 0) ↔h (l_s, 0)
    ∗ alloca_tgt i_t A_t
    ∗ alloca_src i_s A_s
    ∗ stack_tgt i_t
    ∗ stack_src i_s
    ∗ heap_ctx sheapG_heap_target m_t mf_t GS_t LS_t LsS_t
    ∗ heap_ctx sheapG_heap_source m_s mf_s GS_s LS_s LsS_s
  .
  Proof.
    iIntros (Hin_t Hin_s)
      "Hinv Hs_t Hs_s Ha_t Ha_s Hh_t Hh_s Ht Hs Hrel Hb_t Hb_s".
    iDestruct "Hinv" as "(Hauth & Hheap)".

    iAssert ((¬ ⌜set_Exists (λ '(b_t', b_s'), l_t = b_t') L⌝)%I) as "%Hext_t".
    { iIntros (([b_t' b_s'] & Hin & <-)).
      iPoseProof (big_sepS_elem_of with "Hheap") as "Hr"; first by apply Hin.
      iDestruct "Hr" as (? v_t' v_s') "(Hr_t & Ha_t' & Ha_s')".
      by iApply (heap_block_size_excl with "Hb_t Ha_t'"). }

    iAssert ((¬ ⌜set_Exists (λ '(b_t', b_s'), l_s = b_s') L⌝)%I) as "%Hext_s".
    { iIntros (([b_t' b_s'] & Hin & <-)).
      iPoseProof (big_sepS_elem_of with "Hheap") as "Hr"; first by apply Hin.
      iDestruct "Hr" as (? v_t' v_s') "(Hr_t & Ha_t' & Ha_s')".
      by iApply (heap_block_size_excl with "Hb_s Ha_s'").
    }

    iMod ((gset_bij_own_extend l_t l_s) with "Hauth") as "[Hinv #Helem]"; eauto.
    { intros b_s' Hb_s'. apply Hext_t. by exists (l_t, b_s'). }
    { intros b_t' Hb_t'. apply Hext_s. by exists (b_t', l_s). }

    destruct_HC "Hh_t".
    iDestruct "Hh_s" as (cft hFt)
        "(Hσ_s&HB_s&HCF_s&HA_s&HL_s&HD_s&HSA_s&HG_s&%Hdup_s&%Hbs_s&%Hwf_s)".

    (* Frames agree *)
    iDestruct (ghost_var_agree with "Hs_t HCF") as "%Hcf_t"; subst.
    iDestruct (ghost_var_agree with "Hs_s HCF_s") as "%Hcf_s"; subst.

    (* Update alloca set *)
    rewrite allocaS_eq.
    iDestruct (ghost_var_agree with "Ha_t HA") as "%Ha_t"; subst.
    iDestruct (ghost_var_agree with "Ha_s HA_s") as "%Ha_s"; subst.

    (* Extend bij set *)
    iFrame.
    iSplitL "Hheap Ht Hs Hrel Hb_t Hb_s".
    { rewrite /heapbij_interp. iFrame. iApply big_sepS_insert.
      { intro. eapply Hext_s. exists (l_t, l_s); eauto. }
      iFrame. rewrite /alloc_rel. iExists n, v_t, v_s.
      destruct n; last by iFrame.
      destruct (C !! (l_t, l_s)) eqn : HC; iFrame;
      iExists _; iSplitL ""; cbn; try done; rewrite HC; iFrame; try done.
      cbn. destruct (1-q)%Qp eqn: H; auto.
      iFrame. rewrite Qp.sub_Some in H.
      iDestruct (heap_mapsto_split with "Ht") as "(?&?)";
        [ done | iFrame].
      iDestruct (heap_mapsto_split with "Hs") as "(?&?)";
        [ done | iFrame]; done. }

    (* Relation *)
    iSplitL "". { iSplitL; first done. iPureIntro; done. }

    (* Target heap ctx *)
    iSplitL "Hs_t Hb HL HD HSA Ha_t".
    { iExists _, _. iFrame.
      iSplitL ""; first iPureIntro; eauto. }

    (* Source heap ctx *)
    iExists _, _. iFrame.
    iSplitL ""; first iPureIntro; eauto.
  Qed.

End laws.
