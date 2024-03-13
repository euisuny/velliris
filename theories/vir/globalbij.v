(** * Bijection between global variables *)

From iris.prelude Require Import options.

From velliris.program_logic Require Import program_logic.
From velliris.vir Require Import heapbij spec.

From Vellvm Require Import Semantics.LLVMEvents Handlers.
From ITree Require Import ITree Eq Eq.EqAxiom.

Set Default Proof Using "Type*".

Section globalbij.

  Context {Σ : gFunctors} `{!sheapGS Σ, !checkedoutGS Σ, !heapbijGS Σ}.

  Lemma rev_injective {A} (l l' : _ A) : rev l' = rev l -> l' = l.
  Proof.
    revert l'.
    induction l; intros.
    - cbn in H. symmetry in H. apply Util.rev_nil_rev in H. auto.
    - cbn in H. destruct l'.
      + intros. exfalso; eapply app_cons_not_nil; eauto.
      + intros; cbn in H.
        apply app_inj_tail in H. destruct H; subst.
        f_equiv. by eapply IHl.
  Qed.

  Lemma alist_find_app_some {A} f l1 l2 (d : A):
    (FMapAList.alist_find AstLib.eq_dec_raw_id f (l1 ++ l2) = Some d <->
    (FMapAList.alist_find AstLib.eq_dec_raw_id f l1 = Some d \/
    (FMapAList.alist_find AstLib.eq_dec_raw_id f l1 = None /\
      FMapAList.alist_find AstLib.eq_dec_raw_id f l2 = Some d)))%list.
  Proof.
    split.
    { induction l1; intros; cbn in H.
      { cbn. right; eauto. }
      { destruct a; cbn.
        destruct (RelDec.rel_dec f r) eqn: Heq.
        { left; auto. }
        specialize (IHl1 H). destruct IHl1.
        - inversion H. rewrite H0 H2. by left.
        - right; auto. } }
    { induction l1; intros; cbn in H.
      { destruct H; inversion H; auto. }
      { destruct a; cbn; destruct H.
        { destruct (RelDec.rel_dec f r) eqn: Heq; auto. }
        { destruct (RelDec.rel_dec f r) eqn: Heq; auto.
          destruct H. inversion H. } } }
  Qed.

  Lemma alist_find_app_none {A} f l1 l2 :
    (FMapAList.alist_find AstLib.eq_dec_raw_id f (l1 ++ l2) = None <->
    (FMapAList.alist_find AstLib.eq_dec_raw_id f l1 = None /\
      FMapAList.alist_find (V := A) AstLib.eq_dec_raw_id f l2 = None))%list.
  Proof.
    split.
    {induction l1; intros; cbn in H.
    { cbn; eauto. }
    { destruct a; cbn.
      destruct (RelDec.rel_dec f r) eqn: Heq; [ inversion H | ].
      specialize (IHl1 H). destruct IHl1.
      split; auto. } }
    {induction l1; intros; cbn in H.
    { destruct H; cbn; eauto. }
    { destruct a; cbn.
      destruct (RelDec.rel_dec f r) eqn: Heq; [ inversion H | ].
      { destruct H; eauto. }
      specialize (IHl1 H). destruct IHl1.
      split; auto. } }
  Qed.

  Lemma alist_find_singleton {A} r f (d d0 : A) :
    FMapAList.alist_find AstLib.eq_dec_raw_id f [(r, d)] = Some d0 ->
    f = r /\ d = d0.
  Proof.
    cbn;intros. destruct (RelDec.rel_dec f r) eqn: Heq; inversion H.
    rewrite RelDec.rel_dec_correct in Heq; auto.
  Qed.

  Lemma alist_find_none {A} f l :
    FMapAList.alist_find (V := A) AstLib.eq_dec_raw_id f l = None ->
    forall k v, In (k, v) l -> k <> f.
  Proof.
    revert f.
    induction l; cbn; intros; auto.
    destruct a; destruct H0.
    { inversion H0; subst.
      destruct (RelDec.rel_dec f k) eqn: Hf; [ inversion H | ].
      rewrite <- RelDec.neg_rel_dec_correct in Hf; auto. }
    { destruct (RelDec.rel_dec f r) eqn: Hf; [ inversion H | ].
      eapply IHl; eauto. }
  Qed.

  Lemma fold_alist_insert_some_neq f l1 l2 r d d0:
    FMapAList.fold_alist (λ (k : LLVMAst.raw_id) (v0 : dvalue) (acc : vir.globals), <[k:=v0]> acc) l2 l1 !! f = Some d -> r <> f ->
    FMapAList.fold_alist (λ (k : LLVMAst.raw_id) (v0 : dvalue) (acc : vir.globals), <[k:=v0]> acc) (<[r:=d0]> l2) l1 !! f = Some d.
  Proof.
    revert f l2 r d d0.
    induction l1; intros; cbn in H; cbn; auto.
    { rewrite lookup_insert_ne; auto. }
    { destruct a.
      destruct (RelDec.rel_dec r r0) eqn: Hr.
      { rewrite RelDec.rel_dec_correct in Hr. subst.
        rewrite insert_insert. auto. }
      { apply RelDec.neg_rel_dec_correct in Hr.
        rewrite insert_commute; auto. } }
  Qed.

  Lemma fold_alist_insert_some_eq f l1 l2 r d:
    FMapAList.fold_alist (λ (k : LLVMAst.raw_id) (v0 : dvalue) (acc : vir.globals), <[k:=v0]> acc) l2 l1 !! f = Some d -> r = f ->
    FMapAList.fold_alist (λ (k : LLVMAst.raw_id) (v0 : dvalue) (acc : vir.globals), <[k:=v0]> acc) (<[r:=d]> l2) l1 !! f = Some d.
  Proof.
    revert f l2 r d.
    induction l1; intros; cbn in H; cbn; auto.
    { subst; rewrite lookup_insert; auto. }
    { destruct a. subst.
      destruct (RelDec.rel_dec r0 f) eqn: Hr.
      { rewrite RelDec.rel_dec_correct in Hr. subst.
        rewrite insert_insert. auto. }
      { apply RelDec.neg_rel_dec_correct in Hr.
        rewrite insert_commute; auto. } }
  Qed.


  Lemma fold_alist_insert_some f l1 l2 r d:
    FMapAList.fold_alist (λ (k : LLVMAst.raw_id) (v0 : dvalue) (acc : vir.globals), <[k:=v0]> acc) l2 l1 !! f = Some d ->
    (forall d0, r <> f /\
      FMapAList.fold_alist (λ (k : LLVMAst.raw_id) (v0 : dvalue) (acc : vir.globals), <[k:=v0]> acc) (<[r:=d0]> l2) l1 !! f = Some d) \/
    (r = f /\
      FMapAList.fold_alist (λ (k : LLVMAst.raw_id) (v0 : dvalue) (acc : vir.globals), <[k:=v0]> acc) (<[r:=d]> l2) l1 !! f = Some d).
  Proof.
    intros.
    destruct (RelDec.rel_dec r f) eqn: Hrf;
      [ rewrite RelDec.rel_dec_correct in Hrf | apply RelDec.neg_rel_dec_correct in Hrf ].
    { right. eapply fold_alist_insert_some_eq in H; eauto. }
    { left. intros; eapply fold_alist_insert_some_neq in H; eauto. }
  Qed.

  Lemma alist_to_gmap_find_gen f g g' d :
    (FMapAList.alist_find AstLib.eq_dec_raw_id f g = Some d \/
    (FMapAList.alist_find AstLib.eq_dec_raw_id f g = None /\
      g' !! f = Some d)) ->
    (FMapAList.fold_alist
      (λ (k : LLVMAst.raw_id) (v0 : dvalue) (acc : vir.globals),
          <[k:=v0]> acc) g' (rev g)) !! f = Some d.
  Proof.
    intros; setoid_rewrite <- (rev_involutive g) in H.
    revert g' f d H.
    induction (rev g).
    { intros; cbn in H; destruct H; [inversion H | by destruct H]. }
    cbn in *; destruct a; intros.
    destruct H.
    { apply alist_find_app_some in H. destruct H.
      { eapply IHl; eauto. }
      { destruct H as (?&?); subst.
        apply alist_find_singleton in H0. destruct H0 as (?&?); subst.
        eapply IHl; right; eauto. split; auto.
        by rewrite lookup_insert. } }
    { destruct H as (Hf & Hg').
      assert (r <> f).
      { eapply alist_find_none in Hf; eauto.
        eapply in_elt. }
      eapply IHl; right.
      apply alist_find_app_none in Hf. destruct Hf as (Hf1 & Hf2).
      split; auto.
      rewrite lookup_insert_ne; eauto. }
  Qed.

  Lemma alist_to_gmap_find f g d :
    FMapAList.alist_find AstLib.eq_dec_raw_id f g = Some d ->
    (FMapAList.fold_alist
      (λ (k : LLVMAst.raw_id) (v0 : dvalue) (acc : vir.globals),
          <[k:=v0]> acc) ∅ (rev g)) !! f = Some d.
  Proof.
    intros; eapply alist_to_gmap_find_gen; by left.
  Qed.

  Lemma fold_alist_find_insert r d l l' f d0:
    FMapAList.fold_alist
      (λ (k : LLVMAst.raw_id) (v0 : dvalue) (acc : vir.globals), <[k:=v0]> acc)
      (<[r := d]>l') l !! f = Some d0 ->
    FMapAList.fold_alist
      (λ (k : LLVMAst.raw_id) (v0 : dvalue) (acc : vir.globals), <[k:=v0]> acc)
      l' l !! f = Some d0 \/
   (r = f /\ d = d0).
  Proof.
    revert l' r d f d0.
    induction l; cbn; intros; eauto.
    { assert (H' := H).
      rewrite lookup_insert_Some in H; destruct H.
      - destruct H; subst; right; eauto.
      - destruct H; eauto. }
    destruct a; cbn in *.
    destruct (RelDec.rel_dec r r0) eqn: Hr.
    { rewrite RelDec.rel_dec_correct in Hr. subst.
      rewrite insert_insert in H. left; auto. }
    { apply RelDec.neg_rel_dec_correct in Hr.
      eapply IHl; eauto.
      rewrite insert_commute; eauto. }
  Qed.

  Lemma fold_alist_none_insert r d l l' f:
    FMapAList.fold_alist
        (λ (k : LLVMAst.raw_id) (v0 : dvalue) (acc : vir.globals), <[k:=v0]> acc)
        (<[r := d]> l') l !! f = None <->
    FMapAList.fold_alist
        (λ (k : LLVMAst.raw_id) (v0 : dvalue) (acc : vir.globals), <[k:=v0]> acc)
        l' l !! f = None /\ r <> f.
  Proof.
    split.
    { revert r d f l'.
      induction l; cbn; intros; eauto.
      { rewrite lookup_insert_None in H; destruct H. auto. }
      destruct a; eauto.
      destruct (RelDec.rel_dec r r0) eqn: Hr.
      { eapply IHl; eauto.
        rewrite RelDec.rel_dec_correct in Hr. subst.
        rewrite insert_insert in H.
        rewrite insert_insert. eauto. }
      { apply RelDec.neg_rel_dec_correct in Hr.
        eapply IHl; eauto.
        rewrite insert_commute; eauto. } }
    { revert r d f l'.
      induction l; cbn; intros; eauto.
      { destruct H; rewrite lookup_insert_None; auto. }
      destruct a; eauto.
      destruct (RelDec.rel_dec r r0) eqn: Hr.
      { rewrite RelDec.rel_dec_correct in Hr. subst.
        rewrite insert_insert. destruct H; eauto. }
      { apply RelDec.neg_rel_dec_correct in Hr.
        rewrite insert_commute; eauto. } }
  Qed.

  Lemma fold_alist_find_insert' r d l l' f d0:
    FMapAList.fold_alist
      (λ (k : LLVMAst.raw_id) (v0 : dvalue) (acc : vir.globals), <[k:=v0]> acc)
      (<[r := d]>l') l !! f = Some d0 ->
    FMapAList.fold_alist
      (λ (k : LLVMAst.raw_id) (v0 : dvalue) (acc : vir.globals), <[k:=v0]> acc)
      l' l !! f = Some d0 \/
    (FMapAList.fold_alist
      (λ (k : LLVMAst.raw_id) (v0 : dvalue) (acc : vir.globals), <[k:=v0]> acc)
      ∅ l !! f = None /\
     r = f /\ d = d0).
  Proof.
    revert l' r d f d0.
    induction l; cbn; intros; eauto.
    { assert (H' := H). rewrite lookup_insert_Some in H; destruct H.
      - destruct H; subst; right; eauto.
      - destruct H; eauto. }
    destruct a; cbn in *.
    destruct (RelDec.rel_dec r r0) eqn: Hr.
    { rewrite RelDec.rel_dec_correct in Hr. subst.
      rewrite insert_insert in H. left; auto. }
    { apply RelDec.neg_rel_dec_correct in Hr.
      rewrite insert_commute in H; eauto.
      specialize (IHl _ _ _ _ _ H).
      destruct IHl; eauto.
      destruct H0 as (?&?&?); right; subst; eauto.
      split; eauto. clear -H0 Hr.
      rewrite fold_alist_none_insert; eauto. }
  Qed.

  Lemma alist_to_gmap_none l f :
    FMapAList.fold_alist
          (λ (k : LLVMAst.raw_id) (v0 : dvalue) (acc : vir.globals), <[k:=v0]> acc)
          ∅ l !! f = None ->
    FMapAList.alist_find AstLib.eq_dec_raw_id f (rev l) = None.
  Proof.
    revert f. induction l; eauto.
    cbn; intros. destruct a.
    apply fold_alist_none_insert in H; destruct H.
    rewrite alist_find_app_none; split.
    { eapply IHl; eauto. }
    assert (f <> r). { intro; apply H0; eauto. }
    cbn; apply Util.eq_dec_neq in H1. rewrite H1; eauto.
  Qed.

  Lemma alist_to_gmap_find' f g d :
    (FMapAList.fold_alist
      (λ (k : LLVMAst.raw_id) (v0 : dvalue) (acc : vir.globals),
          <[k:=v0]> acc) ∅ (rev g)) !! f = Some d ->
    FMapAList.alist_find AstLib.eq_dec_raw_id f g = Some d.
  Proof.
    intros; setoid_rewrite <- (rev_involutive g).
    revert f d H.
    induction (rev g).
    { cbn; intros; inversion H. }

    cbn in *; destruct a; intros.
    rewrite alist_find_app_some.
    apply fold_alist_find_insert' in H; destruct H.
    { left; apply IHl; auto. }
    destruct H as (?&?); subst.

    right; cbn. destruct H0; subst; eauto.
    assert (Dec: RelDec.rel_dec f f = true) by apply Util.eq_dec_eq.
    rewrite Dec; eauto; split; eauto.
    eapply alist_to_gmap_none; eauto.
  Qed.

  Lemma sim_global_read (f: LLVMAst.global_id) Φ:
    (∀ (v_t v_s : dvalue),
        dval_rel v_s v_t -∗
        Φ v_s v_t) -∗
    trigger (GlobalRead f) ⪯ trigger (GlobalRead f)
    [{ (v_t, v_s), Φ v_t v_s }].
  Proof.
    iIntros "Hl".

    rewrite sim_expr_unfold.
    iIntros "%σ_t %σ_s SI".
    destruct σ_t as ((?&?)&?&?); destruct σ_s as ((?&?)&?&?).
    provide_case: TAU_STEP.

    (iSplitL ""; [ iPureIntro | ]).
    { apply EqAxiom.bisimulation_is_eq. rewrite <- itree_eta.
      rewrite /interp_L2 StateFacts.interp_state_trigger_eqit; cbn; rewrite /add_tau.
      rewrite bind_tau. apply eqitree_Tau; cbn. rewrite bind_bind.
      reflexivity. }

    (iSplitL ""; [ iPureIntro | ]).
    { apply EqAxiom.bisimulation_is_eq. rewrite <- itree_eta.
      rewrite /interp_L2 StateFacts.interp_state_trigger_eqit; cbn; rewrite /add_tau.
      rewrite bind_tau. apply eqitree_Tau; cbn. rewrite bind_bind.
      reflexivity. }

    cbn.
    iDestruct "SI" as (???) "(Hhs & Hht & Hgv & Hi & %WF & Hlo & Hbij)".
    iDestruct "Hbij" as "(%Hsub&#Hgs_t&#Hgs_s&#Hrel)".
    destruct (g0 !! f) eqn: Hs.

    { assert (Hs'' := Hs).

      assert (Hs' := Hs).
      apply elem_of_dom_2 in Hs.
      iDestruct (big_sepM_lookup_acc _ _ _ _ Hs' with "Hrel") as "(Helem & Hrel')".

      iAssert (global sheapG_heap_source f d)%I as "Hs_elem".
      { rewrite global_eq /global_def.
        iExists g0.
        iSplitL ""; [ | iApply "Hgs_s"].
        by iPureIntro. }
      iDestruct "Helem" as (v' Hv') "Helem".
      iDestruct (global_in with "Hgs_s Hs_elem") as %Hin.
      iDestruct (global_intro with "Hgs_t") as "#Hg_t".
      { eauto. }

      rewrite Hv' Hin; cbn.

      iApply sim_coindF_tau; iApply sim_coindF_base.
      rewrite /lift_expr_rel.
      iExists (g, p, (p0, f0)), v', (g0, p1, (p2, f1)), d; iFrame.
      do 2 (iSplitL ""; [ iPureIntro; rewrite <- itree_eta; reflexivity | ]).
      rewrite /state_interp. cbn.
      iFrame.
      iSplitL "Hhs Hht Hgv Hi".
      { iExists C, S, G. repeat iExists _. iFrame. destruct p; iFrame.
        iSplitL ""; first done.

        rewrite /globalbij_interp.
        iSplitL ""; [ iPureIntro; exact Hsub
          | iSplitL "" ; [iApply "Hgs_t" | ] ].
        iSplitL "" ; [iApply "Hgs_s" | ].
        iApply "Hrel". }
      iSpecialize ("Hl" with "Helem").
      iExists v', d.
      do 2 (iSplitL ""; [ iPureIntro; reflexivity | ]); done.
    }
    { cbn.
      rewrite sim_coindF_unfold sim_indF_unfold /sim_expr_inner.
      provide_case: SOURCE_EXC.
      iPureIntro. rewrite Hs. cbn. reflexivity. }
  Qed.

  Lemma sim_global_read1 (f: LLVMAst.global_id) g g0 x_t x_s:
    g !! f = Some x_t ->
    g0 !! f = Some x_s ->
    target_globals g -∗
    source_globals g0 -∗
    trigger (GlobalRead f) ⪯ trigger (GlobalRead f)
    [{ (v_t, v_s), dval_rel v_t v_s ∗ ⌜v_t = x_t⌝ ∗ ⌜v_s = x_s⌝ }].
  Proof.
    iIntros (??) "Hg Hg0".

    rewrite sim_expr_eq.
    iIntros "%σ_t %σ_s SI".
    destruct σ_t as ((?&?)&?&?); destruct σ_s as ((?&?)&?&?).
    iDestruct "SI" as (???) "(Hhs & Hht & Hgv & Hi & %WF & Hlo & Hbij)".
    iDestruct "Hbij" as "(%Hsub&#Hgs_t&#Hgs_s&#Hrel)".
    iDestruct (globals_agree with "Hgs_t Hg") as %Ht; subst.
    iDestruct (globals_agree with "Hgs_s Hg0") as %Ht; subst.
    setoid_rewrite StateFacts.interp_state_vis; setoid_rewrite bind_tau; cbn.
    cbn in *. rewrite H H0.

    iApply sim_coind_tau.
    rewrite bind_bind !bind_ret_l.
    iApply sim_coind_tau.
    rewrite !StateFacts.interp_state_ret.
    iApply sim_coind_base; eauto.
    iFrame.
      iSplitL "Hhs Hht Hgv Hi".
    { iExists C, S, G. repeat iExists _. iFrame. destruct p; iFrame.
      repeat (iSplitL ""; first done). done. }
    iExists _, _; eauto.
    repeat (iSplitL ""; first done). cbn.
    iDestruct (big_sepM_lookup_acc _ _ _ _ H0 with "Hrel") as "(Helem & Hrel')".
    iDestruct "Helem" as (??) "#Helem".
    rewrite H1 in H; inv H. iFrame "Helem"; done.
  Qed.

  Lemma sim_global_write f v_t v_s g g0:
    g !! f = Some v_t ->
    g0 !! f = Some v_s ->
    target_globals g -∗
    source_globals g0 -∗
    trigger (GlobalWrite f v_t) ⪯ trigger (GlobalWrite f v_s)
    [{ (v_t, v_s), True }].
  Proof.
    iIntros (??) "Hg Hg0".

    rewrite sim_expr_unfold.
    iIntros "%σ_t %σ_s SI".
    destruct σ_t as ((?&?)&?&?); destruct σ_s as ((?&?)&?&?).
    provide_case: TAU_STEP.

    (iSplitL ""; [ iPureIntro | ]).
    { apply EqAxiom.bisimulation_is_eq. rewrite <- itree_eta.
      rewrite /interp_L2 StateFacts.interp_state_trigger_eqit; cbn; rewrite /add_tau.
      rewrite bind_tau. apply eqitree_Tau; cbn. rewrite bind_bind.
      reflexivity. }

    (iSplitL ""; [ iPureIntro | ]).
    { apply EqAxiom.bisimulation_is_eq. rewrite <- itree_eta.
      rewrite /interp_L2 StateFacts.interp_state_trigger_eqit; cbn; rewrite /add_tau.
      rewrite bind_tau. apply eqitree_Tau; cbn. rewrite bind_bind.
      reflexivity. }

    cbn.
    iDestruct "SI" as (???) "(Hhs & Hht & Hgv & Hi & %WF & Hlo & Hbij)".
    iDestruct "Hbij" as "(%Hsub&#Hgs_t&#Hgs_s&#Hrel)".

    iDestruct (globals_agree with "Hgs_t Hg") as %Ht; subst.
    iDestruct (globals_agree with "Hgs_s Hg0") as %Ht; subst.

    rewrite !insert_id; eauto.
    iApply sim_coindF_tau.
    iApply sim_coindF_base.
    rewrite /lift_expr_rel.
    iExists (g , p, (p0, f0)), tt,
      (g0, p1, (p2, f1)), tt; iFrame.
    do 2 (iSplitL ""; [ iPureIntro; rewrite <- itree_eta; reflexivity | ]).
    rewrite /state_interp. cbn.
    iFrame.
      iSplitL "Hhs Hht Hgv Hi".
    { iExists C, S, G. repeat iExists _. iFrame. destruct p; iFrame.
      repeat (iSplitL ""; first done). done. }
    iExists tt, tt; eauto.
  Qed.

End globalbij.
