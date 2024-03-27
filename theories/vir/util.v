From iris.algebra Require Import gmap auth.
From iris.prelude Require Import options.
From iris.proofmode Require Export tactics.
Set Default Proof Using "Type".

From velliris.utils Require Import tactics.
From velliris.vir Require Export vir.
From Vellvm Require Import Handlers.Handlers.

Open Scope nat_scope.

(* Lemmas about [Qp] *)
Lemma add_le_sub_r_Some qr q qa:
  (qr + q ≤ qa)%Qp ->
  ∃ q', (qa - q = Some q')%Qp.
Proof.
  setoid_rewrite Qp.sub_Some.
  intros Hq.
  apply Qp.le_lteq in Hq. destruct Hq.
  { rewrite Qp.lt_sum in H. destruct H; eauto.
    exists (qr + x)%Qp. rewrite H. rewrite Qp.add_assoc.
    f_equiv. apply Qp.add_comm. }
  { exists qr. rewrite -H. apply Qp.add_comm. }
Qed.

Lemma add_le_sub_r_Some' qr q qa:
  (qr + q ≤ qa)%Qp ->
  ((∃ q', qa - q = Some (qr + q')) \/ (qa = qr + q))%Qp.
Proof.
  setoid_rewrite Qp.sub_Some.
  intros Hq.
  apply Qp.le_lteq in Hq. destruct Hq.
  { rewrite Qp.lt_sum in H. destruct H; eauto. left.
    exists x. rewrite H. rewrite Qp.add_assoc.
    f_equiv. apply Qp.add_comm. }
  { right. by rewrite -H. }
Qed.

Lemma add_le_sub_l_Some qr q qa:
  (qr + q ≤ qa)%Qp ->
  ∃ q', (qa - qr = Some q')%Qp.
Proof.
  rewrite Qp.add_comm.
  apply add_le_sub_r_Some.
Qed.

Lemma le_eq (q q': Qp) :
  (q' ≤ q)%Qp -> (q ≤ q')%Qp -> q = q'.
Proof.
  rewrite !Qp.le_lteq.
  intros [] []; subst; eauto.
  exfalso.
  apply Qp.lt_nge in H.
  apply H.
  by apply Qp.lt_le_incl.
Qed.

(* Some equivalent computable functions for standard list manipulation *)

Fixpoint In_b {A} `{EQ: EqDecision A} (a:A) (l:list A) : bool :=
  match l with
    | nil => false
    | b :: m => @bool_decide _ (decide_rel eq b a) || @In_b A _ a m
  end.

Lemma In_b_In {A} `{EQ: EqDecision A} (a:A) (l:list A) :
  In_b a l = true <-> In a l.
Proof.
  revert a; induction l; cbn; split; intros;
    try solve [inversion H]; auto.
  { apply orb_prop in H. destruct H.
    - left. by apply bool_decide_eq_true in H.
    - right. apply IHl; auto. }
  destruct H; subst.
  { apply orb_true_intro.
    left; by apply bool_decide_eq_true. }
  { apply orb_true_intro.
    right; by eapply IHl. }
Qed.

Fixpoint NoDup_b {A} `{EQ: EqDecision A} (l : list A) : bool :=
  match l with
  | nil => true
  | x :: l => negb (@In_b _ _ x l) && @NoDup_b A EQ l
  end.

Lemma NoDup_b_NoDup {A} `{EQ: EqDecision A} (l:list A) :
  NoDup_b l = true <-> NoDup l.
Proof.
  induction l; cbn; split; intros;
    try solve [inversion H || constructor].
  { apply andb_prop in H. destruct H.
    apply NoDup_cons.
    split.
    - rewrite elem_of_list_In.
      intro. apply In_b_In in H1.
      rewrite H1 in H; cbn in H; done.
    - by apply IHl. }

  apply andb_true_intro.
  apply NoDup_cons in H; destruct H.
  rewrite elem_of_list_In in H.
  split; try by apply IHl.
  destruct (In_b a l) eqn: Hb; auto.
  apply In_b_In in Hb; done.
Qed.

Lemma NoDup_b_NoDup1 {A} `{EQ: EqDecision A} (l:list A) :
  NoDup_b l <-> NoDup l.
Proof.
  rewrite -NoDup_b_NoDup.
  intuition.
  destruct (NoDup_b l); try done.
Qed.


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

(* [alist]-related util functions *)

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

(* LATER: Generalize these [fold_alist] lemmas to general association lists *)
Lemma fold_alist_insert_some_neq f l1 l2 r d d0:
  FMapAList.fold_alist (λ (k : LLVMAst.raw_id) (v0 : dvalue)
   (acc : global_env), <[k:=v0]> acc) l2 l1 !! f = Some d -> r <> f ->
  FMapAList.fold_alist (λ (k : LLVMAst.raw_id) (v0 : dvalue)
   (acc : global_env), <[k:=v0]> acc) (<[r:=d0]> l2) l1 !! f = Some d.
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
  FMapAList.fold_alist (λ (k : LLVMAst.raw_id) (v0 : dvalue)
   (acc : global_env), <[k:=v0]> acc) l2 l1 !! f = Some d -> r = f ->
  FMapAList.fold_alist (λ (k : LLVMAst.raw_id) (v0 : dvalue)
   (acc : global_env), <[k:=v0]> acc) (<[r:=d]> l2) l1 !! f = Some d.
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
  FMapAList.fold_alist (λ (k : LLVMAst.raw_id) (v0 : dvalue)
   (acc : global_env), <[k:=v0]> acc) l2 l1 !! f = Some d ->
  (forall d0, r <> f /\
    FMapAList.fold_alist (λ (k : LLVMAst.raw_id) (v0 : dvalue)
      (acc : global_env), <[k:=v0]> acc) (<[r:=d0]> l2) l1 !! f = Some d) \/
  (r = f /\
    FMapAList.fold_alist (λ (k : LLVMAst.raw_id) (v0 : dvalue)
      (acc : global_env), <[k:=v0]> acc) (<[r:=d]> l2) l1 !! f = Some d).
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
    (λ (k : LLVMAst.raw_id) (v0 : dvalue) (acc : global_env),
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
    (λ (k : LLVMAst.raw_id) (v0 : dvalue) (acc : global_env),
        <[k:=v0]> acc) ∅ (rev g)) !! f = Some d.
Proof.
  intros; eapply alist_to_gmap_find_gen; by left.
Qed.

Lemma fold_alist_find_insert r d l l' f d0:
  FMapAList.fold_alist
    (λ (k : LLVMAst.raw_id) (v0 : dvalue) (acc : global_env), <[k:=v0]> acc)
    (<[r := d]>l') l !! f = Some d0 ->
  FMapAList.fold_alist
    (λ (k : LLVMAst.raw_id) (v0 : dvalue) (acc : global_env), <[k:=v0]> acc)
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
      (λ (k : LLVMAst.raw_id) (v0 : dvalue) (acc : global_env), <[k:=v0]> acc)
      (<[r := d]> l') l !! f = None <->
  FMapAList.fold_alist
      (λ (k : LLVMAst.raw_id) (v0 : dvalue) (acc : global_env), <[k:=v0]> acc)
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
    (λ (k : LLVMAst.raw_id) (v0 : dvalue) (acc : global_env), <[k:=v0]> acc)
    (<[r := d]>l') l !! f = Some d0 ->
  FMapAList.fold_alist
    (λ (k : LLVMAst.raw_id) (v0 : dvalue) (acc : global_env), <[k:=v0]> acc)
    l' l !! f = Some d0 \/
  (FMapAList.fold_alist
    (λ (k : LLVMAst.raw_id) (v0 : dvalue) (acc : global_env), <[k:=v0]> acc)
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
        (λ (k : LLVMAst.raw_id) (v0 : dvalue) (acc : global_env), <[k:=v0]> acc)
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
    (λ (k : LLVMAst.raw_id) (v0 : dvalue) (acc : global_env),
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

(* Some utility lemmas *)

Lemma combine_fst {A B} (l : list A) (l' : list B) :
  length l = length l' ->
  (combine l l').*1 = l.
Proof.
  revert l'.
  induction l; cbn in *; eauto.
  intros.
  destruct l'; [ done | ].
  cbn. f_equiv. eauto.
Qed.

Lemma combine_snd {A B} (l : list A) (l' : list B) :
  length l = length l' ->
  (combine l l').*2 = l'.
Proof.
  revert l'.
  induction l; cbn in *; eauto.
  { destruct l'; by intros. }
  intros.
  destruct l'; [ done | ].
  cbn. f_equiv. eauto.
Qed.

Lemma lookup_singleton_inv (K : Type) (M : Type → Type)
  `{EqDecision K} `{FinMap K M} :
  ∀ (A : Type) (i k : K) (x y: A),
      ({[i := y]} : M A) !! k = Some x ->
      i = k /\ x = y.
Proof.
  intros * Hlu.
  destruct (decide (i = k)); subst.
  - rewrite lookup_singleton in Hlu; inversion Hlu; subst.
    split; auto.
  - rewrite lookup_singleton_ne in Hlu; eauto; inversion Hlu.
Qed.

(* Utility functions about fold *)

Lemma fold_left_delete_comm {A K} `{!EqDecision K} `{!Countable K}
(f : list K) a (m : gmap K A):
  fold_left (fun m key => base.delete key m) f (base.delete a m) =
  base.delete a (fold_left (fun m key => base.delete key m) f m).
Proof.
  revert a m.
  induction f; cbn; auto.
  intros.
  rewrite delete_commute. by rewrite IHf.
Qed.

Lemma fold_delete_distr {A B} `{Countable A} `{EQA:EqDecision A}:
  forall a (d : list A) (m : gmap A B),
  a ∈ (list_to_set d : gset A) ->
  NoDup d ->
  fold_left (fun m key => delete key m) d m =
  delete a (fold_left (fun m key => delete key m) (remove EQA a d) m).
Proof.
  intros * Ha Hnd_s'. rewrite -fold_left_delete_comm.
  revert a m Ha.
  induction d.
  { set_solver. }
  { intros. cbn in Ha; cbn.

    apply NoDup_cons in Hnd_s'. destruct Hnd_s' as (?&Hnd_s').
    apply elem_of_union in Ha.
    destruct Ha.
    { assert (a0 = a) by set_solver.
      subst. destruct (EQA a a); last done.
      f_equiv; eauto.
      rewrite notin_remove; eauto.
      intros Hfalse. apply elem_of_list_In in Hfalse.
      set_solver. }
    { assert (a0 <> a).
      { intro; apply H0. subst. set_solver. }
      destruct (EQA a0 a); first done.
      cbn. rewrite fold_left_delete_comm.
      setoid_rewrite fold_left_delete_comm at 1.
      f_equiv.
      apply IHd; eauto. } }
Qed.

Lemma list_to_set_remove {A} `{EQA:EqDecision A} `{!Countable A}
  (x : list A) (k : A) :
  NoDup x ->
  (list_to_set (remove EQA k x) : gset A) = list_to_set x ∖ {[k]}.
Proof.
  revert k.
  induction x; first set_solver.
  cbn.
  intros * Hnd.
  apply NoDup_cons in Hnd. destruct Hnd as (?&?).
  intros.
  destruct (decide (k = a)); subst.
  { destruct (EQA a a); try done.
    rewrite difference_union_distr_l_L.
    rewrite difference_diag_L.
    rewrite union_empty_l_L. by eapply IHx. }
  { destruct (EQA k a); try done.
    rewrite difference_union_distr_l_L.
    cbn. rewrite IHx; eauto. set_solver. }
Qed.

Lemma NoDup_remove:
  ∀ (a : Z) (mf' : list Z),
    NoDup mf' → a ∈ mf' → NoDup (remove Z.eq_dec a mf').
Proof.
  intros a mf' H0 H2.
  revert a H0 H2.
  induction mf'; first set_solver.
  intros. apply NoDup_cons in H0. destruct H0.
  apply elem_of_cons in H2.
  destruct H2.
  { subst. rewrite remove_cons.
    rewrite notin_remove; auto.
    intro; apply H. by apply elem_of_list_In. }
  { cbn. destruct (Z.eq_dec a0 a); first set_solver.
    apply NoDup_cons.
    split; eauto.
    intro. apply H.
    apply elem_of_list_In.
    apply elem_of_list_In in H2.
    apply in_remove in H2. destruct H2; auto. }
Qed.

(* Properties about [list_to_map] and [list_to_set] used for local env *)
Lemma list_to_map_insert x v (l : local_env) :
  list_to_map (FMapAList.alist_add AstLib.eq_dec_raw_id x v l) =
    <[x := v]> (list_to_map l : gmap _ _).
Proof.
  induction l; eauto.
  do 2 cbn in IHl; cbn.

  destruct (negb (RelDec.rel_dec x a.1)) eqn: H; cbn; eauto.
  { assert (Hneq: x ≠ a.1).
    { rewrite negb_true_iff in H.
      by rewrite <- RelDec.neg_rel_dec_correct in H. }
    rewrite insert_commute; [ | done].
    rewrite IHl.
    by (rewrite insert_commute; [ | done]). }
  { assert (Heq: x = a.1).
    { rewrite negb_false_iff in H. by rewrite RelDec.rel_dec_correct in H. }
    subst. rewrite insert_insert. auto. }
Qed.

Lemma list_to_map_delete_alist l (L : local_env):
  (list_to_map (FMapAList.alist_remove AstLib.eq_dec_raw_id l L) : gmap _ _) =
      base.delete l (list_to_map L).
Proof.
  induction L; eauto.
  cbn.
  destruct (negb (RelDec.rel_dec l a.1)) eqn: H; cbn; eauto.
  { assert (Hneq: l ≠ a.1).
    { rewrite negb_true_iff in H.
      by rewrite <- RelDec.neg_rel_dec_correct in H. }
    rewrite delete_insert_ne; eauto.
    by rewrite IHL. }
  { assert (Heq: l = a.1).
    { rewrite negb_false_iff in H. by rewrite RelDec.rel_dec_correct in H. }
    subst.
    rewrite delete_insert_delete; eauto. }
Qed.

Lemma list_to_set_delete (l : local_loc) (L : local_env):
  ((list_to_set (FMapAList.alist_remove AstLib.eq_dec_raw_id l L).*1) : gset _) =
    ((list_to_set L.*1) : gset local_loc) ∖ {[ l ]}.
Proof.
  induction L; eauto.
  { cbn. set_solver. }
  cbn.
  destruct (negb (RelDec.rel_dec l a.1)) eqn: H; cbn; eauto.
  { assert (Hneq: l ≠ a.1).
    { rewrite negb_true_iff in H.
      by rewrite <- RelDec.neg_rel_dec_correct in H. }
    rewrite H. cbn. rewrite IHL. set_solver. }
  { assert (Heq: l = a.1).
    { rewrite negb_false_iff in H. by rewrite RelDec.rel_dec_correct in H. }
    subst. rewrite H. set_solver. }
Qed.

Lemma list_to_set_insert x v (l : local_env) :
  (list_to_set (FMapAList.alist_add AstLib.eq_dec_raw_id x v l).*1 : gset _) =
    {[x]} ∪ (list_to_set l.*1 : gset _).
Proof.
  induction l.
  { cbn. set_solver. }
  cbn.
  destruct (negb (RelDec.rel_dec x a.1)) eqn: H; cbn; eauto.
  { assert (Hneq: x ≠ a.1).
    { rewrite negb_true_iff in H.
      by rewrite <- RelDec.neg_rel_dec_correct in H. }

    assert (Heq : {[x]} ∪ ({[a.1]} ∪ list_to_set l.*1) =
                    {[a.1]} ∪ ({[x]} ∪ (list_to_set l.*1 : gset _)))
      by set_solver.
    rewrite Heq; clear Heq. rewrite -IHl.
    cbn. set_solver. }
  { assert (Heq: x = a.1).
    { rewrite negb_false_iff in H. by rewrite RelDec.rel_dec_correct in H. }
    subst. rewrite -IHl. set_solver. }
Qed.

Lemma list_to_set_foldr_local_env (bs : local_env) :
  (list_to_set (foldr (λ '(x, dv), FMapAList.alist_add AstLib.eq_dec_raw_id x dv) [] bs).*1 : gset _)
  = (list_to_set bs.*1).
Proof.
  induction bs; eauto.
  cbn. destruct a; cbn. rewrite -IHbs.
  rewrite list_to_set_delete.

  remember (list_to_set (foldr (λ '(x, dv), FMapAList.alist_add AstLib.eq_dec_raw_id x dv) [] bs).*1).
  clear.

  unfold_leibniz.

  split; rewrite !elem_of_union elem_of_difference; [|intuition];
  destruct (decide (x ∈ y)); intuition.
  destruct (decide (x ∈ ({[r]} : gset _))); intuition.
Qed.

Lemma list_to_map_foldr_local_env (bs : local_env) :
  (list_to_map (foldr (λ '(x, dv), FMapAList.alist_add AstLib.eq_dec_raw_id x dv) [] bs) : gmap _ _)
  = list_to_map bs.
Proof.
  induction bs; eauto.
  cbn. destruct a; cbn. rewrite -IHbs.
  rewrite list_to_map_delete_alist.

  remember (list_to_map (foldr (λ '(x, dv), FMapAList.alist_add AstLib.eq_dec_raw_id x dv) [] bs)).
  by rewrite insert_delete_insert.
Qed.

Lemma alist_find_to_map_Some A (x : LLVMAst.raw_id) l v:
  FMapAList.alist_find AstLib.eq_dec_raw_id x l = Some v <->
  (list_to_map l : gmap _ A) !! x = Some v.
Proof.
  induction l; eauto.
  split; intros.
  { destruct IHl.
    cbn in H. destruct a.
    destruct (RelDec.rel_dec x r) eqn: Hx; inversion H; subst.
    { cbn. rewrite RelDec.rel_dec_correct in Hx; subst.
      by rewrite lookup_insert. }
    { cbn. rewrite -RelDec.neg_rel_dec_correct in Hx; subst.
      rewrite lookup_insert_ne; eauto.
      rewrite H; eauto. } }
  { destruct IHl.
    cbn in H. destruct a. cbn.
    destruct (RelDec.rel_dec x r) eqn: Hx; inversion H; subst.
    { cbn. rewrite RelDec.rel_dec_correct in Hx; subst.
      by rewrite lookup_insert. }
    { cbn. rewrite -RelDec.neg_rel_dec_correct in Hx; subst.
      rewrite lookup_insert_ne; eauto.
      cbn in *. rewrite lookup_insert_ne in H; eauto.
      rewrite H1; eauto. } }
Qed.

Lemma alist_find_dom_None {A} (id : LLVMAst.raw_id) l :
  id ∉ dom (list_to_map l : gmap _ A) ->
  FMapAList.alist_find AstLib.eq_dec_raw_id id l = None.
Proof.
  induction l; eauto.
  cbn. destruct a; cbn.
  intros.
  destruct (RelDec.rel_dec id r) eqn: Hid; eauto.
  { rewrite RelDec.rel_dec_correct in Hid; subst. set_solver. }
  { rewrite -RelDec.neg_rel_dec_correct in Hid; subst.
    eapply IHl; eauto. set_solver. }
Qed.

Lemma alist_find_dom_Some {A} (id : LLVMAst.raw_id) l :
  id ∈ dom (list_to_map l : gmap _ A) ->
  is_Some (FMapAList.alist_find AstLib.eq_dec_raw_id id l).
Proof.
  induction l; [ set_solver | ].
  destruct a; cbn; intros.
  destruct (RelDec.rel_dec id r) eqn: Hid; eauto.
  { rewrite -RelDec.neg_rel_dec_correct in Hid; subst.
    eapply IHl; eauto. set_solver. }
Qed.


Require Import Coq.Program.Equality.

Lemma dvalue_has_dtyp_serialize dv1 dv2 τ:
  dvalue_has_dtyp dv1 τ ->
  dvalue_has_dtyp dv2 τ ->
  length (serialize_dvalue dv1) = length (serialize_dvalue dv2).
Proof.
  intros H1 H2.
  pose proof (sizeof_serialized H1).
  pose proof (sizeof_serialized H2).
  rewrite -(Nat2N.id (length (serialize_dvalue dv1))).
  rewrite -(Nat2N.id (length (serialize_dvalue dv2))).
  rewrite H H0. done.
Qed.

(* List-related utility *)
Lemma list_filter_subseteq {A} f (l : list A):
  List.filter f l ⊆ l.
Proof.
  induction l; eauto.
  cbn. destruct (f a) eqn: Ha; set_solver.
Qed.

Lemma elem_of_fst_list_some {A B} (x : A) (l : list (A * B)):
  x ∈ l.*1 ->
  ∃ (n : nat) v, l !! n = Some (x, v).
Proof.
  induction l; [ cbn; set_solver | ].
  intros; eauto. cbn in *.
  rewrite elem_of_cons in H.
  destruct H.
  { destruct a; subst. exists 0, b. done. }
  { specialize (IHl H). destruct IHl as (?&?&?).
    exists (S x0); eauto. }
Qed.

Lemma list_some_elem_of_fst {A B} (l : list (A * B)) i x v:
  l !! i = Some (x, v) ->
  x ∈ l.*1.
Proof.
  revert i.
  induction l; try set_solver.
  cbn. induction i; set_solver.
Qed.

Lemma no_dup_fst_list_some {A B} (l l' : list (A * B)) i j x v v':
  NoDup l.*1 ->
  NoDup l'.*1 ->
  l.*1 = l'.*1 ->
  l !! i = Some (x, v) ->
  l' !! j = Some (x, v') ->
  i = j.
Proof.
  revert l' i j x v v'.
  induction l; cbn; [ done | ].
  intros.
  inversion H; subst; destruct a; cbn in *.
  destruct l'; cbn in *; [ done | ].
  destruct p; cbn in *.
  inversion H0; subst; eauto.
  clear H H0. inversion H1; subst; eauto; clear H1.
  revert x v' a0 b l' j H3 H8 H9 H4 H2 H6.
  induction i; subst.

  { cbn in *. intros; inversion H2; subst; eauto.
    intros. destruct j; [ set_solver | ].
    cbn in *. clear -H3 H8.
    exfalso. apply H8.
    by eapply list_some_elem_of_fst. }

  { cbn; intros.
    destruct j.
    { cbn in *. inversion H3; subst.
      exfalso. apply H6.
      by eapply list_some_elem_of_fst. }

    f_equiv. eapply IHl; eauto. }
Qed.

Lemma list_lookup_insert_list_to_set {A B} `{Countable A}
  (k : nat) a (b b': B) (l : list (A * B)):
  l !! k = Some (a, b') ->
  (list_to_set (<[k := (a, b)]> l).*1 : gset _) = (list_to_set l.*1 : gset _).
Proof.
  revert k a b; induction l; [ done | ].
  intros k. revert a l IHl.
  induction k; cbn; intros.
  { inversion H0; subst; eauto. }
  f_equiv; eauto.
Qed.

Lemma list_insert_fst {A B} k a b (l : list (A * B)):
  (<[k:=(a, b)]> l).*1 = <[k := a]> (l.*1).
Proof.
  revert k a b; induction l; eauto.
  cbn.
  intros. destruct a; cbn.
  destruct k; eauto.
  cbn. by f_equiv.
Qed.

Lemma list_insert_snd {A B} k a b (l : list (A * B)):
  (<[k:=(a, b)]> l).*2 = <[k := b]> (l.*2).
Proof.
  revert k a b; induction l; eauto.
  cbn.
  intros. destruct a; cbn.
  destruct k; eauto.
  cbn. by f_equiv.
Qed.

Lemma list_lookup_snd {A B} i a b (l : list (A * B)):
  l !! i = Some (a, b) ->
  l.*2 !! i = Some b.
Proof.
  revert i a b; induction l; cbn; [ done | ].
  intros.
  destruct i; eauto.
  destruct a; cbn in H; inversion H; done.
Qed.

Lemma big_sepL_delete_insert {PROP A}
  `{BiAffine PROP} (Φ : nat → A → PROP) (l : list A) (i : nat) (v: A) :
    ([∗ list] k↦y ∈ l, if decide (k = i) then emp else Φ k y) -∗
    ([∗ list] k↦y ∈ <[i := v]> l, if decide (k = i) then emp else Φ k y).
Proof.
  iInduction l as [| ] "H" forall (i v Φ); [ cbn; iIntros "H"; done | ].
  cbn. destruct i; eauto. cbn.
  destruct (decide (0 = S i)); [ lia | ].
  iIntros "HΦ". iDestruct "HΦ" as "(HΦ & Hi)"; iFrame.
  iSpecialize ("H" $! i).
  iApply big_sepL_mono. Unshelve.
  3 : exact (fun k y => if decide (k = i) then emp else Φ (S k) y)%I.
  { intros; cbn; eauto.
    destruct (decide (S k = S i)); subst; eauto.
    destruct (decide (k = i)); try lia; done. }
  iApply "H".

  iApply big_sepL_mono. Unshelve.
  3 : exact (fun k y => if decide (S k = S i) then emp else Φ (S k) y)%I.
  { intros; cbn; eauto.
    destruct (decide (k = i)); subst; eauto.
    destruct (decide (S k = S i)); try lia; done. }
  done.
Qed.

Lemma big_sepL2_insert {PROP A B} `{BiAffine PROP}
  (l : list A) (l' : list B) (Φ : A -> B -> PROP) a b (i : nat) :
  Φ a b -∗
  ([∗ list] v_t1;v_s1 ∈ l; l', Φ v_t1 v_s1) -∗
  ([∗ list] v_t1;v_s1 ∈ <[ i := a ]> l ; <[ i := b ]> l', Φ v_t1 v_s1).
Proof.
  revert a b i.
  iInduction l as [ | ] "IH" forall (l' Φ).
  { cbn. iIntros (???) "HΦ Hl".
    iDestruct (big_sepL2_nil_inv_l with "Hl") as %Hl; subst; done. }
  iIntros (x y i).
  iInduction i as [ | ] "IHi" forall (x y).
  { cbn. iIntros "HΦ Hl".
    iDestruct (big_sepL2_cons_inv_l with "Hl") as (???) "(HΦ' & Hl')".
    subst; cbn.
    iFrame. }

  cbn. iIntros "HΦ Hl".
  iDestruct (big_sepL2_cons_inv_l with "Hl") as (???) "(HΦ' & Hl')".
  subst; cbn.
  iFrame. iApply ("IH" with "HΦ Hl'").
Qed.

Lemma big_opM_delete_singleton_lookup
  {K B} (A : cmra) `{Countable K} `{!EqDecision K} `{!Countable K}
    (m : gmap K B) (f : _ -> A) (i : K):
  ([^ op map] k↦y ∈ base.delete i m, {[k := f y]}) !! i = None.
Proof.
  induction m using map_ind; cbn.
  { rewrite delete_empty. rewrite big_opM_empty.
    by rewrite lookup_empty. }
  { destruct (decide  (i = i0)).
    { subst. by rewrite delete_insert_delete. }
    { rewrite delete_insert_ne; auto.
      assert (([^ op map] k↦y ∈ <[i0:=x]> (base.delete i m), {[k := f y]}) ≡
        {[i0 := f x]} ⋅ ([^ op map] k↦y ∈ base.delete i m, {[k := f y]})).
      { rewrite big_opM_insert; eauto.
        rewrite lookup_delete_ne; eauto. }
      repeat red in H1.
      specialize (H1 i). inversion H1; subst.
      { rewrite lookup_op in H3.
        rewrite IHm in H3.
        rewrite op_None_right_id in H3.
        assert (i0 <> i) by auto.
        apply (lookup_singleton_ne i0 i (f x)) in H5.
        rewrite H5 in H3; inversion H3. }
      { by rewrite -H3. } } }
Qed.

Lemma alist_find_dom_None' {A} (id : LLVMAst.raw_id) (l : list (_ * A)) :
  id ∉ (list_to_set l.*1 : gset _) ->
  FMapAList.alist_find AstLib.eq_dec_raw_id id l = None.
Proof.
  revert id.
  induction l; eauto.
  intros; cbn; intros.

  destruct a; cbn; intros.
  destruct (RelDec.rel_dec id r) eqn: Hid; eauto.
  { exfalso.  apply H.
    rewrite RelDec.rel_dec_correct in Hid; subst.
    cbn. set_solver. }
  { rewrite -RelDec.neg_rel_dec_correct in Hid; subst.
    eapply IHl; eauto. set_solver. }
Qed.

Lemma foldr_local_env (bs : local_env) :
  NoDup bs.*1 ->
  (foldr
     (λ '(x, dv), FMapAList.alist_add AstLib.eq_dec_raw_id x dv)
     [] bs) = bs.
Proof.
  induction bs; eauto.
  cbn in *. destruct a; eauto; intros.
  inversion H; subst; eauto.
  rewrite IHbs; eauto.
  clear IHbs H.

  induction bs; cbn; eauto.
  cbn. rewrite /FMapAList.alist_add.
  intros.
  simpl.
  destruct (negb (RelDec.rel_dec r a.1)) eqn: H; cbn; eauto.
  { assert (Hneq: r ≠ a.1).
    { rewrite negb_true_iff in H.
      by rewrite <- RelDec.neg_rel_dec_correct in H. }
    f_equiv. destruct a. f_equiv.
    cbn in H2; cbn in H3. inversion H3; subst.
    assert (r ∉ bs.*1) by set_solver.
    specialize (IHbs H0 H5).
    rewrite /FMapAList.alist_add in IHbs.
    inversion IHbs.
    by rewrite H6. }
  { assert (Heq: r = a.1).
    { rewrite negb_false_iff in H. by rewrite RelDec.rel_dec_correct in H. }
    rewrite /FMapAList.alist_add in IHbs.
    destruct a; cbn in *; subst.
    inversion H3; subst.
    exfalso. set_solver. }
Qed.


Lemma assoc_lookup {A B} {RD : RelDec.RelDec (@eq A)}
  {RC: RelDec.RelDec_Correct RD} k (m : list (A * B)) (v : B):
  NoDup m.*1 ->
  Util.assoc k m = Some v <->
  ∃ (i : nat), m !! i = Some (k, v).
Proof.
  split.
  { revert k v.
    induction m; eauto.
    { cbn; intros; inversion H0. }
    { cbn in H; intros. apply NoDup_cons in H; destruct H.
      destruct a. cbn in H0. destruct_if.
      - cbn in *. exists 0%nat; cbn; auto.
        rewrite RelDec.rel_dec_correct in H2; by subst.
      - rewrite -RelDec.neg_rel_dec_correct in H2; subst.
        cbn in *. specialize (IHm H1 _ _ H0). destruct IHm.
        exists (S x); auto. } }
  { revert k v.
    induction m; eauto.
    { cbn; intros; set_solver. }
    { cbn in H; intros. apply NoDup_cons in H; destruct H.
      destruct H0; cbn. destruct a.
      cbn in *.
      destruct x.
      - cbn in *. inv H0.
        destruct (RelDec.rel_dec k k) eqn: Hk; auto.
        rewrite -RelDec.neg_rel_dec_correct in Hk; done.
      - cbn in *.
        specialize (IHm H1 k v (ltac:(exists x; auto))).
        assert (k <> a).
        { intro; subst;
          apply list_some_elem_of_fst in H0; done. }
        destruct (RelDec.rel_dec k a) eqn: Hk; auto.
        rewrite RelDec.rel_dec_correct in Hk; done. } }
Qed.

(* Some util tactics *)

Ltac reflectb :=
  repeat match goal with
  | [ H : NoDup_b _ = true |- _] => apply NoDup_b_NoDup in H
  | [ H : Nat.eqb _ _ = true |- _] => apply Nat.eqb_eq in H
  | [ H : forallb _ _ = true |- _] => rewrite forallb_True in H
  end.

Ltac destructb :=
  repeat match goal with
  | [H : Is_true (forallb _ _) |- _] =>
      rewrite forallb_True in H
  | [H : Is_true (_ && _) |- _] =>
      apply andb_prop_elim in H; destruct H
  | [H : Is_true _ |- _] =>
      apply Is_true_true_1 in H
  | [H : _ /\ _ |- _] => destruct H
  end.

Ltac resolveb := destructb; reflectb.

Ltac nodup :=
  repeat match goal with
  | [H : NoDup (_ :: _) |- _] =>
      apply NoDup_cons in H; destructb
  end.

Ltac base := repeat (iSplitL ""; first done).

Lemma lookup_defn_Some_lookup {B} (f : dvalue) fn (v : B) :
  Util.assoc f fn = Some v -> ∃ i, fn !! i = Some (f, v).
Proof.
  revert f v.
  induction fn; cbn; intros;
    intros; try solve [inv H]; eauto.
  destruct a. destruct_if.
  - reldec; eauto. exists 0%nat; eauto.
  - specialize (IHfn _ _ H2). destruct IHfn.
    exists (S x); cbn; auto.
Qed.

Lemma lookup_defn_Some {B} (fn : dvalue) r (x v : B) i:
  NoDup r.*1 ->
  Util.assoc fn r = Some x ->
  r !! i = Some (fn, v) ->
  v = x.
Proof.
  revert fn x v i.
  induction r; cbn; intros; try solve [inv H0].
  destruct a. destruct_if; reldec.
  { nodup. cbn in *.
    apply lookup_cons_Some in H1. destruct H1.
    - destruct H1; by inv H3.
    - destruct H1.
      by apply list_some_elem_of_fst in H3. }
  { apply lookup_cons_Some in H1. nodup. destruct H1.
    - destruct H1. by inv H5.
    - destruct H1.
      eapply IHr; eauto. }
Qed.


(* ========================================================================== *)

(* List-related helpers *)

Lemma list_fst_fmap_filter {A B} `{RelDec.RelDec A} L l:
  (List.filter (λ x : A * B, negb (RelDec.rel_dec l x.1)) L).*1 =
    List.filter (λ x, negb (RelDec.rel_dec l x)) L.*1.
Proof.
  revert l. induction L; eauto.
  intros; cbn.
  destruct a; cbn.
  destruct (negb (RelDec.rel_dec l a)) eqn: Ha; cbn; [ by f_equiv | done ].
Qed.

#[global] Instance list_empty {A} : Empty (list A).
  constructor; eauto.
Defined.

#[global] Instance list_singleton {A}: base.Singleton A (list A).
  repeat red. intro. exact (X :: []).
Defined.

#[global] Instance list_union {A} `{EqDecision A} : Union (list A).
  repeat intro. apply (list_union X X0).
Defined.

#[global] Instance list_semiset {A} `{EqDecision A}: SemiSet A (list A).
constructor; try split; repeat intro; try set_solver.
- repeat red in H. by apply elem_of_list_union in H.
- by apply elem_of_list_union.
Qed.

Lemma no_dup_alist_add {V} `{EqDecision V} L l (v' : V) :
  NoDup L.*1 ->
  NoDup ((FMapAList.alist_add AstLib.eq_dec_raw_id l v' L).*1).
Proof.
  intros.
  revert l v'.
  induction L; eauto; [ constructor; set_solver | ].
  inversion H; subst; eauto.
  intros.
  specialize (IHL H3 l v').
  destruct a.
  destruct (RelDec.rel_dec l r) eqn: Heq; [ cbn in *; rewrite Heq; cbn; eauto | ].
  cbn in *. rewrite Heq; cbn.
  inversion IHL; subst; eauto.
  constructor; cycle 1.
  { constructor; try set_solver.
    intro; apply H2.
    eapply elem_of_weaken; eauto.
    rewrite list_fst_fmap_filter. apply list_filter_subseteq. }
  { rewrite not_elem_of_cons; split; eauto.
    by apply RelDec.neg_rel_dec_correct. }
Qed.


(* ========================================================================== *)

From ITree Require Import ITree Eq.
From Paco Require Import paco.

(* ITree-related helpers *)

Lemma euttge_tauR_inv E R (e1 e2 : itree E R):
  e1 ≳ Tau e2 ->
  e1 ≳ e2.
Proof.
  intros H. rewrite (itree_eta e2) in H.
  punfold H; pstep; red. red in H.
  remember (observe e1).
  remember (observe e2).
  clear Heqi Heqi0 e1 e2. cbn in H.
  remember ((TauF {| _observe := i0 |})).
  induction H; subst; try inversion Heqi1; eauto; pclearbot.
  - constructor; eauto.
    punfold REL. rewrite H0 in REL. done.
  - constructor; eauto.
  - inversion CHECK.
Qed.

Lemma euttge_tauR_inv' E R (e1 e2 : itree E R):
  e1 ≳ Tau e2 ->
  ∃ e1', observe e1 = TauF e1'.
Proof.
  intros H. rewrite (itree_eta e2) in H.
  punfold H; red in H.
  remember (observe e1).
  remember (observe e2).
  clear Heqi Heqi0 e1 e2. cbn in H.
  remember ((TauF {| _observe := i0 |})).
  induction H; subst; try inversion Heqi1; eauto; pclearbot.
  inversion CHECK.
Qed.
