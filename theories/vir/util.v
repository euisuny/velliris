From iris.algebra Require Import gmap auth.
From iris.prelude Require Import options.
From iris.proofmode Require Export tactics.
Set Default Proof Using "Type*".

From velliris.utils Require Import tactics.
From velliris.vir Require Export vir.
From Vellvm Require Import Handlers.Handlers.

From Vellvm.Utils Require Export FMapAList.

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

Fixpoint list_eqb (l l' : list dvalue): bool :=
  match l, l' with
    | nil, nil => true
    | x :: tl, x' :: tl' =>
        Coqlib.proj_sumbool (@dvalue_eq_dec x x') && list_eqb tl tl'
    | _ , _ => false
  end.

Lemma list_eqb_eq l l' :
  list_eqb l l' <-> l = l'.
Proof.
  split; revert l'; induction l; cbn;
    destruct l'; intros; try done.
  { apply andb_prop_elim in H. destruct H.
    destruct (Coqlib.proj_sumbool dvalue_eq_dec) eqn: H'; try done.
    apply Coqlib.proj_sumbool_true in H'; subst.
    f_equiv; eauto. }
  { inv H.
    specialize (IHl _ eq_refl).
    destruct (list_eqb l' l'); try done.
    compute.
    destruct (dvalue_eq_dec (d1:=d) (d2:=d)) eqn: Hd; eauto. }
Qed.


(* ========================================================================== *)

(* List-related helpers *)

Lemma list_filter_filter {A} f (l : list A):
  List.filter f l = filter f l.
Proof.
  induction l; eauto.
  cbn. destruct (decide (f a)); destruct (f a); try inversion i;
  by try rewrite IHl.
Qed.

Lemma list_fst_fmap_filter {A B} `{RelDec.RelDec A} L l:
  (filter (λ x : A * B, negb (RelDec.rel_dec l x.1)) L).*1 =
    filter (λ x, negb (RelDec.rel_dec l x)) L.*1.
Proof.
  revert l. induction L; eauto.
  intros; cbn.
  destruct a; cbn.
  destruct (decide (negb (RelDec.rel_dec l a))) eqn: Ha; cbn; [ by f_equiv | done ].
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

(* ========================================================================== *)
#[global] Instance RelDec_EqDecision {K : Type}
  {RelEq : RelDec.RelDec (@eq K)}
  {RelEq_Correct : RelDec.RelDec_Correct RelEq} :
  EqDecision K.
Proof.
  repeat intro.
  destruct (RelDec.rel_dec x y) eqn: Heq.
  { assert (x = y).
    { by apply RelDec.rel_dec_correct. }
    by constructor. }
  { assert (x <> y).
    { by apply RelDec.neg_rel_dec_correct. }
    by constructor. }
Defined.
(* ========================================================================== *)

(* [alist]-related util functions *)

Arguments alist_find [_ _ _ _].
Arguments alist_add [_ _ _ _].
Arguments alist_remove [_ _ _ _].


Section alist_properties.

  Context {K : Type}
          {RelEq : RelDec.RelDec (@eq K)}
          {RelEq_Correct : RelDec.RelDec_Correct RelEq}.
  Context {A : Type}.

  Implicit Type l : list (K * A).
  Implicit Type m : list (K * A).

  Lemma no_dup_alist_add l k v :
    NoDup l.*1 ->
    NoDup ((alist_add k v l).*1).
  Proof.
    intros.
    revert k v.
    induction l; eauto; [ constructor; set_solver | ].
    inversion H; subst; eauto.
    intros.
    specialize (IHl H3 k v).
    destruct a.
    destruct (RelDec.rel_dec k k0) eqn: Heq;
      [ cbn in *; rewrite Heq; cbn; eauto | ].
    cbn in *. rewrite Heq; cbn.
    inversion IHl; subst; eauto.
    constructor; cycle 1.
    { constructor; try set_solver.
      intro; apply H2.
      eapply elem_of_weaken; eauto.
      match goal with
        | |- (List.filter ?f ?l).*1 ⊆ ?r =>
            replace (List.filter f l) with (filter f l);
            change r with l.*1
      end; cycle 1.
      { by rewrite list_filter_filter. }
      rewrite list_fst_fmap_filter.
      apply list_filter_subseteq. }
    { rewrite not_elem_of_cons; split; eauto.
      by apply RelDec.neg_rel_dec_correct. }
  Qed.

  Lemma alist_find_app_some f l m (d : A):
    (alist_find f (l ++ m) = Some d <->
    (alist_find f l = Some d \/
    (alist_find f l = None /\
      alist_find f m = Some d)))%list.
  Proof.
    split.
    { induction l; intros; cbn in H.
      { cbn. right; eauto. }
      { destruct a; cbn.
        destruct (RelDec.rel_dec f k) eqn: Heq.
        { left; auto. }
        specialize (IHl H). destruct IHl.
        - inversion H. rewrite H0 H2. by left.
        - right; auto. } }
    { induction l; intros; cbn in H.
      { destruct H; inversion H; auto. }
      { destruct a; cbn; destruct H.
        { destruct (RelDec.rel_dec f k) eqn: Heq; auto. }
        { destruct (RelDec.rel_dec f k) eqn: Heq; auto.
          destruct H. inversion H. } } }
  Qed.

  Lemma alist_find_app_none f l m :
    (alist_find f (l ++ m) = None <->
    (alist_find f l = None /\
      alist_find (V := A) f m = None))%list.
  Proof.
    split.
    {induction l; intros; cbn in H.
    { cbn; eauto. }
    { destruct a; cbn.
      destruct (RelDec.rel_dec f k) eqn: Heq; [ inversion H | ].
      specialize (IHl H). destruct IHl.
      split; auto. } }
    {induction l; intros; cbn in H.
    { destruct H; cbn; eauto. }
    { destruct a; cbn.
      destruct (RelDec.rel_dec f k) eqn: Heq; [ inversion H | ].
      { destruct H; eauto. }
      specialize (IHl H). destruct IHl.
      split; auto. } }
  Qed.

  Lemma alist_find_singleton r f (d d0 : A) :
    alist_find f [(r, d)] = Some d0 ->
    f = r /\ d = d0.
  Proof.
    cbn;intros. destruct (RelDec.rel_dec f r) eqn: Heq; inversion H.
    rewrite RelDec.rel_dec_correct in Heq; auto.
  Qed.

  Lemma alist_find_none f l :
    alist_find (V := A) f l = None ->
    forall k v, In (k, v) l -> k <> f.
  Proof.
    revert f.
    induction l; cbn; intros; auto.
    destruct a; destruct H0.
    { inversion H0; subst.
      destruct (RelDec.rel_dec f k) eqn: Hf; [ inversion H | ].
      rewrite <- RelDec.neg_rel_dec_correct in Hf; auto. }
    { destruct (RelDec.rel_dec f k0) eqn: Hf; [ inversion H | ].
      eapply IHl; eauto. }
  Qed.

  Lemma alist_find_cons_eq :
    ∀ {x l v},
      alist_find x ((x, v) :: l) = Some v.
  Proof.
    intros. cbn. by rewrite eq_dec_eq.
  Qed.

  Lemma alist_not_in_domain :
    ∀ {x r l v},
      r ∉ l.*1 ->
      alist_find x l = Some v ->
      x <> r.
  Proof.
    intros; revert x r v H H0; induction l; eauto.
    intros * Hn Hf; destruct a; cbn in *.
    destruct (RelDec.rel_dec x k) eqn: Hxr0.
    { inv Hf. rewrite RelDec.rel_dec_correct in Hxr0; subst.
      set_solver. }
    eapply IHl; eauto. set_solver.
  Qed.

  Lemma alist_find_Some:
    ∀ {x l v n},
      NoDup l.*1 ->
      l !! n = Some (x, v) ->
      alist_find x l = Some v.
  Proof.
    intros * Hnd; revert n x v; induction l; intros; eauto.
    { inversion H. }
    { destruct a. cbn in *.
      rewrite lookup_cons in H.
      destruct n;
        first inversion H; subst; first apply alist_find_cons_eq.
      apply NoDup_cons in Hnd; destruct Hnd as (?&?).
      eapply IHl in H; eauto.
      pose proof (alist_not_in_domain H0 H) as Hneq.
      apply eq_dec_neq in Hneq; by rewrite Hneq. }
  Qed.

  Lemma alist_find_Some_iff:
    ∀ {x l v},
      NoDup l.*1 ->
      alist_find x l = Some v ↔ ∃ n, l !! n = Some (x, v).
  Proof.
    intros * Hnd; split; cycle 1.
    { intros (?&?); by eapply alist_find_Some. }

    induction l; intros H; first inversion H.
    cbn in *. destruct a.
    setoid_rewrite lookup_cons.
    destruct (RelDec.rel_dec x k) eqn: Heq.
    { inv H. exists 0%nat.
      rewrite RelDec.rel_dec_correct in Heq; by subst. }
    apply NoDup_cons in Hnd; destruct Hnd.
    apply IHl in H; eauto. destruct H.
    by exists (S x0).
  Qed.

End alist_properties.

Lemma alist_add_domain_stable:
  ∀ (L : local_env) (l : local_loc) (v v': local_val),
    (list_to_map L : gmap _ _) !! l = Some v ->
    (list_to_set (alist_add l v' L).*1 =
                  (list_to_set L.*1 : gset _)).
Proof.
  induction L; [ intros; inversion H | ].
  intros. cbn in H. cbn.
  assert
    (Haux: forall a : LLVMAst.raw_id,
      list_to_set
      (List.filter (λ x : LLVMAst.raw_id * uvalue, negb (RelDec.rel_dec a x.1)) L).*1 =
      list_to_set L.*1 ∖ ({[ a ]} : gset _)).
  { clear. induction L.
    - cbn; intros.
      by rewrite difference_disjoint_L.
    - intros. cbn.
      destruct (RelDec.rel_dec a0 a.1) eqn: Ha.
      { rewrite RelDec.rel_dec_correct in Ha; rewrite Ha.
        set_solver. }
      { cbn. rewrite difference_union_distr_l_L.
        rewrite difference_disjoint_L; cycle 1.
        { apply disjoint_singleton_r.
          apply not_elem_of_singleton_2.
          by rewrite RelDec.neg_rel_dec_correct. }
        by rewrite IHL. } }
  destruct (RelDec.rel_dec l a.1) eqn: Ha.
  { rewrite RelDec.rel_dec_correct in Ha; subst.
    rewrite Util.eq_dec_eq.
    cbn. rewrite lookup_insert in H.
    rewrite Haux. clear.

    destruct (decide (a.1 ∈ (list_to_set L.*1 : gset _))).
    { rewrite -union_difference_singleton_L; eauto.
      set_solver. }
    { set_solver. } }

  { rewrite Ha; cbn.
    rewrite -RelDec.neg_rel_dec_correct in Ha.
    rewrite lookup_insert_ne in H; eauto.
    specialize (IHL _ _ v' H).
    rewrite Haux.
    assert (l ∈ (list_to_set L.*1 : gset _)). { set_solver. }
    clear -Ha H0.
    assert ({[l]} ∪ ({[a.1]} ∪ list_to_set L.*1 ∖ {[l]}) =
            {[l]} ∪ ({[a.1]} ∪ list_to_set L.*1) ∖ ({[l]} : gset _)).
    { set_solver. }
    rewrite H.
    rewrite -union_difference_singleton_L; eauto.
    set_solver. }
Qed.

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

Lemma fold_alist_insert_some_eq f l m r d:
  fold_alist (λ (k : LLVMAst.raw_id) (v0 : dvalue)
  (acc : global_env), <[k:=v0]> acc) m l !! f = Some d -> r = f ->
  fold_alist (λ (k : LLVMAst.raw_id) (v0 : dvalue)
  (acc : global_env), <[k:=v0]> acc) (<[r:=d]> m) l !! f = Some d.
Proof.
  revert f m r d.
  induction l; intros; cbn in H; cbn; auto.
  { subst; rewrite lookup_insert; auto. }
  { destruct a. subst.
    destruct (RelDec.rel_dec r0 f) eqn: Hr.
    { rewrite RelDec.rel_dec_correct in Hr. subst.
      rewrite insert_insert. auto. }
    { apply RelDec.neg_rel_dec_correct in Hr.
      rewrite insert_commute; auto. } }
Qed.

Lemma fold_alist_insert_some f l m r d:
  fold_alist (λ (k : LLVMAst.raw_id) (v0 : dvalue)
  (acc : global_env), <[k:=v0]> acc) m l !! f = Some d ->
  (forall d0, r <> f /\
    fold_alist (λ (k : LLVMAst.raw_id) (v0 : dvalue)
      (acc : global_env), <[k:=v0]> acc) (<[r:=d0]> m) l !! f = Some d) \/
  (r = f /\
    fold_alist (λ (k : LLVMAst.raw_id) (v0 : dvalue)
      (acc : global_env), <[k:=v0]> acc) (<[r:=d]> m) l !! f = Some d).
Proof.
  intros.
  destruct (RelDec.rel_dec r f) eqn: Hrf;
    [ rewrite RelDec.rel_dec_correct in Hrf | apply RelDec.neg_rel_dec_correct in Hrf ].
  { right. eapply fold_alist_insert_some_eq in H; eauto. }
  { left. intros; eapply fold_alist_insert_some_neq in H; eauto. }
Qed.

Lemma alist_to_gmap_find_gen f g g' d :
  (alist_find f g = Some d \/
  (alist_find f g = None /\
    g' !! f = Some d)) ->
  (fold_alist
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
  alist_find f g = Some d ->
  (fold_alist
    (λ (k : LLVMAst.raw_id) (v0 : dvalue) (acc : global_env),
        <[k:=v0]> acc) ∅ (rev g)) !! f = Some d.
Proof.
  intros; eapply alist_to_gmap_find_gen; by left.
Qed.

Lemma fold_alist_find_insert r d l l' f d0:
  fold_alist
    (λ (k : LLVMAst.raw_id) (v0 : dvalue) (acc : global_env), <[k:=v0]> acc)
    (<[r := d]>l') l !! f = Some d0 ->
  fold_alist
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
  fold_alist
      (λ (k : LLVMAst.raw_id) (v0 : dvalue) (acc : global_env), <[k:=v0]> acc)
      (<[r := d]> l') l !! f = None <->
  fold_alist
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
  fold_alist
    (λ (k : LLVMAst.raw_id) (v0 : dvalue) (acc : global_env), <[k:=v0]> acc)
    (<[r := d]>l') l !! f = Some d0 ->
  fold_alist
    (λ (k : LLVMAst.raw_id) (v0 : dvalue) (acc : global_env), <[k:=v0]> acc)
    l' l !! f = Some d0 \/
  (fold_alist
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
  fold_alist
        (λ (k : LLVMAst.raw_id) (v0 : dvalue) (acc : global_env), <[k:=v0]> acc)
        ∅ l !! f = None ->
  alist_find f (rev l) = None.
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
  (fold_alist
    (λ (k : LLVMAst.raw_id) (v0 : dvalue) (acc : global_env),
        <[k:=v0]> acc) ∅ (rev g)) !! f = Some d ->
  alist_find f g = Some d.
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

Lemma fold_left_delete_comm {K} `{!EqDecision K} `{!Countable K}
  (f : list K) a {A} (m : gmap K A):
  fold_left (fun m key => base.delete key m) f (base.delete a m) =
  base.delete a (fold_left (fun m key => base.delete key m) f m).
Proof.
  revert a m.
  induction f; cbn; auto.
  intros.
  setoid_rewrite delete_commute. by rewrite IHf.
Qed.

Lemma foldl_delete_comm {K} `{!EqDecision K} `{!Countable K}
  (f : list K) a {A} (m : gmap K A):
  foldl (fun m key => base.delete key m) (base.delete a m) f =
  base.delete a (foldl (fun m key => base.delete key m) m f).
Proof.
  revert a m.
  induction f; cbn; auto.
  intros.
  setoid_rewrite delete_commute. by rewrite IHf.
Qed.

Instance foldl_proper {A B}
  `{LeibnizEquiv A}
  : Proper
    ((@equiv A _ ==> @eq B ==> @equiv A _) ==>
        eq ==> @equiv A _  ==> @equiv A _) (@fold_left A B).
Proof.
  repeat intro; subst.
  revert x y x1 y1 H1 H3.
  induction y0; cbn; eauto.
  intros; eauto.
  apply IHy0; eauto.
  apply H1; eauto.
Qed.

Lemma fold_delete_some_L:
  ∀ (K : Type) (EqDecision0 : EqDecision K) (Countable0 : 
      Countable K) 
    (A : cmra) (a : K) (f : list K),
    a ∉ f
    → ∀ (m2 : gmap K A) (x : A),
      m2 !! a = Some x
      → fold_left (λ (m : gmap K A) (key : K), delete key m) f m2
          !! a = Some x.
Proof.
  intros K EqDecision0 Countable0 A a f; revert a.
  induction f; cbn; intros; eauto.
  apply not_elem_of_cons in H.
  destruct H; eauto.
  apply IHf; eauto.
  by rewrite lookup_delete_ne.
Qed.

Lemma fold_delete_some:
  ∀ (K : Type) (EqDecision0 : EqDecision K) (Countable0 : 
      Countable K) 
    (A : cmra) (a : K) (f : list K),
    a ∉ f
    → ∀ (m2 : gmap K A) (x : A),
      m2 !! a ≡ Some x
      → fold_left (λ (m : gmap K A) (key : K), delete key m) f m2
          !! a ≡ Some x.
Proof.
  intros K EqDecision0 Countable0 A a f; revert a.
  induction f; cbn; intros; eauto.
  apply not_elem_of_cons in H.
  destruct H; eauto.
  apply IHf; eauto.
  by rewrite lookup_delete_ne.
Qed.

Lemma delete_local_update'
  `{!EqDecision K} `{!Countable K} {A : cmra}
  (m1 m2 : gmap K A) i x `{!Exclusive x} :
  m2 !! i ≡ Some x → (m1, m2) ~l~> (delete i m1, delete i m2).
Proof.
  intros Hi. apply local_update_unital=> n mf Hmv Hm; simpl in *.
  split; auto using delete_validN.
  { by apply delete_validN. }
  rewrite Hm=> j; destruct (decide (i = j)) as [<-|].
  - rewrite lookup_op !lookup_delete left_id symmetry_iff dist_None.
    apply eq_None_not_Some=> -[y Hi'].
    move: (Hmv i). rewrite Hm lookup_op Hi Hi' -Some_op. by apply exclusiveN_l.
  - by rewrite lookup_op !lookup_delete_ne // lookup_op.
Qed.

Lemma delete_fold_local_update (K : Type)
  `{!EqDecision K} `{!Countable K}
  {A : cmra} (m1 m2 : gmap K A) (f : list K):
  NoDup f ->
  (∀ i, i ∈ f -> ∃ x, m2 !! i ≡ Some x /\ Exclusive x) ->
  (m1, m2) ~l~>
  (fold_left (fun m key => base.delete key m) f m1,
    fold_left (fun m key => base.delete key m) f m2).
Proof.
  intros Hnd H. revert m1 m2 H.
  induction f; [ by intros | ].
  intros; cbn. apply NoDup_cons in Hnd.
  destruct Hnd as (?&?).
  etrans; [ eapply (IHf _ m1 m2); eauto | ].
  { intros. eapply H. rewrite elem_of_cons; by right. }
  do 2 rewrite fold_left_delete_comm.
  assert (Helem: a ∈ a :: f) by set_solver.
  destruct (H _ Helem) as (?&?&?).
  eapply delete_local_update'; eauto.
  apply fold_delete_some; eauto.
  Unshelve. all :eauto.
Qed.

Lemma delete_fold_local_update_L (K : Type)
  `{!EqDecision K} `{!Countable K}
  {A : cmra}
  (m1 m2 : gmap K A) (f : list K):
  NoDup f ->
  (∀ i, i ∈ f -> ∃ x, m2 !! i = Some x /\ Exclusive x) ->
  (m1, m2) ~l~>
  (fold_left (fun m key => base.delete key m) f m1,
    fold_left (fun m key => base.delete key m) f m2).
Proof.
  intros Hnd H. revert m1 m2 H.
  induction f; [ by intros | ].
  intros; cbn. apply NoDup_cons in Hnd.
  destruct Hnd as (?&?).
  etrans; [ eapply (IHf _ m1 m2); eauto | ].
  { intros. eapply H. rewrite elem_of_cons; by right. }
  do 2 rewrite fold_left_delete_comm.
  assert (Helem: a ∈ a :: f) by set_solver.
  destruct (H _ Helem) as (?&?&?).
  eapply delete_local_update; eauto.
  apply fold_delete_some_L; eauto.
  Unshelve. all :eauto.
Qed.

Lemma big_opM_fold_left_delete_domain {A B}
  {EqDec : EqDecision A} {Cont: Countable A}
  {LE: LeibnizEquiv (gmapUR A (prodR fracR (agreeR B)))}
  (d : list A) (m : gmap A B) :
  NoDup d ->
  dom m ≡ list_to_set d ->
  fold_left (fun m k => base.delete k m) d
    ([^op map] k↦x ∈ m, ({[k := (1%Qp, to_agree x)]}) : gmapUR _ _)
    ≡ (ε : gmapUR _ _).
Proof.
  revert m.
  induction d.
  { intros.
    apply dom_empty_inv in H0; subst; cbn.
    by rewrite big_opM_empty. }
  intros; cbn.
  rewrite fold_left_delete_comm.

  cbn in H0.
  apply dom_union_inv in H0; cycle 1.
  { rewrite NoDup_cons in H. destruct H as (?&?).
    set_solver. }
  destruct H0 as (?&?&?&?&?&?); subst.
  apply NoDup_cons in H. destruct H.
  specialize (IHd x0 H0 H3). cbn in IHd.
  rewrite <- IHd.

  apply dom_singleton_inv in H2; destruct H2 as (?&?); subst.
  rewrite -fold_left_delete_comm.
  eapply foldl_proper; try done.
  { repeat intro; subst; by rewrite H2. }
  rewrite big_opM_union; eauto.
  rewrite {1} /op /cmra_op; cbn -[op].
  rewrite /ucmra_op ; cbn -[op].
  rewrite /gmap_op_instance ; cbn -[op].
  rewrite delete_merge.
  rewrite big_opM_singleton. rewrite delete_singleton.
  rewrite merge_empty_l.
  rewrite /compose {1} /op /cmra_op; cbn.
  rewrite delete_notin; cycle 1.
  { clear IHd H3 H.
    revert a x1 H1.
    induction x0 using map_ind; cbn.
    - rewrite big_opM_empty. set_solver.
    - pose proof (big_opM_insert
        (fun k x => {[ k := (1%Qp, to_agree x)]} ) _ i x H) as H'.
      repeat red in H'. intros.
      specialize (H' a).
      inversion H'; cycle 1.
      { symmetry; done. }
      { assert ({[a := x1]} ##ₘ m). {
          rewrite map_disjoint_insert_r in H1.
          destruct H1; done. }
        specialize (IHx0 _ _ H5).
        rewrite lookup_op in H3.
        rewrite IHx0 in H3.
        rewrite lookup_singleton_ne in H3; first inversion H3.
        clear -H1.
        apply map_disjoint_dom_1 in H1; cbn in H1.
        rewrite dom_singleton in H1.
        rewrite dom_insert in H1.
        set_solver. } }

  repeat red. intros.
  rewrite lookup_omap.
  destruct (([^ op map] k↦y ∈ x0, {[k := (1%Qp, to_agree y)]}) !! i);
    simpl; by constructor.
Qed.

Lemma big_opM_delete_singleton_lookup
  {K B} (A : cmra) `{Countable K} `{!EqDecision K} `{!Countable K}
    (m : gmap K B) (f : _ -> A) (i z: K):
  i <> z ->
  ([^ op map] k↦y ∈ base.delete i m, {[k := f y]}) !! z ≡
  ([^ op map] k↦y ∈ m, {[k := f y]}) !! z.
Proof.
  revert i z f.
  induction m using map_ind; intros; cbn.
  { rewrite delete_empty. rewrite big_opM_empty.
    by rewrite lookup_empty. }
  { intros. destruct (decide (i = i0)).
    { subst. rewrite !delete_insert_delete.

      assert (([^ op map] k↦y ∈ <[i0:=x]> m, {[k := f y]}) ≡
        {[i0 := f x]} ⋅ ([^ op map] k↦y ∈ delete i0 m, {[k := f y]})).
      { rewrite big_opM_insert; eauto.
        rewrite delete_notin; eauto. }
      repeat red in H2. specialize (H2 z).
      inversion H2; subst.
      { rewrite lookup_op in H4.
        rewrite lookup_singleton_ne in H4; eauto.
        rewrite op_None_left_id in H4.
        rewrite -H4. rewrite -H3. f_equiv. by symmetry. }
      { rewrite lookup_op in H5.
        rewrite lookup_singleton_ne in H5; eauto.
        rewrite op_None_left_id in H5.
        rewrite -H4. rewrite -H5. done. } }
    { rewrite delete_insert_ne; auto.
      assert (([^ op map] k↦y ∈ <[i:=x]> (delete i0 m), {[k := f y]}) ≡
        {[i := f x]} ⋅ ([^ op map] k↦y ∈ delete i0 m, {[k := f y]})).
      { rewrite big_opM_insert; eauto.
        rewrite lookup_delete_ne; eauto. }
      do 7 red in H2.
      rewrite H2. clear H2.

      assert (([^ op map] k↦y ∈ <[i:=x]> m, {[k := f y]}) ≡
        {[i := f x]} ⋅ ([^ op map] k↦y ∈ m, {[k := f y]})).
      { by rewrite big_opM_insert. }

      do 7 red in H2.
      rewrite H2. clear H2.

      rewrite !lookup_op.
      f_equiv. by eapply IHm. } }
Qed.

(* ------------------------------------------------------------------------ *)
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
  list_to_map (alist_add x v l) =
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
  (list_to_map (alist_remove l L) : gmap _ _) =
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
  ((list_to_set (alist_remove l L).*1) : gset _) =
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
  (list_to_set (alist_add x v l).*1 : gset _) =
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
  (list_to_set (foldr (λ '(x, dv), alist_add x dv) [] bs).*1 : gset _)
  = (list_to_set bs.*1).
Proof.
  induction bs; eauto.
  cbn. destruct a; cbn. rewrite -IHbs.
  rewrite list_to_set_delete.

  remember (list_to_set (foldr (λ '(x, dv), alist_add x dv) [] bs).*1).
  clear.

  unfold_leibniz.

  split; rewrite !elem_of_union elem_of_difference; [|intuition];
  destruct (decide (x ∈ y)); intuition.
  destruct (decide (x ∈ ({[r]} : gset _))); intuition.
Qed.

Lemma list_to_map_foldr_local_env (bs : local_env) :
  (list_to_map (foldr (λ '(x, dv), alist_add x dv) [] bs) : gmap _ _)
  = list_to_map bs.
Proof.
  induction bs; eauto.
  cbn. destruct a; cbn. rewrite -IHbs.
  rewrite list_to_map_delete_alist.

  remember (list_to_map (foldr (λ '(x, dv), alist_add x dv) [] bs)).
  by rewrite insert_delete_insert.
Qed.

Lemma alist_find_to_map_Some A (x : LLVMAst.raw_id) l v:
  alist_find x l = Some v <->
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
  alist_find id l = None.
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
  is_Some (alist_find id l).
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

Lemma alist_find_dom_None' {A} (id : LLVMAst.raw_id) (l : list (_ * A)) :
  id ∉ (list_to_set l.*1 : gset _) ->
  alist_find id l = None.
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
     (λ '(x, dv), alist_add x dv)
     [] bs) = bs.
Proof.
  induction bs; eauto.
  cbn in *. destruct a; eauto; intros.
  inversion H; subst; eauto.
  rewrite IHbs; eauto.
  clear IHbs H.

  induction bs; cbn; eauto.
  cbn. rewrite /alist_add.
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
    rewrite /alist_add in IHbs.
    inversion IHbs.
    by rewrite H6. }
  { assert (Heq: r = a.1).
    { rewrite negb_false_iff in H. by rewrite RelDec.rel_dec_correct in H. }
    rewrite /alist_add in IHbs.
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
