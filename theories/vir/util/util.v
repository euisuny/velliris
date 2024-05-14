From Coq Require Import Program.Equality.

From velliris.vir Require Export vir.
From Vellvm.Utils Require Export FMapAList.

From iris.algebra Require Import gmap auth.
From iris.prelude Require Import options.
From iris.proofmode Require Export tactics.
Set Default Proof Using "Type*".

Open Scope nat_scope.


(* ------------------------------------------------------------------------ *)
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

(* ------------------------------------------------------------------------ *)
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

(* ------------------------------------------------------------------------ *)
(* Some util tactics *)


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

Ltac nodup :=
  repeat match goal with
  | [H : NoDup (_ :: _) |- _] =>
      apply NoDup_cons in H; destructb
  end.

Ltac reflectb :=
  repeat match goal with
  | [ H : NoDup_b _ = true |- _] => apply NoDup_b_NoDup in H
  | [ H : Nat.eqb _ _ = true |- _] => apply Nat.eqb_eq in H
  | [ H : forallb _ _ = true |- _] => rewrite forallb_True in H
  end.

Ltac resolveb := destructb; reflectb.

Ltac base := repeat (iSplitL ""; first done).

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

(* On [list_intersection] *)
Lemma list_intersection_subset {A} `{EqDecision A} (l l' : list A):
  l ⊆ l' ->
  list_intersection l l' = l.
Proof.
  revert l'.
  dependent induction l; eauto; cbn.
  intros.
  destruct (decide_rel elem_of a l'); try set_solver.
  f_equiv. eapply IHl; set_solver.
Qed.

Lemma list_intersection_eq {A} `{EqDecision A} (l : list A):
  list_intersection l l = l.
Proof.
  apply list_intersection_subset; set_solver.
Qed.

(* ------------------------------------------------------------------------ *)
(* Utility about operators over [list] *)

Lemma eq_fmap {A B} (r_t r_s : list (A * B)) :
  r_t.*1 = r_s.*1 ->
  r_t.*2 = r_s.*2 ->
  r_t = r_s.
Proof.
  revert r_s; induction r_t; intros.
  { destruct r_s; by inv H. }
  destruct r_s; inv H.
  destruct a, p; inv H2; cbn in *; subst.
  inv H0. f_equiv. by apply IHr_t.
Qed.

Lemma list_not_elem_of_remove {A eq_dec} (l : list A) x i:
  x ∉ l ->
  x ∉ (remove eq_dec i l).
Proof.
  revert x i.
  induction l; eauto.
  intros. apply not_elem_of_cons in H. destruct H.
  cbn. destruct (eq_dec i a); auto.
  apply not_elem_of_cons; split; auto.
Qed.

Lemma list_elem_of_remove {A eq_dec} (l : list A) x i:
  i <> x ->
  x ∈ l <->
  x ∈ (remove eq_dec i l).
Proof.
  split; revert x i H; induction l; eauto.
  { intros. apply elem_of_cons in H0. destruct H0; subst.
    { cbn. destruct (eq_dec i a); auto; try done.
      apply elem_of_cons; auto. }
    { cbn. destruct (eq_dec i a); auto; try done.
      apply elem_of_cons; auto. } }
  { intros. cbn in H0.
    destruct (eq_dec i a); auto; subst; try done.
    { apply elem_of_cons; right; eapply IHl; eauto. }
    { apply elem_of_cons in H0.
      destruct H0; subst; apply elem_of_cons; auto.
      right; eapply IHl; eauto. } }
Qed.


Lemma elem_of_snd {A B} `{EqDecision B} l (L : list (A * B)):
  l ∈ L.*2 <-> exists v, (v, l) ∈ L.
Proof.
  split.
  { induction L; cbn; intros; eauto.
    { by apply elem_of_nil in H. }
    { destruct a. cbn in *.
      destruct (decide (l = b)); subst.
      { setoid_rewrite elem_of_cons. eauto. }
      { apply elem_of_cons in H. destruct H; [ done | ].
        specialize (IHL H). destruct IHL.
        setoid_rewrite elem_of_cons; eauto. } } }
  { induction L; cbn; intros; eauto; destruct H.
    { by apply elem_of_nil in H. }
    { destruct a. cbn in *.
      destruct (decide (l = b)); subst.
      { setoid_rewrite elem_of_cons. eauto. }
      { apply elem_of_cons in H.
        destruct H; inv H; try done.
        - cbn in *. apply elem_of_cons; right;
            eapply IHL; eauto.
          exists x; apply elem_of_cons; auto.
        - cbn in *. apply elem_of_cons; right.
          apply IHL; eauto.
          exists x; apply elem_of_cons; auto. } } }
Qed.

Lemma NoDup_remove {A eq_dec} (l : list A) i:
  NoDup l ->
  NoDup (remove eq_dec i l).
Proof.
  revert i.
  induction l; eauto.
  intros; nodup.
  cbn. destruct (eq_dec i a); auto.
  apply NoDup_cons; split; auto.
  by apply list_not_elem_of_remove.
Qed.

Lemma map_Forall_nil {A B} `{EqDecision A} `{Countable A} (m : gmap A B):
  map_Forall (λ (i : A) (_ : B), i ∉ nil) m.
Proof.
  induction m using map_ind; auto.
  - apply map_Forall_empty.
  - apply map_Forall_insert; auto.
    split; eauto. set_solver.
Qed.

(* ========================================================================== *)
(* EqDecision classes. *)

(* Warning: do not change the ordering or weight of these instances;
 Coq Typeclass resolution is fragile. *)

#[global] Instance attr_eq_dec: EqDecision fn_attr.
Proof. solve_decision. Defined.

#[global] Instance RelDec_EqDecision {K : Type}
  {RelEq : RelDec.RelDec (@eq K)}
  {RelEq_Correct : RelDec.RelDec_Correct RelEq} :
  EqDecision K | 10000.
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

  Lemma alist_find_elem_of {x l v} :
    alist_find x l = Some v ->
    x ∈ l.*1.
  Proof.
    induction l ;cbn; intros H ; try inv H; eauto.
    destruct a.
    destruct (RelDec.rel_dec x k) eqn: Heq.
    { inv H1; cbn.
      assert (x = k).
      { by apply RelDec.rel_dec_correct. }
      subst; set_solver. }
    assert (x <> k).
    { by apply RelDec.neg_rel_dec_correct. }
    subst; set_solver.
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


Lemma assoc_list_elem_of_lookup {K V}
  `{EqDecision K} `{Countable K}
  (A B : list (K * V)) (l : K):
  l ∈ A.*1 ->
  list_to_set A.*1 = (list_to_set B.*1 : gset _)->
  exists n v, B !! n = Some (l, v).
Proof.
  intros e Heq.
  eapply (@elem_of_list_to_set K
              (@gset _ _ _)) in e; last typeclasses eauto.
  Unshelve. all : try typeclasses eauto.
  setoid_rewrite Heq in e. clear -e.
  rewrite elem_of_list_to_set in e.
  by apply elem_of_fst_list_some.
Qed.

Lemma list_filter_join {A} f (l : list A):
  List.filter f (List.filter f l) = List.filter f l.
Proof.
  induction l; eauto.
  cbn. destruct (f a) eqn: Hf; eauto.
  cbn. rewrite Hf; f_equiv; done.
Qed.

(* ------------------------------------------------------------------------ *)

(* [Remove_ids] : remove a list of keys from an associative list. *)
Definition remove_ids {K} {R : K -> K -> Prop} {RelDec_R: RelDec.RelDec R} {V}
  (k : list K) (l : alist K V) : alist K V:=
    fold_left (fun acc (x : K) => alist_remove x acc) k l.

Lemma remove_id_cons_alist_add
  {K} {RelDec_R: RelDec.RelDec eq} {RelEq_Correct : RelDec.RelDec_Correct RelDec_R}
  {V} :
  ∀ (k : list K) (l : alist K V) (x : K) (v : V),
    (remove_ids (x :: k) (alist_add x v l)) = remove_ids k (alist_remove x l).
Proof.
  intros k.
  induction k; eauto; cbn; eauto.
  { intros.
    rewrite eq_dec_eq; cbn. rewrite list_filter_join; done. }
  intros.

  intros; rewrite eq_dec_eq; cbn.
  cbn in *. setoid_rewrite eq_dec_eq in IHk; cbn in IHk.
  rewrite !list_filter_join.
  setoid_rewrite <-IHk; eauto.
Qed.

Lemma alist_remove_not_in
  {K} {RelDec_R: RelDec.RelDec eq} {RelEq_Correct : RelDec.RelDec_Correct RelDec_R}
  {V} :
  forall (l : alist K V) x,
  x ∉ l.*1 ->
  alist_remove x l = l.
Proof.
  induction l; eauto.
  intros; cbn; eauto.
  apply not_elem_of_cons in H; destruct H.
  eapply RelDec.rel_dec_neq_false in H; eauto; rewrite H; cbn.
  f_equiv; eauto.
Qed.

Lemma alist_remove_fst_eq {K : Type}
  {RelDec_R : RelDec.RelDec eq}
  {RelDec_C: RelDec.RelDec_Correct RelDec_R} :
  ∀ {V : Type} (l l' : alist K V) (x : K),
    l.*1 = l'.*1 ->
    (alist_remove x l).*1 = (alist_remove x l').*1.
Proof.
  induction l; intros; (destruct l'; inv H; eauto).
  destruct a, p; inv H1. cbn in *; subst.
  destruct_if_goal; cbn; try solve [f_equiv; eauto].
  by eapply IHl.
Qed.

Lemma alist_add_fst_eq {K : Type}
  {RelDec_R : RelDec.RelDec eq}
  {RelDec_C: RelDec.RelDec_Correct RelDec_R} :
  ∀ {V : Type} (l l' : alist K V) (x : K) v v',
    l.*1 = l'.*1 ->
    (alist_add x v l).*1 = (alist_add x v' l').*1.
Proof.
  cbn. intros. f_equiv.
  by apply alist_remove_fst_eq.
Qed.

Lemma big_sepL_alist_remove
  {PROP K} `{BiAffine PROP}
  {RelDec_R: RelDec.RelDec eq} {RelEq_Correct : RelDec.RelDec_Correct RelDec_R}
  {V} :
  forall (l : alist K V) x n v (P : _ -> PROP),
  l !! n = Some (x, v) ->
  NoDup l.*1 ->
  ([∗ list] k↦y ∈ l, if decide (k = n) then emp else P y) -∗
  ([∗ list] '(k, v) ∈ alist_remove x l, P (k, v)).
Proof.
  intros l.
  iInduction l as [ | ] "IH"; [ eauto | ].
  iIntros (k n v P Hlu Hnd) "Hl".
  pose proof (alist_find_Some Hnd Hlu) as Hlf.
  cbn.
  destruct n; cycle 1.
  { cbn in *. destruct a. cbn in *.
    apply NoDup_cons in Hnd; destruct Hnd.
    destruct (RelDec.rel_dec k k0) eqn: Hk.
    { (* absurd. *) exfalso.
      rewrite RelDec.rel_dec_correct in Hk; subst.
      apply H0. clear - Hlu.
      eapply list_some_elem_of_fst; eauto. }
    destruct (decide (0 = S n)%nat) eqn: Heq; [ lia | ]; try rewrite Heq.
    iDestruct "Hl" as "(HP & Hl)"; iFrame.
    iApply "IH"; eauto.
    iApply big_sepL_mono; try done.
    cbn. iIntros (???) "H".
    destruct (decide (S k1 = S n));
    destruct (decide (k1 = n)); try lia;
      try done. }

  destruct (decide (0 = 0))%nat ; try lia; clear e.
  iDestruct "Hl" as "(_ & Hl)".
  cbn in *. destruct a; inv Hlu.
  rewrite eq_dec_eq in Hlf. rewrite eq_dec_eq; cbn; clear Hlf.
  cbn in *.
  assert (List.filter (λ x : K * V, negb (RelDec.rel_dec k x.1)) l = l).
  { induction l; eauto.
    cbn in *. apply NoDup_cons in Hnd; destruct Hnd.
    apply not_elem_of_cons in H0. destruct H0.
    eapply RelDec.rel_dec_neq_false in H0; eauto; rewrite H0; cbn.
    f_equiv; eapply IHl. apply NoDup_cons; eauto; split; try set_solver.
    apply NoDup_cons in H1; destruct H1; eauto. }
  rewrite H0.
  iApply big_sepL_mono; [ | iApply "Hl"]; cbn; eauto.
  intros; destruct y; eauto.
Qed.

Lemma big_sepL2_alist_remove
  {PROP K} `{BiAffine PROP}
  {RelDec_R: RelDec.RelDec eq} {RelEq_Correct : RelDec.RelDec_Correct RelDec_R}
  {V} :
  forall (l l' : alist K V) x n v v' (R : _ -> _ -> PROP),
  l !! n = Some (x, v) ->
  l' !! n = Some (x, v') ->
  NoDup l.*1 ->
  NoDup l'.*1 ->
  ([∗ list] v1; v2 ∈ l.*2; l'.*2, R v1 v2) -∗
  ([∗ list] v1; v2 ∈ (alist_remove x l).*2; (alist_remove x l').*2, R v1 v2).
Proof.
  intros l.
  iInduction l as [ | ] "IH".
Admitted.

Lemma alist_remove_subseteq
  {K} {RelDec_R: RelDec.RelDec eq} {RelEq_Correct : RelDec.RelDec_Correct RelDec_R}
  {V} :
  ∀ (l : alist K V) (x : K), alist_remove x l ⊆ l.
Proof.
  induction l; try set_solver.
  cbn. intros; destruct (RelDec.rel_dec x a.1) eqn: Heq; cbn; try done;
  set_solver.
Qed.

Lemma alist_remove_commut
  {K} {RelDec_R: RelDec.RelDec eq} {RelEq_Correct : RelDec.RelDec_Correct RelDec_R}
  {V} :
  ∀ (l : alist K V) (x y : K),
    alist_remove x (alist_remove y l) = alist_remove y (alist_remove x l).
Proof.
  induction l ; eauto.
  cbn. intros.
  destruct_if_goal; cbn; eauto; rewrite ?H ?H0; eauto.
  f_equiv. eauto.
Qed.

Lemma remove_ids_subseteq
  {K} {RelDec_R: RelDec.RelDec eq} {RelEq_Correct : RelDec.RelDec_Correct RelDec_R}
  {V} :
  ∀ (L : list K) (l : alist K V) (x : K),
  remove_ids L (alist_remove x l) ⊆ remove_ids L l.
Proof.
  intros L; induction L; cbn; eauto.
  { intros. apply alist_remove_subseteq. }
  intros. etransitivity.
  2 : eapply IHL. rewrite alist_remove_commut.
  unfold remove_ids. set_solver.
Qed.

(* ------------------------------------------------------------------------ *)
(** *Defintions useful for manipulating finite maps and their properties *)

(* Codomain of a finite map *)
Definition codomain {A B} `{Countable A} `{EqDecision A}
  (m : gmap A B) := (map_to_list m).*2.

Lemma codomain_empty {A B} `{Countable A} `{EqDecision A}:
  codomain (∅ : gmap A B) = ∅.
Proof.
  rewrite /codomain. by rewrite map_to_list_empty.
Qed.

(* ------------------------------------------------------------------------ *)

(* Filter a finite map given a list of keys [l]. *)
Definition filter_keys {A B} `{Countable A} `{EqDecision A}
  (m : gmap A B) (l : list A) :=
  (filter (fun '(x, _) => x ∈ l) m).

Lemma filter_keys_nil {A B} `{EqDecision A} `{Countable A} (m : gmap A B):
  filter_keys m nil = ∅.
Proof.
  pose proof (map_filter_empty_iff (fun '(x, _) => x ∈ nil) m).
  destruct H0.
  by specialize (H1 (map_Forall_nil m)).
Qed.

Lemma filter_keys_None {A B} `{EqDecision A} `{Countable A}
  (m : gmap A B) l i:
  i ∉ l ->
  filter_keys m l !! i = None.
Proof.
  revert i l.
  induction m using map_ind;
  intros; first set_solver.
  rewrite /filter_keys.
  destruct (decide (i ∈ l)).
  - rewrite map_filter_insert_True ; [ | set_solver].
    rewrite lookup_insert_ne; [ | set_solver].
    eapply IHm; eauto.
  - rewrite map_filter_insert_False ; [ | set_solver].
    rewrite delete_notin; auto.
    eapply IHm; eauto.
Qed.

Lemma filter_keys_Some {A B} `{EqDecision A} `{Countable A}
  (m : gmap A B) l i y:
  m !! i = Some y ->
  i ∈ l ->
  filter_keys m l !! i = Some y.
Proof.
  revert i y m.
  induction m using map_ind;
  intros; first set_solver.
  rewrite /filter_keys.
  apply lookup_insert_Some in H1. destruct H1.
  - destruct H1; subst.
    rewrite map_filter_insert_True ; [ | set_solver].
    by rewrite lookup_insert.
  - destruct H1.
    destruct (decide (i0 ∉ l)).
    { rewrite map_filter_insert_False; [ | set_solver].
      rewrite delete_notin; auto. }
    { assert (i0 ∈ l) by set_solver.
      clear n.
      rewrite map_filter_insert_True; [ | set_solver].
      rewrite lookup_insert_ne; auto. }
Qed.

Lemma filter_keys_Some_inv {A B} `{EqDecision A} `{Countable A}
  l (m : gmap A B) i y:
  filter_keys m l !! i = Some y ->
  m !! i = Some y ∧ i ∈ l.
Proof.
  revert i y l.
  induction m using map_ind;
  rewrite /filter_keys;
  intros; first set_solver.
  destruct (decide (i ∈ l)).
  { rewrite map_filter_insert_True in H1; [ | done].
    apply lookup_insert_Some in H1. destruct H1.
    - destruct H1; subst.
      rewrite lookup_insert; split; eauto.
    - destruct H1; subst.
      rewrite lookup_insert_ne; eauto; split; eauto. }
  { rewrite map_filter_insert_False in H1; [ | set_solver].
    rewrite delete_notin in H1; auto.
    specialize (IHm _ _ _ H1). destruct IHm.
    split; eauto.
    assert (i <> i0) by set_solver.
    rewrite lookup_insert_ne; eauto. }
Qed.

Lemma filter_keys_cons_insert {A B} `{EqDecision A} `{Countable A}
  v l (m : gmap A B) x:
  m !! v = Some x ->
  filter_keys m (v :: l) = <[v := x]> (filter_keys m l).
Proof.
  intros. apply map_eq. intros.
  apply option_eq; intros y.
  rewrite map_lookup_filter_Some.
  split; intros; eauto.
  { destruct H1. apply elem_of_cons in H2.
    destruct H2; subst; eauto.
    - rewrite H0 in H1; inv H1. by rewrite lookup_insert.
    - destruct (decide (i = v)); subst.
      + rewrite H0 in H1; inv H1. by rewrite lookup_insert.
      + rewrite lookup_insert_ne; auto.
        by apply filter_keys_Some. }

  { apply lookup_insert_Some in H1.
    destruct H1; destruct H1; subst; first set_solver.
    apply filter_keys_Some_inv in H2; destruct H2; split; auto.
    set_solver. }
Qed.

Lemma filter_keys_cons_notin {A B} `{EqDecision A} `{Countable A}
  v l (m : gmap A B):
  m !! v = None ->
  filter_keys m (v :: l) = (filter_keys m l).
Proof.
  intros. apply map_eq. intros.
  apply option_eq; intros y.
  rewrite map_lookup_filter_Some.
  split; intros; eauto.
  { destruct H1. apply elem_of_cons in H2.
    destruct H2; subst; eauto.
    - rewrite H0 in H1; inv H1.
    - destruct (decide (i = v)); subst.
      + rewrite H0 in H1; inv H1.
      + apply filter_keys_Some; auto. }

  { apply filter_keys_Some_inv in H1. destruct H1.
    split; auto. set_solver. }
Qed.

Lemma filter_keys_cons_is_Some {A B} `{EqDecision A} `{Countable A}
  v l (m : gmap A B) x:
  is_Some (filter_keys m l !! x) ->
  is_Some (filter_keys m (v :: l) !! x).
Proof.
  revert m x v.
  induction l.
  { intros. rewrite filter_keys_nil in H0.
    destruct H0. set_solver. }

  intros. destruct H0.
  apply filter_keys_Some_inv in H0. destruct H0 as (?&?).
  exists x0.
  apply filter_keys_Some; try done. set_solver.
Qed.

Lemma filter_keys_cons {A B} `{EqDecision A} `{Countable A}
  (m : gmap A B) v l a b:
  filter_keys m l !! a = Some b ->
  filter_keys m (v :: l) !! a = Some b.
Proof.
  intros.
  apply filter_keys_Some_inv in H0.
  destruct H0.
  apply filter_keys_Some; eauto. set_solver.
Qed.

Lemma elem_map_to_list_filter_keys_cons {A B} `{EqDecision A} `{Countable A} v l (m : gmap A B) x:
  x ∈ map_to_list (filter_keys m l) ->
  x ∈ map_to_list (filter_keys m (v :: l)).
Proof.
  intros.
  destruct x.
  rewrite elem_of_map_to_list.
  apply elem_of_map_to_list in H0.
  by apply filter_keys_cons.
Qed.

Lemma codomain_filter_keys_cons {A B} `{EqDecision A} `{Countable A}
  `{EqDecision B}
  v l (m : gmap A B) x:
  x ∈ codomain (filter_keys m l) ->
  x ∈ codomain (filter_keys m (v :: l)).
Proof.
  intros.
  apply elem_of_snd in H0.
  destruct H0.
  apply (elem_map_to_list_filter_keys_cons v) in H0.
  apply elem_of_snd.
  exists x0; eauto.
Qed.

(* ------------------------------------------------------------------------ *)

(* List of keys [l] is contained in the finite map [m] *)
Definition contains_keys {A B} `{Countable A} `{EqDecision A}
  (m : gmap A B) (l : list A) :=
  list_to_set l ⊆ dom m.

(* There is no duplication in the codomain of the finite map [m].  *)
Definition NoDup_codomain {A B} `{Countable A} `{EqDecision A}
  (m : gmap A B) := NoDup (codomain m).

Lemma nodup_codomain_cons_inv {A B} `{EqDecision A} `{Countable A}
  `{EqDecision B} v l (g : gmap A B):
  NoDup (v :: l) ->
  contains_keys g (v :: l) ->
  NoDup_codomain (filter_keys g (v :: l)) ->
  NoDup_codomain (filter_keys g l).
Proof.
  rewrite /contains_keys /NoDup_codomain /filter_keys /codomain.
  revert v l.
  induction g using map_ind; first set_solver.
  cbn; intros.
  rewrite dom_insert in H2. nodup.
  destruct (decide (v = i)); subst.
  { rewrite map_filter_insert_False; auto.
    rewrite delete_notin; auto.
    rewrite map_filter_insert in H3; auto.
    destruct (decide (i ∈ i :: l)); last set_solver.
    rewrite map_to_list_insert in H3; cycle 1.
    { apply map_lookup_filter_None; by left. }
    cbn in H3. nodup.
    erewrite map_filter_strong_ext_1 in H5; eauto.
    { split; intros; destructb; eauto; try set_solver. } }
  { rewrite map_filter_insert in H3; auto.
    rewrite map_filter_insert.
    destruct (decide (i ∈ l)).
    { assert (v ∈ dom m).
      { clear -H2 n.
        apply (difference_mono_r _ _ {[i]}) in H2.
        do 2 rewrite difference_union_distr_l_L in H2.
        rewrite difference_disjoint in H2; [ | set_solver].
        rewrite difference_diag_L in H2.
        rewrite union_empty_l in H2. set_solver. }

      specialize (IHg v (List.remove (decide_rel eq) i l)).
      destruct (decide (i ∈ v :: l)); last set_solver.
      rewrite map_to_list_insert; cycle 1.
      { apply map_lookup_filter_None; by left. }
      rewrite map_to_list_insert in H3; cycle 1.
      { apply map_lookup_filter_None; by left. }
      cbn in *.
      clear H5 e0. nodup.

      assert ({[v]} = ({[v]} ∖ {[i]} : gset _)) by set_solver.
      apply not_elem_of_dom in H0.
      assert (dom m = ({[i]} ∪ dom m) ∖ {[i]}) by set_solver.

      apply NoDup_cons; split; cycle 1.
      { erewrite map_filter_strong_ext_1;
          first eapply IHg; eauto.
        { apply NoDup_cons; eauto. split.
          { by apply list_not_elem_of_remove. }
          { by apply NoDup_remove. } }
        { rewrite list_to_set_remove; auto.
          rewrite H6; clear H6.
          rewrite -difference_union_distr_l_L.
          rewrite H7. set_solver. }
        { erewrite map_filter_strong_ext_1 in H5; eauto.
          split; intros; destructb.
          - split; eauto.
            apply elem_of_cons in H8; destructb; destruct H8; subst;
              auto; first set_solver.
            apply elem_of_cons; right.
            apply list_elem_of_remove; eauto.
            intro; subst.
            assert (is_Some (m !! i0)) by eauto.
            rewrite -elem_of_dom in H10. done.
          - split; eauto.
            apply elem_of_cons in H8; destructb; destruct H8; subst;
              auto; first set_solver.
            apply elem_of_cons; right.
            rewrite list_elem_of_remove; eauto.
            intro; subst.
            assert (is_Some (m !! i0)) by eauto.
            rewrite -elem_of_dom in H10. done. }
        { split; intros; destructb; split; eauto.
          - assert (is_Some (m !! i0)) by eauto.
            rewrite -list_elem_of_remove; eauto.
            rewrite -elem_of_dom in H10.
            intro; subst; set_solver.
          - assert (is_Some (m !! i0)) by eauto.
            rewrite list_elem_of_remove; eauto.
            rewrite -elem_of_dom in H10.
            intro; subst; set_solver. } }

      intro; apply H3; eauto.

      by apply codomain_filter_keys_cons. }
    { destruct (decide (i ∈ v :: l)); first set_solver.

      rewrite delete_notin; eauto.
      rewrite delete_notin in H3; eauto.
      specialize (IHg v (List.remove (decide_rel eq) i l)).
      apply not_elem_of_dom in H0.
      erewrite map_filter_strong_ext_1;
          first eapply IHg; eauto.
      { apply NoDup_cons; eauto. split.
        { by apply list_not_elem_of_remove. }
        { by apply NoDup_remove. } }
      { cbn. rewrite list_to_set_remove; auto.
        set_solver. }
      { erewrite map_filter_strong_ext_1 in H3; eauto.
        split; intros; destructb.
        - split; eauto.
          apply elem_of_cons in H5; destructb; destruct H5; subst;
            auto; first set_solver.
          apply elem_of_cons; right.
          apply list_elem_of_remove; eauto.
          intro; subst.
          assert (is_Some (m !! i0)) by eauto.
          rewrite -elem_of_dom in H7. done.
        - split; eauto.
          apply elem_of_cons in H5; destructb; destruct H5; subst;
            auto; first set_solver.
          apply elem_of_cons; right.
          rewrite list_elem_of_remove; eauto.
          intro; subst.
          assert (is_Some (m !! i0)) by eauto.
          by rewrite -elem_of_dom in H7. }
      { split; intros; destructb; split; eauto.
        - assert (is_Some (m !! i0)) by eauto.
          apply list_elem_of_remove; set_solver.
        - assert (is_Some (m !! i0)) by eauto.
          rewrite list_elem_of_remove; eauto.
          apply elem_of_dom in H7. intro; set_solver. } } }
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
