From Coq Require Import String List Program.Equality.
From iris.prelude Require Import options.
From iris.base_logic.lib Require Export gen_heap ghost_map.
From iris.base_logic Require Import gset_bij.

From ITree Require Import
  ITree Eq
  Interp.InterpFacts Interp.RecursionFacts Events.StateFacts TranslateFacts.

From Vellvm Require Import Syntax.LLVMAst Syntax.DynamicTypes
  Semantics.InterpretationStack Handlers Utils.Util Semantics.LLVMEvents.

From Equations Require Import Equations.

From Paco Require Import paco.

From velliris.logic Require Import satisfiable.
From velliris.program_logic Require Import program_logic.
From velliris.vir Require Import
  vir spec globalbij heapbij frame_laws primitive_laws bij_laws logical_relations
  fundamental_exp.
From velliris.utils Require Import no_event.

Set Default Proof Using "Type*".

Import ListNotations.
Import SemNotations.


(* ------------------------------------------------------------------------ *)
(* Utility about general operators *)

  (* Move : Utils*)
  Lemma codomain_empty {A B} `{Countable A} `{EqDecision A}:
    codomain (∅ : gmap A B) = ∅.
  Proof.
    rewrite /codomain. by rewrite map_to_list_empty.
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

(* ------------------------------------------------------------------------ *)
(* Utility *)

  (* TODO Move: VIR Utility *)
  Lemma dvalue_has_dtyp_eq :
    forall dv dt,
      dvalue_has_dtyp_fun dv dt = true <-> dvalue_has_dtyp dv dt.
  Proof.
    split; first apply dvalue_has_dtyp_fun_sound.
    intros.
    induction H; eauto.
    - induction H; auto.
      cbn; apply andb_true_intro; split; auto.
    - cbn. revert sz H; induction xs; auto.
      { cbn. intros; subst. by compute. }
      { cbn. intros; subst.
      forward IHxs.
      { intros; apply IH; apply in_cons; auto. }
      forward IHxs.
      { intros; apply IHdtyp; apply in_cons; auto. }
      specialize (IHxs _ eq_refl).
      apply andb_true_iff in IHxs. destruct IHxs; auto.
      cbn; apply andb_true_intro; split; auto.
      - cbn; apply andb_true_intro; split; auto.
        apply IH; auto. by constructor.
      - rewrite Nat2N.id.
        apply Nat.eqb_refl. }
  Qed.

  (* TODO Move: Utility *)
  Lemma lmapsto_lookup_list γ (i : list frame_names) L (args : local_env) :
    (list_to_set args.*1 : gset _) = list_to_set L.*1 ->
    ghost_map_auth (local_name (current_frame i)) 1 (list_to_map L) -∗
    ([∗ list] '(l, v) ∈ args, lmapsto γ (current_frame i) l v)  ==∗
    ⌜list_to_map args = (list_to_map L : gmap _ _)⌝ ∗
    ghost_map_auth (local_name (current_frame i)) 1 (list_to_map L) ∗
    ([∗ list] '(l, v) ∈ args, lmapsto γ (current_frame i) l v).
  Proof.
    iIntros (Hdom) "Hauth Hmap".
    iDestruct (lmapsto_no_dup with "Hmap") as %Hmap_nd.
    rewrite -!dom_list_to_map_L in Hdom.
    iInduction args as [ | ] "IH" forall (L i Hdom).
    { cbn in *; destruct L; set_solver. }

    cbn in *. rewrite dom_insert_L in Hdom.
    assert (a.1 ∈ dom (list_to_map L : gmap _ _)) by set_solver.
    rewrite (union_difference_singleton_L a.1 (dom (list_to_map L)))
      in Hdom; [ | set_solver ].

    apply elem_of_dom in H. destruct H.

    rewrite -(insert_delete (list_to_map L) a.1 x); auto.
    destruct a; cbn.
    iDestruct "Hmap" as "(H & Hmap)".
    iDestruct (lmapsto_lookup with "Hauth H") as %Hlu.
    rewrite lookup_insert in Hlu; inv Hlu.
    apply NoDup_cons in Hmap_nd; destruct Hmap_nd.
    cbn in *.
    assert (dom (list_to_map args : gmap _ _) = (dom (list_to_map L : gmap _ _) ∖ {[ r ]} : gset _)).
    { assert (r ∉ dom (list_to_map args : gmap _ _)).
      { rewrite dom_list_to_map; set_solver. }
      eapply union_cancel_l_L; set_solver. }
    rewrite -dom_delete_L in H2.
    rewrite -list_to_map_delete_alist in H2.
    iSpecialize ("IH" $! H1 _ _ H2).
    rewrite {3} lmapsto_eq /lmapsto_def.
    iDestruct (ghost_map_delete with "Hauth H") as ">H".
    rewrite delete_insert; last by rewrite lookup_delete.
    rewrite -{1} list_to_map_delete_alist.
    iSpecialize ("IH" with "H Hmap").
    iDestruct "IH" as ">(%Heq & H & Hv)"; iFrame.
    rewrite Heq. rewrite list_to_map_delete_alist; iFrame.
    iSplitL ""; first done.

    iDestruct (ghost_map_insert with "H") as ">(H & Hv)".
    { by setoid_rewrite lookup_delete. }
    iFrame. rewrite lmapsto_eq; done.
  Qed.

  (* TODO Move: Utility *)
  Lemma list_to_map_insert_nodup (i : nat) x v (l : local_env):
    NoDup l.*1 ->
    (∃ v', l !! i = Some (x, v')) ->
    list_to_map (<[i := (x, v)]> l) = <[ x := v ]> (list_to_map l : gmap _ _).
  Proof.
    revert i x v.
    induction l; cbn; intros.
    { inversion H0. set_solver. }
    destruct H0 as (?&?).
    apply NoDup_cons in H; destruct H.
    destruct i; cbn; inv H0.
    { cbn; by rewrite insert_insert. }
    rewrite IHl; eauto.

    destruct (decide (x = a.1)).
    { subst. exfalso. apply H.
      eapply list_some_elem_of_fst; eauto. }
    { rewrite insert_commute; auto. }
  Qed.

  (* TODO Move: Utility *)
  Lemma raw_id_eqb_eq id id' :
    raw_id_eqb id id' <-> id = id'.
  Proof.
    split; intros; destruct id, id'; try inversion H;
      cbn in H; try f_equiv.
    - apply String.eqb_eq. destruct (s =? s0)%string; auto.
    - apply Z.eqb_eq. destruct (n =? n0)%Z; auto.
    - apply Z.eqb_eq. destruct (n =? n0)%Z; auto.
    - subst. rewrite /raw_id_eqb.
      rewrite String.eqb_refl; done.
    - subst. rewrite /raw_id_eqb.
      rewrite Z.eqb_refl; done.
    - subst. rewrite /raw_id_eqb.
      rewrite Z.eqb_refl; done.
  Qed.


  (* TODO: Move utils *)
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

  Lemma lookup_defn_cons_None {B} fn x (v : B) tl:
    lookup_defn fn ((x,v) :: tl) = None <->
    fn <> x /\ lookup_defn fn tl = None.
  Proof.
    split; revert fn x v; induction tl; cbn; intros; eauto;
      destruct_if.
    { split; eauto;
      by apply RelDec.neg_rel_dec_correct in H0. }
    { destruct a; destruct_if.
      apply RelDec.neg_rel_dec_correct in H0, H1; split; eauto. }
    { destruct H.
      rewrite RelDec.neg_rel_dec_correct in H; by rewrite H. }
    { destruct H, a; destruct_if.
      rewrite RelDec.neg_rel_dec_correct in H; by rewrite H. }
  Qed.

  Lemma lookup_defn_cons_Some {B} fn x (v : B) tl y:
    lookup_defn fn ((x,v) :: tl) = Some y <->
    (fn = x /\ v = y) \/ (fn <> x /\ lookup_defn fn tl = Some y).
  Proof.
    split; revert fn x v; induction tl; cbn; intros; eauto;
      destruct_if.
    { left.
      rewrite RelDec.rel_dec_correct in H0; auto. }
    { left.
      rewrite RelDec.rel_dec_correct in H0; auto. }
    { destruct a.
      destruct_if.
      - rewrite RelDec.rel_dec_correct in H1; auto.
        apply RelDec.neg_rel_dec_correct in H0; auto.
      - apply RelDec.neg_rel_dec_correct in H1; auto.
        apply RelDec.neg_rel_dec_correct in H0; auto. }
    { destruct H; [ destruct H | ].
      - rewrite -RelDec.rel_dec_correct in H; rewrite H; subst; auto.
      - inv H; inv H1. }
    { destruct H; [ destruct H | destruct a ].
      - rewrite -RelDec.rel_dec_correct in H; rewrite H; subst; auto.
      - destruct H. destruct_if.
        + apply RelDec.neg_rel_dec_correct in H; by rewrite H.
        + apply RelDec.neg_rel_dec_correct in H; by rewrite H. }
  Qed.

  Lemma lookup_defn_Some_In {B} f fn (v : B) :
    lookup_defn f fn = Some v -> In (f, v) fn.
  Proof.
    revert f v.
    induction fn; cbn; intros;
      intros; try solve [inv H]; eauto.
    destruct a. destruct_if.
    - reldec; eauto.
    - right; by apply IHfn.
  Qed.

  Lemma lookup_defn_None_In {B} f fn :
    lookup_defn f fn = None -> not (∃ (v : B), In (f, v) fn).
  Proof.
    revert f.
    induction fn; cbn; intros;
      repeat intro; try solve [inv H]; eauto; destruct H0; auto.
    destruct a. destruct_if.
    reldec; eauto. destruct H0.
    - inv H0. apply H1; auto.
    - eapply IHfn; eauto.
  Qed.

  Lemma lookup_defn_None_elem {B} f (fn : list (_ * B)) :
    lookup_defn f fn = None <-> f ∉ fn.*1.
  Proof.
    revert f.
    split.
    { induction fn; cbn; intros;
      repeat intro; try solve [inv H]; eauto; try set_solver.
      destruct a. destruct_if.
      reldec; eauto.
      apply elem_of_cons in H0.
      destruct H0; try done.
      eapply IHfn; eauto. }

    { induction fn; cbn; intros;
      repeat intro; try solve [inv H]; eauto; try set_solver.
      destruct a. cbn in H.
      apply not_elem_of_cons in H. destruct H.
      destruct_if_goal; reldec; try done.
      by eapply IHfn. }
  Qed.

(* ------------------------------------------------------------------------ *)

  Definition instrE_conv : forall T, instr_E T -> expr vir_lang T :=
      (λ (T : Type) x, Vis (instrE_conv T x) Monad.ret).

  Definition base {R1 R2} : exprO (Λ := vir_lang) R1 -d> exprO (Λ := vir_lang) R2 -d> iPropI Σ :=
    fun e_t e_s =>
    (∃ (v_t : R1) (v_s : R2), ⌜e_t = Ret v_t⌝ ∗ ⌜e_s = Ret v_s⌝)%I.

  Lemma contains_base_tauL {R1 R2} Ψ :
    □ (∀ x y, (base (R1 := R1) (R2 := R2) (go x) (go y) ∗ Ψ x y) ∗-∗ Ψ x y) -∗
    □ (∀ x y, Ψ (TauF x) y -∗ Ψ (observe x) y).
  Proof.
    iIntros "#H".
    iModIntro. iIntros (??) "HΨ".
    iSpecialize ("H" $! (TauF x) y).
    iDestruct "H" as "(H1 & H2)".
    iSpecialize ("H2" with "HΨ").
    iDestruct "H2" as "(H2 & _)".
    iDestruct "H2" as (???) "H2".
    inversion H.
  Qed.

  Lemma contains_base_tauR {R1 R2} Ψ :
    □ (∀ x y, (base (R1 := R1) (R2 := R2) (go x) (go y) ∗ Ψ x y) ∗-∗ Ψ x y) -∗
    □ (∀ x y, Ψ x (TauF y) -∗ Ψ x (observe y)).
  Proof.
    iIntros "#H".
    iModIntro. iIntros (??) "HΨ".
    iSpecialize ("H" $! x (TauF y)).
    iDestruct "H" as "(H1 & H2)".
    iSpecialize ("H2" with "HΨ").
    iDestruct "H2" as "(H2 & _)".
    iDestruct "H2" as (???) "%H2".
    inversion H2.
  Qed.

  Lemma sim_expr'_tau_inv {R1 R2} (e_t:exprO R1) (e_s:exprO R2)
      (Φ : exprO R1 -d> exprO R2 -d> iPropI Σ) :
      □ (∀ x y, (base x y ∗ Φ x y) ∗-∗ Φ x y) -∗
      Tau e_t ⪯ Tau e_s [[ Φ ]] -∗ e_t ⪯ e_s [[ Φ ]].
  Proof.
    iIntros "#Hl H".
    rewrite /sim_expr' /sim_coind'.
    iIntros (??) "SI".
    iSpecialize ("H" with "SI"). iMod "H".
    iApply sim_indF_tau_invR.
    { iIntros (??) "H". rewrite /lift_rel.
      iDestruct "H" as (????) "(SI & %Ht & %Hs & H)".
      iSpecialize ("Hl" with "H"). iDestruct "Hl" as "(Hl & _)".
      iDestruct "Hl" as (???) "%H2".
      subst. apply simpobs in Hs.
      setoid_rewrite interp_state_ret in Hs. by apply eqit_inv in Hs. }
    iApply sim_indF_tau_invL.
    { iIntros (??) "H". rewrite /lift_rel.
      iDestruct "H" as (????) "(SI & %Ht & %Hs & H)".
      iSpecialize ("Hl" with "H"). iDestruct "Hl" as "(Hl & _)".
      iDestruct "Hl" as (???) "%H2".
      subst. apply simpobs in Ht.
      setoid_rewrite interp_state_ret in Ht. by apply eqit_inv in Ht. }
    eauto.
  Qed.


  (* TODO Move to [vir.v] *)
  Lemma instr_conv_call :
    forall d dv e attrs,
      instr_conv (trigger (Call d dv e attrs)) ≅
        vis (ExternalCall d dv e (FNATTR_Internal :: attrs)) (fun x => Tau (Ret x)).
  Proof.
    intros. rewrite /instr_conv.
    rewrite interp_vis. setoid_rewrite interp_ret.
    rewrite {1}/subevent /resum /ReSum_inl /cat /Cat_IFun /inl_ /Inl_sum1.
    rewrite /resum /ReSum_id /id_ /Id_IFun.
    simp instrE_conv. rewrite bind_trigger.
    reflexivity.
  Qed.

(* ------------------------------------------------------------------------ *)

  (* LATER : move *)
  Lemma sim_expr_exception_vis {R R2} (e : _ R) s0 (k : _ -> _ R2) Φ:
    ⊢ e ⪯ vis (Exception.Throw (print_msg s0)) k [{ Φ }].
  Proof.
    rewrite sim_expr_eq /sim_expr_.
    iIntros (??) "SI". iModIntro.
    rewrite /interp_L2.
    rewrite StateFacts.interp_state_vis; cbn; rewrite /add_tau.
    cbn; rewrite /pure_state. rewrite bind_tau !bind_vis.
    iApply sim_coind_tauR.
    iApply sim_coind_exc.
  Qed.

  Lemma sim_expr_UB {R R2} (e : _ R) s0 (k : _ -> _ R2) Φ:
    ⊢ e ⪯ vis (ThrowUB s0) k [{ Φ }].
  Proof.
    rewrite sim_expr_eq /sim_expr_.
    iIntros (??) "SI". iModIntro.
    rewrite /interp_L2.
    rewrite StateFacts.interp_state_vis; cbn; rewrite /add_tau.
    cbn; rewrite /pure_state. rewrite bind_tau !bind_vis.
    iApply sim_coind_tauR.
    iApply sim_coind_ub.
  Qed.

(* ------------------------------------------------------------------------ *)

  (* Unfold all the sum injections used by [subevent ]*)
  Ltac unwrap_event e :=
    repeat
      match goal with
      | |- context[?f e] => rewrite /f
      end;
    repeat
      match goal with
      | |- context[?f (@inl1 ?E1 ?E2 ?X e)] =>
          progress
            unwrap_event (@inl1 E1 E2 X e)
      | |- context[?f (@inr1 ?E1 ?E2 ?X e)] =>
          progress
            unwrap_event (@inr1 E1 E2 X e)
      end.

  (* TODO WIP : Move after working on these *)
  Ltac simp_subevent :=
    match goal with
      | |- context [subevent _ ?e] =>
          unwrap_event e;
          try simp instrE_conv
    end.

  Lemma instr_conv_noncall:
    forall X (e : exp_E X),
      instr_conv (trigger e) ≅ vis e (fun x => Tau (Ret x)).
  Proof.
    intros. rewrite /instr_conv.
    rewrite interp_vis. setoid_rewrite interp_ret.
    rewrite bind_vis.
    unwrap_event e;
      destruct_match_goal;
      [ unwrap_event l |
        unwrap_event s; destruct_match_goal] ;
      match goal with
        | [ H : _ X |- _ ] => rename H into e
      end; unwrap_event e;
      simp instrE_conv;
      rewrite /instr_to_L0;
      by setoid_rewrite bind_ret_l.
  Qed.

  (* TODO: Move *)
  Instance subev_expE_L0 Ev `{Ev -< exp_E} : Ev -< language.L0 vir_lang.
  Proof.
    repeat red in H.
    repeat intro.
    specialize (H _ X).
    pose (exp_to_L0 H) as H'. exact H'.
  Defined.

  Lemma instr_conv_noncall':
    forall X Ev (e : Ev X) `{Ev -< exp_E},
      instr_conv (trigger e) ≅ vis e (fun x => Tau (Ret x)).
  Proof.
    intros. rewrite /instr_conv.
    rewrite interp_vis. setoid_rewrite interp_ret.
    rewrite bind_vis.
    simp_subevent. unwrap_event (H X e).
    destruct_match_goal;
      by setoid_rewrite bind_ret_l.
  Qed.

  Ltac itree_simp e :=
    lazymatch e with
    (* Conversion lemmas *)
    | exp_conv (Ret _) => rewrite exp_conv_ret
    | exp_conv (bind _ _) => rewrite exp_conv_bind
    | exp_conv (ITree.bind _ _) => rewrite exp_conv_bind
    | instr_conv (trigger (Call _ _ _ _)) =>
        rewrite instr_conv_call
    | instr_conv (trigger _) =>
        rewrite instr_conv_noncall +
        rewrite instr_conv_noncall'
    | instr_conv (Ret ?x) => rewrite (instr_conv_ret x)
    | instr_conv (Ret _) => rewrite instr_conv_ret
    | instr_conv (bind _ _) => rewrite instr_conv_bind
    | instr_conv (ITree.bind _ _) => rewrite instr_conv_bind
    | L0'expr_conv (Ret _) => rewrite L0'expr_conv_ret
    | L0'expr_conv (bind _ _) => rewrite L0'expr_conv_bind
    | L0'expr_conv (ITree.bind _ _) => rewrite L0'expr_conv_bind

    (* Basic rewrite *)
    | ITree.bind _ (fun x => Ret x) => rewrite bind_ret_r
    | ITree.bind (Ret ?r) ?k => rewrite (bind_ret_l r k)
    | ITree.bind (Ret _) _ => rewrite bind_ret_l
    | ITree.bind (ITree.bind _ _) _ => rewrite bind_bind
    | ITree.bind ?e _ => progress itree_simp e

    (* Interp-related laws *)
    | interp ?f (Ret ?x) => rewrite (interp_ret f x)
    | interp _ (Ret _) => rewrite interp_ret
    | interp ?f (ITree.bind ?t ?k) => rewrite (interp_bind f t k)
    | interp ?f (translate ?t ?k) => rewrite (interp_translate f t k)
    | interp _ (translate _ _) => rewrite interp_translate

    (* Specific to level translations *)
    | interp (λ T e, Vis (instrE_conv T (exp_to_instr e)) (λ x : T , Ret x)) _ =>
        rewrite (eq_itree_interp _ _ eq2_exp_to_L0); last done
    end.

  Ltac Tau := iApply sim_expr_tau.

  Ltac sim_expr_simp e :=
    match e with
    (* Event translation adjustment *)
    | sim_expr _ (L0'expr_conv (translate instr_to_L0' _))
               (L0'expr_conv (translate instr_to_L0' _)) =>
        iApply instr_to_L0'
    | sim_expr _ (instr_conv (translate exp_to_instr _))
               (instr_conv (translate exp_to_instr _)) =>
        iApply exp_conv_to_instr
    (* Vis to [trigger] *)
    | sim_expr _ (Vis _ _) (Vis _ _ ) =>
        iApply sim_expr_vis
    | sim_expr _ (vis _ _) (vis _ _ ) =>
        iApply sim_expr_vis
    (* Some symbolic execution under ITree rewrites *)
    | sim_expr _ ?l ?r =>
      (* Try doing ITree rewriting on both sides if possible *)
      itree_simp l + itree_simp r
    end.

  Ltac Cut := iApply sim_expr_bind.

  Ltac Simp := repeat
    lazymatch goal with
    | |- environments.envs_entails _ (bupd ?e) =>
        iModIntro
    | |- environments.envs_entails _ ?e =>
        sim_expr_simp e
    end.

  Ltac Base :=
    Simp;
    repeat Tau;
    match goal with
    (* Base case *)
    | |- environments.envs_entails _
        (sim_expr _ (Ret _) (Ret _)) =>
        iApply sim_expr_base
    end.

(* ------------------------------------------------------------------------ *)
  (* Useful facts for instr reflexivity  *)

  Lemma lift_exp_conv_map_monad {A B}
    (f : A -> _ B) (e : list A) P Q :
    □ (∀ x, P x x -∗
          exp_conv (f x) ⪯ exp_conv (f x)
          [{ (x_t, x_s), Q x_t x_s }]) -∗
    □ ([∗ list] _ ↦x ∈ e, P x x) -∗
    exp_conv (map_monad f e) ⪯
    exp_conv (map_monad f e)
    [{ (r_t, r_s),
      ([∗ list] _ ↦x_t;x_s ∈ r_t;r_s, Q x_t x_s)}].
  Proof.
    iIntros "#H #CI".
    iInduction e as [] "IHl".
    { cbn. Simp. Base.
      iExists _,_; do 2 (iSplitL ""; [done |]); done. }
    { cbn. Simp.
      iDestruct "CI" as "[HP CI]".
      iSpecialize ("H" with "HP").
      Cut.
      iApply sim_expr_bupd_mono; [ | iApply "H"].
      iIntros (??) "HI".
      iDestruct "HI" as (??->->) "HQ".
      Simp.
      iApply sim_expr_bind.
      iSpecialize ("IHl" with "CI").
      iApply (sim_expr_bupd_mono with "[HQ]"); [ | iApply "IHl"].
      iIntros (??) "HI".
      iDestruct "HI" as (??->->) "HQL".
      Simp. Base.
      do 2 iExists _; do 2 (iSplitL ""; [ done | ]).
      iApply big_sepL2_cons; iFrame. }
  Qed.

  Lemma lift_instr_conv_map_monad {A B}
    (f : A -> _ B) (e1 e2 : list A) P Q :
    □ (∀ x y, P x y -∗
          instr_conv (f x) ⪯ instr_conv (f y)
          [{ (x_t, x_s), Q x_t x_s }]) -∗
    □ ([∗ list] x;y ∈ e1;e2, P x y) -∗
    instr_conv (map_monad f e1) ⪯
    instr_conv (map_monad f e2)
    [{ (r_t, r_s),
      ([∗ list] x_t;x_s ∈ r_t;r_s, Q x_t x_s)}].
  Proof.
    iIntros "#H #CI".
    iInduction e2 as [] "IHl" forall (e1).
    { iDestruct (big_sepL2_nil_inv_r with "CI") as %Hx; subst; cbn.
      cbn. Simp. Base.
      iExists _,_; do 2 (iSplitL ""; [done |]); done. }
    { cbn.
      iDestruct (big_sepL2_cons_inv_r with "CI") as (???) "(CI1 & CI2)";
        subst; cbn.
      Simp.
      iDestruct "CI" as "[HP CI]".
      iSpecialize ("H" with "HP"). Cut.
      iApply sim_expr_bupd_mono; [ | iApply "H"].
      iIntros (??) "HI".
      iDestruct "HI" as (??->->) "HQ".
      Simp. Cut.
      iSpecialize ("IHl" with "CI").
      iApply (sim_expr_bupd_mono with "[HQ]"); [ | iApply "IHl"].
      iIntros (??) "HI".
      iDestruct "HI" as (??->->) "HQL".
      Base.
      do 2 iExists _; do 2 (iSplitL ""; [ done | ]).
      iApply big_sepL2_cons; iFrame. }
  Qed.

  (* LATER: Generalize this helper lemma to any triple that is lifted with *)
  (*   [map_monad] *)
  Lemma denote_exp_map_monad (e: list (texp dtyp)) C i_t i_s A_t A_s :
    code_inv C i_t i_s A_t A_s -∗
    instr_conv
      (map_monad (λ '(t, op), translate exp_to_instr (denote_exp (Some t) op)) e)
      ⪯
    instr_conv
      (map_monad (λ '(t, op), translate exp_to_instr (denote_exp (Some t) op)) e)
      [{ (e_t, e_s), code_inv C i_t i_s A_t A_s
                       ∗ [∗ list] _↦x_t;x_s ∈ e_t;e_s, uval_rel x_t x_s }].
  Proof.
    iIntros "CI".
    iInduction e as [] "IHl".
    { cbn. rewrite /instr_conv.
      rewrite interp_ret. iApply sim_expr_base.
      iExists _,_; do 2 (iSplitL ""; [done |]); iFrame; done. }
    { cbn. rewrite /instr_conv.
      rewrite interp_bind.
      destruct a; cbn; iApply sim_expr_bind.
      iApply exp_conv_to_instr.
      iApply sim_expr_bupd_mono; cycle 1.
      { iApply (expr_logrel_refl with "CI"); eapply H. }
      iIntros (??) "H".
      iDestruct "H" as (????) "(Hv & CI)".
      rewrite H H0 !bind_ret_l; clear e_t e_s H H0.
      do 2 rewrite interp_bind.
      iModIntro; iApply sim_expr_bind.
      iSpecialize ("IHl" with "CI").
      iApply (sim_expr_bupd_mono with "[Hv]"); [ | iApply "IHl"].
      cbn. iIntros (e_t e_s) "H".
      iDestruct "H" as (?? Ht Hs) "(CI & H)";
        rewrite Ht Hs !bind_ret_l !interp_ret.
      iApply sim_expr_base. iModIntro.
      iExists _, _; do 2 (iSplitL ""; [ done | ]).
      rewrite big_sepL2_cons; iFrame. }
  Qed.

(* ------------------------------------------------------------------------ *)

  (* TODO: Move to [logical_relations] *)
  Definition CFG_attributes (defs : CFG.mcfg dtyp) :=
    dc_attrs <$> (CFG.m_declarations defs).

  Definition defs_names {T FnBody} (defs : list (definition T FnBody)) :=
    (fun f => dc_name (df_prototype f)) <$> defs.

  Definition CFG_names (defs : CFG.mcfg dtyp) :=
    defs_names (CFG.m_definitions defs).

  Definition filter_keys {A B} `{Countable A} `{EqDecision A}
    (m : gmap A B) (l : list A) :=
    (filter (fun '(x, _) => x ∈ l) m).

  Definition codomain {A B} `{Countable A} `{EqDecision A}
    (m : gmap A B) := (map_to_list m).*2.

  Definition NoDup_codomain {A B} `{Countable A} `{EqDecision A}
    (m : gmap A B) := NoDup (codomain m).

  Definition contains_keys {A B} `{Countable A} `{EqDecision A}
    (m : gmap A B) (l : list A) :=
    list_to_set l ⊆ dom m.

  Definition CFG_WF (defs: CFG.mcfg dtyp) (g_t g_s : global_env) :=
    let funs := CFG.m_definitions defs in
    (length (CFG.m_declarations defs) = length (CFG.m_definitions defs)) /\
    NoDup (CFG_names defs) /\
    Forall fun_WF funs /\
    Forall (fun x => dc_attrs x = nil) (CFG.m_declarations defs) /\
    contains_keys g_t (CFG_names defs) /\
    contains_keys g_s (CFG_names defs) /\
    (* No aliasing or duplicated function address storing in globals *)
    NoDup_codomain (filter_keys g_t (CFG_names defs)) /\
    NoDup_codomain (filter_keys g_s (CFG_names defs)).

  Definition fundefs_rel_WF
    (F_t F_s : list (dvalue * _)) (Attr_t Attr_s : list (list fn_attr)) :=
    ((∀ i fn_s v_s,
        ⌜F_s !! i = Some (fn_s, v_s)⌝ -∗
        ∃ fn_t v_t,
          ⌜F_t !! i = Some (fn_t, v_t)⌝ ∗
          dval_rel fn_t fn_s ∗
          ⌜Attr_t !! i = Some nil⌝ ∗
          ⌜Attr_s !! i = Some nil⌝ ∗
          ⌜fun_WF v_t⌝ ∗ ⌜fun_WF v_s⌝) ∗
      (∀ i, ⌜F_s !! i = None -> F_t !! i = None⌝))%I.


  (* TODO: Move to [logical_relations]--[auxiliary properties ] *)
  Lemma global_names_cons_lookup {T FnBody}
    f (l : list (definition T FnBody)) (g : global_env):
    contains_keys g (defs_names (f :: l)) ->
    is_Some (g !! dc_name (df_prototype f)).
  Proof.
    intros.
    setoid_rewrite fmap_cons in H; cbn in H.
    apply elem_of_dom. set_solver.
  Qed.

  Lemma contains_keys_cons_inv {T FnBody}
    (l : list (definition T FnBody)) (g : global_env) x:
    contains_keys g (defs_names (x :: l)) ->
    dc_name (df_prototype x) ∈ dom g /\ contains_keys g (defs_names l).
  Proof.
    intros. unfold contains_keys in H. cbn in H.
    apply union_subseteq in H.
    destruct H; split; eauto.
    set_solver.
  Qed.

  Arguments defs_names : simpl never.
  Arguments CFG_names /.

  Lemma mcfg_defs_keys_extend:
    ∀ (f : definition dtyp (CFG.cfg dtyp))
      (l : list (definition dtyp (CFG.cfg dtyp)))
      (g : global_env) (x : dvalue) (r : list dvalue),
      g !! dc_name (df_prototype f) = Some x ->
      dc_name (df_prototype f) ∉ defs_names l ->
      Permutation r (codomain (filter_keys g (defs_names l))) →
      Permutation (x :: r) (codomain (filter_keys g (defs_names (f :: l)))).
  Proof.
    intros.
    rewrite (filter_keys_cons_insert _ _ _ x); eauto.
    rewrite /codomain.
    rewrite map_to_list_insert; first rewrite H1; eauto.
    apply filter_keys_None; set_solver.
  Qed.

  Lemma NoDup_mcfg_extend:
    ∀ f (l : list (definition dtyp (CFG.cfg dtyp)))
      (g : global_env) (x : dvalue) r,
      g !! f = Some x ->
      NoDup_codomain (filter_keys g (f :: defs_names l)) ->
      f ∉ (defs_names l) ->
      Permutation r (codomain (filter_keys g (defs_names l))) →
      NoDup r → NoDup (x :: r).
  Proof.
    intros * Hin Hnd_l Hf Hc Hnd.
    apply NoDup_cons; split; auto.
    revert g x r Hin Hf Hc Hnd_l Hnd; induction l.
    { intros.
      rewrite filter_keys_nil in Hc.
      rewrite /codomain in Hc.
      rewrite map_to_list_empty in Hc.
      apply Permutation_nil_r in Hc.
      set_solver. }
    intros.
    erewrite filter_keys_cons_insert in Hnd_l; eauto.
    rewrite /NoDup_codomain /codomain in Hnd_l.
    rewrite map_to_list_insert in Hnd_l; cycle 1.
    { apply filter_keys_None.
      intro. apply elem_of_list_fmap in H.
      destruct H as (?&?&?). set_solver. }
    cbn in *.
    nodup. rewrite /codomain in Hc.
    rewrite Hc; auto.
  Qed.
(* ------------------------------------------------------------------------ *)

  (* Local write reflexivity *)
  Lemma local_write_refl C x v_t v_s i_t i_s A_t A_s:
    ⊢ code_inv C i_t i_s A_t A_s -∗ uval_rel v_t v_s -∗
    trigger (LocalWrite x v_t) ⪯ trigger (LocalWrite x v_s)
      [{ (v1, v2), code_inv C i_t i_s A_t A_s }].
  Proof.
    iIntros "CI #Hrel".
    iApply sim_update_si.

    iIntros "%σ_t %σ_s SI".
    iDestruct (local_code_inv with "CI SI") as ">H".
    iDestruct "H" as (?????)
        "(%Hnd_t & %Hnd_s & Hlt & Hls & Hv & #Ha_v & SI & Hd_t & Hd_s
          & HC & Hf_t & Hf_s & #WF & Ha_t & Ha_s)".
    iFrame.

    destruct (decide (x ∈ (vlocal σ_t).1.*1)).
    {
      assert (exists n v, args_t !! n = Some (x, v)).
      { clear -H0 e.
        eapply (@elem_of_list_to_set raw_id
                  (@gset raw_id _ _)) in e; last typeclasses eauto.
        Unshelve. all : try typeclasses eauto.
        setoid_rewrite <-H0 in e. clear -e.
        rewrite elem_of_list_to_set in e.
        by apply elem_of_fst_list_some. }

      assert (exists n v, args_s !! n = Some (x, v)).
      { rewrite H in H0. clear -H0 e.
        eapply (@elem_of_list_to_set raw_id
                  (@gset raw_id _ _)) in e; last typeclasses eauto.
        Unshelve. all : try typeclasses eauto.
        setoid_rewrite <-H0 in e. clear -e.
        rewrite elem_of_list_to_set in e.
        by apply elem_of_fst_list_some. }
      destruct H2 as (?&?&?).
      destruct H3 as (?&?&?).

      iDestruct (lmapsto_no_dup with "Hlt") as "%Hdup_t".
      iDestruct (lmapsto_no_dup with "Hls") as "%Hdup_s".

      iDestruct (big_sepL_delete with "Hlt") as "(Helemt & Hl_t)"; eauto; cbn.
      iDestruct (big_sepL_delete with "Hls") as "(Helems & Hl_s)"; eauto; cbn.

      iApply (sim_expr_bupd_mono with "[Hl_t Hl_s Hd_t Hd_s HC Hv Ha_t Ha_s]");
        [ | iApply (sim_local_write with "Hf_t Hf_s Helemt Helems")].
      iIntros (??) "Hp".
      iDestruct "Hp" as (????) "(Ht & Hs & Hf_t & Hf_s)".

      iModIntro. iExists _,_.
      do 2 (iSplitL ""; [ done | ]); rewrite /CFG_inv.

      pose proof (no_dup_fst_list_some _ _ _ _ _ _ _ Hdup_t Hdup_s H H2 H3); subst.
      iExists (<[x2 := (x, v_t)]> args_t),
              (<[x2 := (x, v_s)]> args_s). iFrame.

      setoid_rewrite (big_sepL_delete (fun i '(l_t, v_t1)=> [ l_t := v_t1 ]t i_t) _ x2 (x, v_t))%I; cycle 1.
      { rewrite list_lookup_insert; eauto.
        by apply lookup_lt_is_Some. }
      setoid_rewrite (big_sepL_delete (fun i '(l_t, v_t1)=> [ l_t := v_t1 ]s i_s) _ x2 (x, v_s))%I; cycle 1.
      { rewrite list_lookup_insert; eauto.
        by apply lookup_lt_is_Some. }
      iFrame.

      do 2 (erewrite list_lookup_insert_list_to_set; eauto);
      rewrite H0 H1; iFrame.
      iFrame "WF".
      cbn; rewrite !list_insert_fst.
      iSplitL ""; first ( iPureIntro; by f_equiv ).

      iSplitL "Hl_t".
      { by iApply big_sepL_delete_insert. }
      iSplitL "Hl_s".
      { by iApply big_sepL_delete_insert. }

      rewrite !list_insert_snd.
      iSplitR ""; last by iFrame "Ha_v".
      iApply (big_sepL2_insert args_t.*2 args_s.*2 uval_rel with "Hrel Hv"). }

    { assert (Hn : x ∉ (list_to_set (vlocal σ_t).1.*1 : gset _)) by set_solver.
      assert (Hn1 : x ∉ (list_to_set (vlocal σ_s).1.*1 : gset _)).
      { rewrite -H1 -H H0; set_solver. }
      iApply (sim_expr_bupd_mono with "[HC Ha_t Ha_s Hv Hlt Hls]");
        [ | iApply (sim_local_write_alloc _ _ _ _ _ _ _ _ Hn Hn1 with "Hd_t Hd_s Hf_t Hf_s")].
      iIntros (??) "Hp".
      iDestruct "Hp" as (????) "(Ht & Hs & Hd_t & Hd_s & Hf_t & Hf_s)".
      iModIntro. iExists _,_.
      do 2 (iSplitL ""; [ done | ]). rewrite /CFG_inv.
      iExists ((x, v_t) :: args_t), ((x, v_s) :: args_s); iFrame.
      cbn. rewrite H0 H1; iFrame.
      iFrame "WF".
      iSplitL "".
      { rewrite H; done. }
      by iFrame "Hrel Ha_v". }
  Qed.

  Lemma call_refl v_t v_s e_t e_s d i_t i_s l A_t A_s C:
    code_inv C i_t i_s A_t A_s -∗
    dval_rel v_t v_s -∗
    ([∗ list] x_t; x_s ∈ e_t;e_s, uval_rel x_t x_s) -∗
    (trigger (ExternalCall d v_t e_t l))
    ⪯
    (trigger (ExternalCall d v_s e_s l))
    [{ (v_t, v_s), uval_rel v_t v_s ∗
                     code_inv C i_t i_s A_t A_s }].
  Proof.
    iIntros "CI #Hv #He".

    rewrite /instr_conv.

    rewrite sim_expr_eq.

    iIntros (σ_t σ_s) "SI".
    unfold interp_L2.
    rewrite /subevent /resum /ReSum_inl /cat /Cat_IFun /inl_ /Inl_sum1
      /resum /ReSum_id /id_ /Id_IFun.
    simp instrE_conv.
    rewrite !interp_state_vis.
    setoid_rewrite interp_state_ret.
    cbn -[state_interp].
    rewrite /handle_stateEff.
    rewrite !bind_vis.

    iApply sim_coindF_vis. iRight.
    iModIntro.
    rewrite /handle_event; cbn -[state_interp].
    rewrite /resum /ReSum_id /id_ /Id_IFun.
    simp handle_call_events. iLeft.
    iFrame.
    iDestruct "CI" as (??) "(?&?&Hs_t&Hs_s&#HWF&?&?&?&?&HC&?)".
    iExists (C, i_t, i_s).
    iSplitL "Hs_t Hs_s HC".
    { rewrite /call_args_eq / arg_val_rel; cbn; iFrame.
      iFrame "HWF".
      iSplitL ""; last done; iSplitL "Hv"; done. }

    iIntros (??) "(SI & V)".
    iDestruct "V" as "(?&?&?&?)".
    cbn -[state_interp].
    iApply sim_coindF_tau; iApply sim_coindF_base.
    rewrite /lift_expr_rel. iModIntro.
    iExists v_t0.1, v_t0.2, v_s0.1, v_s0.2; iFrame.
    rewrite -!itree_eta; do 2 (iSplitL ""; [done |]).
    iExists _,_; do 2 (iSplitL ""; [done |]); iFrame.
    iExists _,_; iFrame. done.
  Qed.


  (* TODO: Move *)
  Lemma instr_call_refl C fn attrs args id  i_t i_s A_t A_s:
    ⊢ (code_inv C i_t i_s A_t A_s -∗
      instr_conv
       (denote_instr (IId id, INSTR_Call fn args attrs)) ⪯
       instr_conv
       (denote_instr (IId id, INSTR_Call fn args attrs))
       [{ (r_t, r_s),
           code_inv C i_t i_s A_t A_s }])%I.
  Proof.
    iIntros "CI".
    cbn; destruct fn.
    Simp. Cut.
    iApply sim_expr_bupd_mono;
      [ | iApply (denote_exp_map_monad args _ with "CI") ]; auto.
    iIntros (??) "H".
    iDestruct "H" as (??->->) "(CI & #H)";
    Simp.

    (* 1. expression refl *)
    Cut. Simp.
    iApply sim_expr_bupd_mono; [ | by iApply expr_logrel_refl].
    iIntros (??) "Hp"; iDestruct "Hp" as (??->->) "(#Hv & CI)".
    Simp.

    (* 2. Call simulation *)
    Cut.

    iApply (sim_expr_bupd_mono with "[CI]");
      last (iApply (instr_conv_concretize_or_pick_strong with "Hv")).

    iIntros (??) "H'".
    iDestruct "H'" as (??->->) "(Hdv & %Hdu_t & %Hdu_s)".
    Simp. Cut. Simp.

    iApply sim_expr_bupd_mono ; [ | iApply (call_refl with "CI Hdv H")].
    cbn. clear e_t e_s.
    iIntros (??) "Hp".
    iDestruct "Hp" as (??->->) "(#Hv2 & CI)".

    Simp.

    (* 3. Local write simulation *)
    Base; Simp.
    iApply sim_expr_bupd_mono ;
      [ | iApply (local_write_refl with "CI Hv2")].

    iIntros (??) "Hp".
    iDestruct "Hp" as (??->->) "CI".
    Simp. Base.
    iExists _, _; by iFrame.
  Qed.

  Lemma instr_call_void_refl C fn args attrs n i_t i_s A_t A_s:
    ⊢ (code_inv C i_t i_s A_t A_s -∗
      instr_conv
       (denote_instr (IVoid n, INSTR_Call fn args attrs)) ⪯
       instr_conv
       (denote_instr (IVoid n, INSTR_Call fn args attrs))
       [{ (r_t, r_s), code_inv C i_t i_s A_t A_s }])%I.
  Proof.
    iIntros "CI".
    cbn; destruct fn.
    Simp; Cut.
    iApply sim_expr_bupd_mono;
      [ | iApply (denote_exp_map_monad args _ with "CI") ]; auto.
    cbn. iIntros (??) "H".
    iDestruct "H" as (??->->) "(CI & #H)"; Simp.
    (* 1. expression refl *)
    Cut; Simp.
    iApply sim_expr_bupd_mono; [ | by iApply expr_logrel_refl].
    cbn. iIntros (??) "Hp".
    iDestruct "Hp" as (??->->) "(#Hv & CI)".
    Simp.

    (* 2. Call simulation *)
    Cut.
    iApply (sim_expr_bupd_mono with "[CI]");
      last (iApply (instr_conv_concretize_or_pick_strong with "Hv")).

    iIntros (??) "H'".
    iDestruct "H'" as (??->->) "(Hdv & %Hdu_t & %Hdu_s)".
    Simp; Cut; Simp.

    iApply sim_expr_bupd_mono ; [ | iApply (call_refl with "CI Hdv H")].
    cbn. clear e_t e_s.
    iIntros (??) "Hp".
    iDestruct "Hp" as (??->->) "(#Hv2 & CI)".
    Simp. Base. Simp. Base.

    iExists _, _; by iFrame.
  Qed.

  Lemma instr_alloca_refl C id t nb align i_t i_s A_t A_s :
    instr_WF (INSTR_Alloca t nb align) ->
    code_inv C i_t i_s A_t A_s -∗
    instr_conv (denote_instr (IId id, INSTR_Alloca t nb align))
    ⪯
    instr_conv (denote_instr (IId id, INSTR_Alloca t nb align))
    [{ (r_t, r_s),
        ∃ l_t l_s, code_inv C i_t i_s (l_t:: A_t) (l_s:: A_s)}].
  Proof.
    iIntros (WF) "CI". cbn.
    Simp; Cut; Simp. cbn in *.
    iApply (sim_expr_bupd_mono with "[] [CI]"); [ |
      iApply (alloca_refl_bij with "CI")]; cycle 1.
    { cbn; intros; apply non_void_b_non_void;
        destruct (non_void_b t); auto. }

    iIntros (??) "H".

    iDestruct "H" as (??->->??) "(#Hv & CI)".
    Simp. Base. Simp.
    iDestruct (dval_rel_lift with "Hv") as "Hdv".

    iApply sim_expr_bupd_mono ;
      [ | iApply (local_write_refl with "CI Hdv")].

    iIntros (??) "Hp".
    iDestruct "Hp" as (??->->) "CI".
    Base.
    iExists _, _; do 2 (iSplitL ""; first done).
    iExists _, _; by iFrame.
  Qed.

  Lemma instr_load_refl id volatile t ptr align i_t i_s A_t A_s:
    instr_WF (INSTR_Load volatile t ptr align) ->
    code_inv ∅ i_t i_s A_t A_s -∗
    instr_conv (denote_instr (IId id, INSTR_Load volatile t ptr align))
    ⪯
    instr_conv (denote_instr (IId id, INSTR_Load volatile t ptr align))
    [{ (r_t, r_s), code_inv ∅ i_t i_s A_t A_s }].
  Proof.
    iIntros (WF) "CI".
    destruct ptr; rewrite /instr_conv; rewrite !interp_bind.

    (* Process the value *)
    iApply sim_expr_bind; iApply sim_expr_mono; cycle 1.
    { iApply exp_conv_to_instr.
      iPoseProof (expr_logrel_refl (Some d) with "CI") as "He".
      iApply "He". }

    iIntros (??) "H".
    iDestruct "H" as (????) "(Hv & CI)".
    rewrite H H0 !bind_ret_l !interp_bind; clear H H0.
    iApply sim_expr_bind.
    iApply (sim_expr_bupd_mono with "[CI] [Hv]") ;
      [ | by iApply instr_conv_concretize_or_pick_strong ].

    iIntros (??) "H"; iDestruct "H" as (????) "(#Hv' & %Hc & %Hc')";
      rewrite H H0; clear H H0; rewrite !bind_ret_l.
    destruct (@dvalue_eq_dec dv_s DVALUE_Poison);
      [ iApply instr_conv_raiseUB | ].

    iDestruct (dval_rel_poison_neg_inv with "Hv'") as "%Hv".
    specialize (Hv n).
    destruct (@dvalue_eq_dec dv_t DVALUE_Poison) eqn: Hb; [ done | ].
    do 2 rewrite interp_bind.
    iApply sim_expr_bind.

    (* Process the ptr *)
    rewrite !interp_vis; cbn -[instr_WF].
    simp_instr.
    setoid_rewrite interp_ret; rewrite !bind_trigger.
    iApply sim_expr_vis.
    iApply (sim_expr_bupd_mono with "[] [CI Hv']"); cycle 1.
    { iApply load_must_be_addr; [ done | ].
      iIntros (????). rewrite H in Hc'; rewrite H0 in Hc.
      cbn in WF. apply andb_prop_elim in WF; destruct WF.
      destruct (dtyp_WF_b t) eqn: Ht; try done.
      apply dtyp_WF_b_dtyp_WF in Ht.
      iApply (load_refl with "CI Hv'"); eauto. }

    cbn -[instr_WF].
    iIntros (??) "H".
    iDestruct "H" as (????) "(#Hv'' & CI)".
    rewrite H H0; rewrite !bind_ret_l ; clear H H0.
    iApply sim_expr_tau.
    iApply sim_expr_base.

    rewrite !bind_ret_l.

    rewrite !interp_vis; cbn -[instr_WF].
    simp_instr. cbn -[instr_WF].

    rewrite !bind_trigger.
    iApply sim_expr_vis.

    iApply (sim_expr_bupd_mono with "[] [CI]");
      [ | iApply (local_write_refl with "CI")]; eauto; cycle 1.
    iIntros (??) "H".
    iDestruct "H" as (????) "CI".
    rewrite H H0; setoid_rewrite bind_ret_l.
    rewrite !interp_ret.
    iApply sim_expr_tau.
    iApply sim_expr_base.
    iExists _, _; do 2 (iSplitL ""; first done); by iFrame.
  Qed.

  Lemma dval_rel_dvalue_has_dtyp dv_t dv_s τ:
    dval_rel dv_t dv_s -∗
    ⌜dvalue_has_dtyp dv_s τ⌝ -∗
    ⌜dvalue_has_dtyp dv_t τ⌝.
  Proof.
    iIntros "H %Hv_s".
    pose (F :=
      (fun dv_t dv_s =>
         ∀ τ,
          ⌜dvalue_has_dtyp dv_s τ⌝ -∗ ⌜dvalue_has_dtyp dv_t τ⌝ : iPropI Σ)%I).
    assert (NonExpansive (F : dvalue -d> dvalue -d> iPropI Σ)).
    { solve_proper_prepare; by repeat f_equiv. }
    iApply (dval_rel_strong_ind F with "[] [H]"); auto.
    iModIntro.
    iIntros (v_t v_s) "H".
    rewrite /F.
    iIntros (??).
    destruct v_t, v_s; try done; cbn.
    all: try solve [inversion H0; iPureIntro; constructor].
    { rewrite /val_rel.Forall2.
      inversion H0; subst; clear H0.
      iInduction fields as [] "IH" forall (fields0 dts H2).
      - iDestruct (big_sepL2_nil_inv_l with "H") as %Hnil; subst.
        inversion H2; subst.
        iPureIntro; constructor; auto.
      - iDestruct (big_sepL2_cons_inv_l with "H") as (???) "((H1 & _) & Hl)";
          subst.
        destruct dts; try solve [inversion H2].
        apply Forall2_cons in H2; destruct H2.
        iDestruct ("H1" $! _ H0) as %Ha.
        iDestruct ("IH" $! _ _ H1 with "Hl") as %Hl.
        iPureIntro; constructor; constructor; auto.
        inversion Hl; auto. }
    { rewrite /val_rel.Forall2.
      inversion H0; subst; clear H0.
      iInduction elts as [] "IH" forall (elts0 H2).
      - iDestruct (big_sepL2_nil_inv_l with "H") as %Hnil; subst.
        inversion H2; subst.
        iPureIntro; constructor; auto.
      - iDestruct (big_sepL2_cons_inv_l with "H") as (???) "((H1 & _) & Hl)";
          subst.
        apply Forall_cons in H2; destruct H2.
        iDestruct ("H1" $! _ H0) as %Ha.
        iDestruct ("IH" $! _ H1 with "Hl") as %Hl.
        iPureIntro; constructor; auto.
        { inversion Hl; auto. }
        cbn. f_equiv; auto. inversion Hl; subst; eauto. lia. }
  Qed.

  Lemma instr_store_refl n volatile val ptr align i_t i_s A_t A_s:
    instr_WF (INSTR_Store volatile val ptr align) ->
    code_inv ∅ i_t i_s A_t A_s -∗
    instr_conv (denote_instr (IVoid n, INSTR_Store volatile val ptr align))
    ⪯
    instr_conv (denote_instr (IVoid n, INSTR_Store volatile val ptr align))
    [{ (r_t, r_s), code_inv ∅ i_t i_s A_t A_s }].
  Proof.
    iIntros (WF) "CI".
    cbn in WF. destruct ptr, d, val; try solve [inversion WF].
    rewrite /instr_conv; rewrite !interp_bind.

    iApply sim_expr_bind; iApply sim_expr_mono; cycle 1.
    { iPoseProof (expr_logrel_refl (Some d) e0 with "CI") as "He"; eauto.
      iApply exp_conv_to_instr.
      iApply "He". }

    iIntros (??) "H".
    iDestruct "H" as (????) "(H & HL)".
    rewrite H H0 !bind_ret_l !interp_bind; clear H H0.

    iApply sim_expr_bind.
    iApply (sim_expr_bupd_mono with "[HL] [H]") ;
      [ | by iApply instr_conv_concretize_or_pick_strong ].

    cbn; iIntros (??) "H".
    iDestruct "H" as (????) "(#Hv' & %Hc & %Hc')";
      rewrite H H0; clear H H0; rewrite !bind_ret_l.
    destruct (dvalue_has_dtyp_fun dv_s d) eqn :Hτ; cycle 1.
    { rewrite interp_bind interp_vis bind_bind.
      rewrite -bind_ret_l. iApply sim_expr_bind.
      iApply sim_expr_exception. }

    apply dvalue_has_dtyp_fun_sound in Hτ.
    iDestruct (dval_rel_dvalue_has_dtyp with "Hv'") as %Hτ'.
    specialize (Hτ' Hτ). rewrite -dvalue_has_dtyp_eq in Hτ'.
    rewrite Hτ'; cbn.

    rewrite !interp_bind.
    iApply sim_expr_bind; iApply sim_expr_mono; cycle 1.
    { iPoseProof (expr_logrel_refl (Some DTYPE_Pointer) e with "HL") as "He"; eauto.
      iApply exp_conv_to_instr.
      iApply "He". }

    iIntros (??) "H".
    iDestruct "H" as (????) "(H & HL)".
    rewrite H H0 !bind_ret_l !interp_bind; clear H H0.
    iApply sim_expr_bind.
    iApply (sim_expr_bupd_mono with "[HL] [H]") ;
      [ | by iApply instr_conv_concretize_or_pick_strong ].

    cbn; iIntros (??) "H"; iDestruct "H" as (????) "(#Hv''' & %Hc'' & %Hc''')";
      rewrite H H0; clear H H0; rewrite !bind_ret_l.

    destruct (@dvalue_eq_dec dv_s0 DVALUE_Poison);
      [ iApply instr_conv_raiseUB | ].
    iDestruct (dval_rel_poison_neg_inv with "Hv'''") as "%Hv".
    specialize (Hv n0).
    destruct (@dvalue_eq_dec dv_t0 DVALUE_Poison) eqn: Hb; [ done | ].
    setoid_rewrite interp_vis; cbn.
    simp_instr. rewrite !bind_trigger.
    iApply sim_expr_vis.

    iApply (sim_expr_bupd_mono with "[] [HL]"); cycle 1.
    { iApply store_must_be_addr; [ done | ].
      iIntros (????). rewrite H in Hc'''; rewrite H0 in Hc''.
      cbn in WF; apply andb_prop_elim in WF.
      destruct WF.

      iApply (store_refl with "HL"); eauto.
      { rewrite -dtyp_WF_b_dtyp_WF. destruct (dtyp_WF_b d); auto. }
      rewrite dvalue_has_dtyp_eq in Hτ'; auto. }

    cbn. iIntros (??) "H".
    iDestruct "H" as (????) "CI".
    rewrite H H0; setoid_rewrite bind_ret_l.
    do 2 rewrite interp_ret.
    iApply sim_expr_tau.
    iApply sim_expr_base. iExists _, _; by iFrame.
  Qed.


(** *Reflexivity theorems for logical relations *)
Section fundamental.

  Context {Σ : gFunctors} `{!vellirisGS Σ}.

  Ltac step_expr :=
    iApply sim_expr_mono;
    [ | by iApply expr_logrel_refl];
    iIntros (??) "Hexp";
    iDestruct "Hexp" as (??->->) "[Hu HC]"; do 2 rewrite bind_ret_l.

  (* Compatibility lemma *)
  (* LATER: See if the [id] generalization is also possible *)
  Theorem phi_compat bid bid' id ϕ ϕ' C A_t A_s:
    (let '(Phi dt  args )  := ϕ in
     let '(Phi dt' args')  := ϕ' in
     match Util.assoc bid args, Util.assoc bid' args' with
     | Some op, Some op' =>
         expr_logrel C
           (denote_exp (Some dt) op)
           (denote_exp (Some dt') op')
           A_t A_s
     | None, None => True
     | _ , _ => False
     end) -∗
    phi_logrel
       (denote_phi bid (id, ϕ))
       (denote_phi bid' (id, ϕ')) C A_t A_s.
  Proof.
    iIntros "He" (????) "H".
    iDestruct "H" as (Harg Hnd_t Hnd_s)
      "(Hdt&Hds&Hat&Has&Hv&Hs_t&Hs_s&#HWF&HC&Ha_t&Ha_s & #Hl)";
      destruct ϕ, ϕ'; cbn.
    rename t0 into t', args0 into args'.

    destruct (Util.assoc bid' args') eqn: H; [ | iApply exp_conv_raise].
    destruct (Util.assoc bid args) eqn: H'; last done.

    Simp.

    iAssert (code_inv C i_t i_s A_t A_s) with
      "[Hdt Hds Hv HC Hat Has Hs_t Hs_s Ha_t Ha_s]" as "HI".
    { rewrite /code_inv; repeat iExists _; iFrame.
      iFrame "HWF".
      by iFrame "Hl". }
    iApply sim_expr_mono; [ | iApply "He"]; [ | done].
    iIntros (??) "H".
    iDestruct "H" as (????) "(Hv & CI)".
    rewrite H0 H1.

    Simp.
    iApply sim_update_si.
    rewrite /update_si.

    iIntros (??) "SI".
    iDestruct "CI" as (??)
      "(Hd_t & Hd_s & Hs_t & Hs_s & HA & %Hc & Ha_t & Ha_s)".

    iFrame. iModIntro. Base.

    iExists _,_,_. do 2 (iSplitL ""; [ try done | ]); iFrame; eauto.
    repeat iExists _; by iFrame.
  Qed.

  Theorem phi_logrel_refl bid id ϕ C A_t A_s:
    ⊢ (phi_logrel (denote_phi bid (id, ϕ)) (denote_phi bid (id, ϕ)) C A_t A_s)%I.
  Proof.
    iApply phi_compat; destruct ϕ.
    destruct (Util.assoc bid args); try done.
    iApply expr_logrel_refl.
  Qed.

  Lemma phi_list_compat bid (Φ Φ' : list (local_id * phi dtyp)) C i_t i_s A_t A_s:
    ([∗ list] ϕ;ϕ' ∈ Φ; Φ',
        phi_logrel (denote_phi bid ϕ) (denote_phi bid ϕ') C A_t A_s) -∗
    code_inv C i_t i_s A_t A_s -∗
    instr_conv (map_monad (λ x, translate exp_to_instr ⟦ x ⟧Φ (bid)) Φ) ⪯
      instr_conv (map_monad (λ x, translate exp_to_instr ⟦ x ⟧Φ (bid)) Φ')
    [{ (r_t, r_s),
        ([∗ list] v_t; v_s ∈ r_t; r_s,
           ⌜v_t.1 = v_s.1⌝ ∗ uval_rel v_t.2 v_s.2)
            ∗ code_inv C i_t i_s A_t A_s }].
  Proof.
    iIntros "HΦ CI".
    rewrite /instr_conv; cbn.

    iInduction Φ as [] "IH" forall (Φ').
    { cbn.
      iPoseProof (big_sepL2_nil_inv_l with "HΦ") as "%Heq"; subst.
      rewrite interp_ret; cbn.
      iApply sim_expr_base; iExists _, _; iFrame; repeat (iSplitL ""; try done). }

    destruct a as (?&[]).
    iPoseProof (big_sepL2_cons_inv_l with "HΦ") as (???) "(He & HΦ)"; subst.
    destruct x2 as (l' & []).
    rename t0 into t', args0 into args', l2' into Φ'.
    iSpecialize ("IH" with "HΦ").
    cbn -[denote_phi].
    Simp.

    iDestruct "CI" as (??)
        "(Hd_t & Hd_s & Hat & Has & #HWF &
        %Hargs & Hs_t & Hs_s & Hv & HC & Ha_t & Ha_s & %Hnd_t & %Hnd_s & #Hl)".

    iApply (sim_expr_bupd_mono with "[IH]"); [ | iApply "He"];
      try iFrame; eauto; cycle 1.

    cbn. iIntros (??) "H".
    iDestruct "H" as (?????) "(H & CI)".
    rewrite H H0. Simp.

    iSpecialize ("IH" with "CI"). subst.
    iApply (sim_expr_bupd_mono with "[H]"); [ | iApply "IH"].
    cbn. iIntros (??) "H'".
    iDestruct "H'" as (????) "(H' & CI)". rewrite H H0.
    Simp. Base.
    iExists ((l0,v_t) :: r_t), ((l0, v_s) :: r_s); iFrame.
    iSplitL ""; done.
  Qed.

  Theorem phis_compat C bid (Φ Φ' : list (local_id * phi dtyp)) A_t A_s:
    ([∗ list] ϕ;ϕ' ∈ Φ; Φ',
        phi_logrel (denote_phi bid ϕ) (denote_phi bid ϕ') C A_t A_s) -∗
    phis_logrel (denote_phis bid Φ) (denote_phis bid Φ') C A_t A_s.
  Proof.
    iIntros "HΦ" (??) "CI".
    iPoseProof (phi_list_compat with "HΦ CI") as "H".
    rewrite /denote_phis.
    Simp. Cut.
    iApply sim_expr_bupd_mono ; [ | iApply "H"]; eauto; try iFrame.

    iIntros (??) "H".
    iDestruct "H" as (??->->) "(H & CI)".
    Simp. setoid_rewrite instr_conv_ret.

    iInduction r_s as [] "IH" forall (r_t).
    { iDestruct (big_sepL2_nil_inv_r with "H") as %Hx; subst; cbn.
      Simp. Base.
      iExists _, _; iFrame; iSplitL ""; done. }

    iDestruct (big_sepL2_cons_inv_r with "H") as (???) "(CI1 & CI2)";
    destruct a, x1; subst; cbn.
    Simp; Cut. Simp.

    iDestruct "CI1" as "(%Hl & Hv)"; subst.

    iApply (sim_expr_bupd_mono with "[CI2]");
      [ | iApply (local_write_refl with "CI Hv")].

    cbn. iIntros (??) "H".
    iDestruct "H" as (??->->) "CI".
    Base.
    iSpecialize ("IH" with "CI2 CI"). Simp.
    iPoseProof (sim_expr_fmap_inv with "IH") as "Hf".
    Cut.

    iApply sim_expr_bupd_mono; [ | iApply "Hf"].

    iIntros (??) "H".
    iDestruct "H" as (????????) "H".
    rewrite H H0; apply eqitree_inv_Ret in H1, H2; subst.
    Simp. Base.
    iExists _, _; iFrame.
    iSplitL ""; done.
  Qed.

  Theorem phis_logrel_refl C bid (Φ : list (local_id * phi dtyp)) A_t A_s:
    (⊢ phis_logrel (denote_phis bid Φ) (denote_phis bid Φ) C A_t A_s)%I.
  Proof.
    iApply phis_compat.
    iInduction Φ as [ | ] "IH"; first done.
    cbn; iSplitL; [ destruct a; iApply phi_logrel_refl | done ].
  Qed.

  Theorem instr_logrel_refl id e A_t A_s:
    instr_WF e ->
    (⊢ instr_logrel id e id e ∅ A_t A_s)%I.
  Proof.
    iIntros (WF ??) "HI".
    destruct e eqn: He.
    all : destruct id; try iApply instr_conv_raise.
    { (* Comment *)
      rewrite /instr_conv interp_ret.
      iApply sim_expr_base.
      iExists _, _;
        do 2 (iSplitL ""; first done).
      iExists ∅, ∅. by cbn. }

    { (* Pure operations *)
      setoid_rewrite interp_bind.
      iApply sim_expr_bind.
      iApply exp_conv_to_instr.
      iApply (sim_expr_bupd_mono with "[] [HI]");
        [ | iApply expr_logrel_refl ]; eauto.
      cbn; iIntros (??) "H".
      iDestruct "H" as (????) "(Hv & Hc)".
      rewrite H H0 !bind_ret_l.
      do 2 rewrite interp_vis. simp_instr.
      rewrite !bind_vis.
      iApply sim_expr_vis.

      iApply (sim_expr_bupd_mono with "[] [Hc Hv]");
        [ | by iApply (local_write_refl with "Hc")].
      iIntros (??) "H".
      iDestruct "H" as (????) "HC".
      rewrite H1 H2.
      iModIntro.
      rewrite !bind_ret_l !interp_ret.
      iApply sim_expr_tau.
      iApply sim_expr_base.
      iExists _, _;
        do 2 (iSplitL ""; first done).

      by iExists ∅, ∅. }

    { iApply (sim_expr_bupd_mono with "[] [HI]");
        last iApply (instr_call_refl with "HI").
      cbn. iIntros (??) "H".
      iDestruct "H" as (????) "H".
      iExists _, _;
        do 2 (iSplitL ""; first done).

      by iExists ∅, ∅. }

   { iApply (sim_expr_bupd_mono with "[] [HI]");
        last iApply (instr_call_void_refl with "HI").
      cbn. iIntros (??) "H".
      iDestruct "H" as (????) "H".
      iExists _, _;
        do 2 (iSplitL ""; first done).
      by iExists ∅, ∅. }

    { iApply (sim_expr_bupd_mono with "[] [HI]");
        last
          iApply (instr_alloca_refl with "HI"); auto.
      cbn. iIntros (??) "H".
      iDestruct "H" as (??????) "H".
      iExists _, _;
        do 2 (iSplitL ""; first done).

      iExists [l_t], [l_s]; by cbn. }

    { iApply (sim_expr_bupd_mono with "[] [HI]");
        last iApply (instr_load_refl with "HI"); auto.
      cbn. iIntros (??) "H".
      iDestruct "H" as (????) "H".
      iExists _, _;
        do 2 (iSplitL ""; first done).
      by iExists ∅, ∅. }

    { iApply (sim_expr_bupd_mono with "[] [HI]");
        last iApply (instr_store_refl with "HI"); auto.
      cbn. iIntros (??) "H".
      iDestruct "H" as (????) "H".
      iExists _, _;
        do 2 (iSplitL ""; first done).
      by iExists ∅, ∅. }
  Qed.

  Theorem code_logrel_refl (c : code dtyp) A_t A_s:
    code_WF c ->
    ⊢ code_logrel c c ∅ A_t A_s.
  Proof.
    iIntros (Hwf ??) "HI"; cbn.
    rewrite /instr_conv. rewrite interp_bind.
    setoid_rewrite interp_ret.

    iInduction c as [| a l] "IHl" forall (i_t i_s A_t A_s);
                                    cbn; rewrite /instr_conv.
    { rewrite interp_ret bind_ret_l.
      iApply sim_expr_base; eauto.

      iExists _, _;
        do 2 (iSplitL ""; first done).
      iExists ∅, ∅; iFrame. }
    cbn in Hwf. apply andb_prop_elim in Hwf;
      destruct Hwf as (HW1 & HW2).

    repeat setoid_rewrite interp_bind.
    rewrite bind_bind.
    destruct a.
    iApply sim_expr_bind.
    iApply sim_expr_bupd_mono;
        [ | iApply instr_logrel_refl];
        cycle 1; eauto.

    iIntros (??) "CI".
    iDestruct "CI" as (????) "CI".
    rewrite H H0 !bind_ret_l. setoid_rewrite interp_ret. clear H H0.
    iApply sim_expr_bind.

    iDestruct "CI" as (??) "CI".
    iSpecialize ("IHl" $! HW2 with "CI").
    iPoseProof (sim_expr_fmap_inv with "IHl") as "H".
    iApply sim_expr_bind.

    iApply sim_expr_bupd_mono; [ | iApply "H"]; try done.

    iIntros (??) "H".
    iDestruct "H" as (????????) "H".
    rewrite H H0. rewrite !bind_ret_l.
    iApply sim_expr_base. rewrite !bind_ret_l.
    iApply sim_expr_base. iFrame.
    iDestruct "H" as (??) "H".

    iExists _, _;
      do 2 (iSplitL ""; first done).
    iExists (nA_t0 ++ nA_t), (nA_s0 ++ nA_s).
    rewrite !app_assoc. done.
  Qed.

  Theorem term_logrel_refl ϒ C:
    (⊢ term_logrel ϒ ϒ C)%I.
  Proof.
    iIntros (??????) "HI".
    destruct ϒ eqn: Hϒ; try solve [iDestruct "WF" as "[]"]; cbn.
    5-8: iApply exp_conv_raise.
    5 : iApply exp_conv_raiseUB.
    { (* TERM_Ret *)
      destruct v.
      setoid_rewrite interp_bind; setoid_rewrite interp_ret.
      iApply sim_expr_bind. step_expr. iApply sim_expr_base; iFrame.
      iExists _, _; iSplitL ""; auto. }
    { (* TERM_Ret_void *)
      rewrite /exp_conv. rewrite interp_ret.
      iApply sim_expr_base.
      iExists _,_. do 2 (iSplitL ""; [ done |]). iFrame.
      iApply uval_rel_none. }
    { (* TERM_Br *)
      destruct v; step.
      step_expr. step.
      iApply (sim_expr_bupd_mono with "[HC]");
        [ | iApply (exp_conv_concretize_or_pick with "Hu") ].
      cbn.
      iIntros (??) "Hexp".
      iDestruct "Hexp" as (??->->) "Hv"; do 2 rewrite bind_ret_l.
      destruct dv_s; try iApply exp_conv_raise; [ | iApply exp_conv_raiseUB ].
      iDestruct (dval_rel_I1_inv with "Hv") as %->.
      destruct (DynamicValues.Int1.eq x DynamicValues.Int1.one).
      { rewrite interp_ret; iApply sim_expr_base.
        iModIntro. iExists _,_. do 2 (iSplitL ""; [ done | ]); by iFrame. }
      { rewrite interp_ret; iApply sim_expr_base.
        iModIntro. iExists _,_. do 2 (iSplitL ""; [ done | ]); by iFrame. } }
    { (* TERM_Br_1 *)
      rewrite /exp_conv interp_ret.
      iApply sim_expr_base.
      iExists _,_. do 2 (iSplitL ""; [ done | ]); by iFrame. }
  Qed.

  Theorem block_logrel_refl b A_t A_s:
    block_WF b ->
    (⊢ block_logrel b b ∅ A_t A_s)%I.
  Proof.
    iIntros (WF ???) "HI".
    rewrite /denote_block /instr_conv interp_bind.
    iApply sim_expr_bind; iApply sim_expr_mono;
      [ | by iApply phis_logrel_refl].
    iIntros (??) "H".
    iDestruct "H" as (????) "HI".
    rewrite H H0; do 2 rewrite bind_ret_l; clear H H0.
    rewrite interp_bind.
    unfold block_WF in WF.
    apply andb_prop_elim in WF. destruct WF.
    iApply sim_expr_bind; iApply sim_expr_mono;
      [ | iApply code_logrel_refl ]; eauto.

    iIntros (??) "H".
    iDestruct "H" as (??????) "Hi".
    rewrite H1 H2; do 2 rewrite bind_ret_l; clear H1 H2.
    iApply sim_expr_mono; cycle 1.
    { rewrite interp_translate.
      rewrite (eq_itree_interp _ _ eq2_exp_to_L0); last done.
      iApply term_logrel_refl; auto. }
    iIntros (??) "H".
    iDestruct "H" as (????) "(HI & H)".
    iExists _,_. rewrite H1 H2.
    do 2 (iSplitL ""; [ done | ]). iFrame.
    by iExists _, _.
  Qed.

  Theorem ocfg_logrel_refl (c : CFG.ocfg dtyp) b1 b2 A_t A_s:
    ocfg_WF c ->
    (⊢ ocfg_logrel c c ∅ A_t A_s b1 b2)%I.
  Proof.
    iIntros (WF ??) "CI".
    rewrite /ocfg_WF in WF.
    rewrite /denote_ocfg.
    unfold CategoryOps.iter, CategoryKleisli.Iter_Kleisli,
      Basics.iter, MonadIter_itree.

    epose proof
      (@interp_iter' _ _ instrE_conv _ _
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
      (λ i, interp instrE_conv
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
    rewrite /instr_conv. rewrite H.

    iApply sim_expr'_tau_inv.
    { iModIntro. iIntros (??). iSplitL.
      - iIntros "(Hb & H & H')"; iFrame.
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
       ∗ code_inv_post ∅ i_t i_s A_t A_s)%I
             with "[] [CI]"); cycle 1.
    { iSplitL ""; first done.
      by iExists ∅, ∅. }
    iModIntro.
    iIntros (??) "(%Heq & CI)"; rewrite Heq. destruct i_s0; clear Heq.
    iDestruct "CI" as (??) "CI".
    iApply sim_expr_lift.

    destruct (CFG.find_block c b0) eqn: Hb0.
    { rewrite interp_bind. iApply sim_expr_bind.
      iApply sim_expr_bupd_mono; [ | iApply block_logrel_refl]; eauto; cycle 1.
      { unfold CFG.find_block in Hb0.
        apply find_some in Hb0. destruct Hb0.
        destruct (forallb block_WF c) eqn: HWF; try done.
        rewrite forallb_forall in HWF.
        specialize (HWF _ H0). destruct (block_WF b3); try done. }

      iIntros (??) "H".
      iDestruct "H" as (????) "(H & l)".
      iDestruct "H" as (??) "H".
      rewrite H0 H1; do 2 rewrite bind_ret_l.
      destruct r_t, r_s; try (iDestruct "l" as %Heq; inversion Heq).
      - rewrite !interp_ret.
        iApply sim_expr_base; iLeft. iModIntro; subst.
        iExists (b0, b5), (b0, b5); iFrame; eauto.
        do 3 (iSplitL ""; first done).
        rewrite !app_assoc.
        by iExists (nA_t0 ++ nA_t), (nA_s0 ++ nA_s).
      - do 2 rewrite interp_ret.
        iApply sim_expr_base; iRight.
        iDestruct "l" as "#l".
        iModIntro; subst. iFrame.
        repeat iExists _; do 2 (iSplitL ""; eauto).
        iSplitL.
        { iExists (nA_t0 ++ nA_t), (nA_s0 ++ nA_s).
          by rewrite !app_assoc. }

        repeat iExists _; do 2 (iSplitL ""; eauto); done. }

    rewrite interp_ret.
    iApply sim_expr_base; iRight. iFrame.
    do 2 iExists _; do 2 (iSplitL ""; eauto).
    iSplitL "CI".
    { iExists nA_t, nA_s; by iFrame. }

    repeat iExists _; do 2 (iSplitL ""; eauto); done.
  Qed.

  Theorem cfg_logrel_refl c A_t A_s:
    cfg_WF c ->
    (⊢ cfg_logrel c c ∅ A_t A_s)%I.
  Proof.
    iIntros (WF ??) "CI";
    setoid_rewrite interp_bind. destruct c; cbn.
    iApply sim_expr'_bind; iApply (sim_expr'_bupd_mono); cycle 1.
    { cbn; iApply ocfg_logrel_refl; auto. }
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

  Theorem fun_logrel_refl f:
    fun_WF f ->
    (⊢ fun_logrel f f ∅)%I.
  Proof.
    iIntros (WF i_t i_s args_t args_s Hlen) "Hs_t Hs_s Hv HC".

    rewrite /denote_function; cbn -[denote_cfg].
    destruct (length (df_args f) =? length args_s) eqn : Hlen_args; cycle 1.
    { rewrite bind_bind bind_vis.

      setoid_rewrite interp_bind.
      setoid_rewrite interp_vis; rewrite bind_trigger.
      iApply sim_expr_lift.
      iApply sim_expr_exception_vis. }

    rewrite /val_rel.Forall2.
    iDestruct (big_sepL2_length  with "Hv") as %Hargs.
    assert (Hlen_f: length (df_args f) =? length args_t = true).
    { apply PeanoNat.Nat.eqb_eq; subst.
      apply PeanoNat.Nat.eqb_eq in Hlen_args; rewrite Hlen_args; done. }
    rewrite Hlen_f.

    rewrite /L0'expr_conv !interp_bind !interp_ret !bind_ret_l.
    setoid_rewrite interp_bind;
    rewrite !interp_vis !bind_bind; cbn -[denote_cfg].
    setoid_rewrite interp_ret.
    setoid_rewrite interp_bind.
    setoid_rewrite interp_vis.
    setoid_rewrite bind_bind.
    setoid_rewrite interp_ret.
    do 2 rewrite -bind_bind.
    rewrite -(bind_bind (Vis (call_conv () (subevent () MemPush)) (λ x : (), Ret x))).
    rewrite -(bind_bind (r <- (Vis (call_conv () (subevent () MemPush)) (λ x : (), Ret x)) ;; Tau (Ret r))).
    iApply sim_expr'_bind.
    rewrite !bind_bind.

    rewrite /subevent /resum /ReSum_inr /cat /Cat_IFun /inr_ /Inr_sum1.
    simp L0'_conv.

    iCombine "Hs_t Hs_s" as "Hst".
    apply PeanoNat.Nat.eqb_eq in Hlen_args, Hlen_f.
    apply andb_prop_elim in WF. destruct WF.
    assert (Hnd: NoDup_b (df_args f) = true).
    { destruct (NoDup_b (df_args f)); done. }
    apply NoDup_b_NoDup in Hnd. clear H. rename H0 into WF.

    iApply (sim_expr'_bupd_mono with "[Hv HC]");
      [ | iApply sim_expr_lift; iApply (sim_push_frame' with "Hst") ];
      [ | rewrite combine_fst | rewrite combine_fst ]; eauto.

    cbn.
    iIntros (??) "H".
    iDestruct "H" as (??????) "(Hs_t & Hs_s & Ha_t & Ha_s & Hd_t & Hd_s & Harg_t & Harg_s)".
    rewrite H H0; clear H H0.

    rewrite !bind_ret_l !bind_tau.
    iApply sim_expr'_tau; rewrite !bind_ret_l.

    rewrite interp_bind.

    (* Denote CFG *)
    iApply sim_expr'_bind.
    iApply spec.instr_to_L0'.

    iDestruct "Hv" as "#Hv".
    iApply sim_expr'_bupd_mono;
      [ | iApply (cfg_logrel_refl with
          "[HC Hs_t Hs_s Ha_t Ha_s Hd_t Hd_s Harg_t Harg_s]") ];
      eauto; cycle 1.
    { Unshelve.
      4 : exact (j_t :: i_t). 4 : exact (j_s :: i_s).
      2 : exact ∅. 2 : exact ∅.
      iExists (combine (df_args f) args_t),
              (combine (df_args f) args_s); iFrame.
      iSplitL "".
      { iPureIntro; eauto. }

      iSplitL "".
      { rewrite !combine_fst; auto. }
      { rewrite !combine_snd; eauto; iFrame.
        rewrite /val_rel.Forall2; iFrame "Hv".
        cbn.
        by rewrite NoDup_nil. } }

    clear e_t0 e_s0.

    iIntros (e_t e_s) "H".
    iDestruct "H" as (????) "(#Hr & HC)".
    rewrite H H0 !bind_ret_l.
    iDestruct "HC" as (??) "HC".

    iDestruct "HC" as (??) "CI".
    rewrite !app_nil_r.

    iDestruct "CI" as
      "(Hd_t&Hd_s&Hs_t&Hs_s&#HWF&%Heq&Hargs_t&Hargs_s&#Huv&HC&Ha_t&Ha_s&#Hbij)".
    iApply sim_expr_lift.

    iApply sim_update_si; iModIntro.
    iIntros (??) "SI".
    iDestruct (state_interp_WF with "SI") as "%WF_S".
    iFrame.

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
    { iDestruct "Hbij" as (Hnd_t Hnd_s) "Hbij".
      iPoseProof (sim_pop_frame_bij with "Hs_t Hs_s Ha_t Ha_s HC Hbij") as "H";
        eauto.
      { intros. cbn in H1.
        assert (length i_s > 0)%Z by lia.
        specialize (Hlen H2). cbn; lia. } }

    iIntros (??) "H".
    iDestruct "H" as (????) "(HC & Hst & Hss)".
    rewrite H1 H2 !bind_ret_l.
    iApply sim_expr_tau; iApply sim_expr_base.
    iFrame. iExists _, _; iFrame "Hr"; done.
  Qed.

  Theorem fundefs_logrel_refl r Attr:
    ⌜fundefs_WF r Attr⌝ -∗
    fundefs_logrel r r Attr Attr ∅.
  Proof.
    rewrite /fundefs_logrel.
    iInduction r as [ | f l] "H" forall (Attr).
    { iIntros. done. }
    { iIntros (WF).
      iIntros (i f_t' f_s'
        addr_t addr_s attr Hlu_t Hlu_s Hattr_t Hattr_s) "#Hrel".
      iIntros (i_t i_s args_t args_s Hlen) "Hs_t Hs_s #Hargs HC".
      iIntros (τ Hcall).
      pose proof fundefs_WF_cons_inv. destruct Attr.
      { clear -Hattr_t. set_solver. }
      pose proof (fundefs_WF_cons_inv _ _ _ _ WF) as HWF_t.
      destruct HWF_t as (?&?).

      destruct i.
      { cbn in Hlu_t, Hlu_s, Hattr_t, Hattr_s.
        inversion Hlu_t; subst.
        inversion Hlu_s; subst.
        inversion Hattr_t; subst.
        rewrite /fundefs_WF in H0.
        cbn in H0.
        do 2 rewrite andb_true_r in H0.
        iApply (fun_logrel_refl f_s' H0 $!
                  i_t i_s args_t args_s Hlen with "Hs_t Hs_s Hargs HC"). }
      { cbn in Hlu_t, Hlu_s, Hattr_t, Hattr_s.
        iSpecialize ("H" $! Attr H1 i f_t' f_s' _ _ attr Hlu_t Hlu_s Hattr_t Hattr_s with "Hrel").
        iSpecialize ("H" $! i_t i_s args_t args_s Hlen with "Hs_t Hs_s Hargs HC").
        by iApply "H". } }
  Qed.

  Theorem mcfg_definitions_refl (defs : CFG.mcfg dtyp) g_t g_s:
    (CFG_WF defs g_t g_s ->
     ⊢ target_globals g_t -∗
     source_globals g_s -∗
     mcfg_definitions defs ⪯ mcfg_definitions defs
      [[ fun e_t e_s =>
          ∃ r_t r_s,
            ⌜e_t = Ret r_t⌝ ∗ ⌜e_s = Ret r_s⌝ ∗
            ⌜Permutation r_t.*1
              (codomain (filter_keys g_t (CFG_names defs)))⌝ ∗
            ⌜Permutation r_s.*1
              (codomain (filter_keys g_s (CFG_names defs)))⌝ ∗
            ([∗ list] i ↦ v_t; v_s ∈ r_t.*1;r_s.*1, dval_rel v_t v_s) ∗
            ⌜Leaf.Leaf r_t (mcfg_definitions defs)⌝ ∗
            ⌜Leaf.Leaf r_s (mcfg_definitions defs)⌝ ∗
            fundefs_rel_WF r_t r_s
                (CFG_attributes defs) (CFG_attributes defs) ∗
            ⌜fundefs_WF r_t (CFG_attributes defs)⌝ ∗
            ⌜fundefs_WF r_s (CFG_attributes defs)⌝ ∗
            □ (fundefs_logrel r_t r_s (CFG_attributes defs) (CFG_attributes defs) ∅) ]])%I.
  Proof.
    rewrite /mcfg_definitions. iIntros (WF) "#Hg_t #Hg_s". destruct defs.
    cbn in *. rewrite /CFG_WF /CFG_names in WF;
      cbn -[defs_names] in WF. destructb.

    rename H into Hlen, H0 into Hdup, H1 into defs, H2 into Hattr,
      H3 into Hdom_t, H4 into Hdom_s, H5 into NoDup_t, H6 into NoDup_s.

    iApply sim_expr_lift.
    iInduction m_definitions as [ | f l] "H"
        forall (m_declarations Hlen Hdup defs Hattr Hdom_t Hdom_s NoDup_t NoDup_s).
    { cbn. iApply sim_expr_base.
      iExists _, _.
      do 2 (iSplitL ""; [ done | ]).
      rewrite /fundefs_logrel. cbn.
      destruct m_declarations; try done; cbn.
      iSplitL "".
      { by rewrite filter_keys_nil codomain_empty. }
      iSplitL "".
      { by rewrite filter_keys_nil codomain_empty. }
      do 3 (iSplitL ""; [ iPureIntro; by constructor | ]).
      iSplitL "".
      { iSplitL ""; auto. iIntros. inv H. }
      do 2 (iSplitL ""; first done).
      iModIntro. iIntros. inversion H0. }

    { cbn. rewrite /CFG_WF; cbn.
      remember (
        b <- address_one_function f;; bs <- map_monad address_one_function l;; Ret (b :: bs)).
      rewrite { 3 4 } Heqi.
      setoid_rewrite bind_bind. rewrite bind_trigger.
      pose proof (global_names_cons_lookup _ _ _  Hdom_t) as Hlu_t.
      destruct Hlu_t as (?&Hlu_t).
      pose proof (global_names_cons_lookup _ _ _  Hdom_s) as Hlu_s.
      destruct Hlu_s as (?&Hlu_s).

      iApply sim_expr_vis; iApply sim_expr_mono;
        [ | iApply (sim_global_read1 with "Hg_t Hg_s") ]; eauto.

      iIntros (??) "HR". iDestruct "HR" as (????) "(#HR & %Hx1 & %Hx2)"; subst.
      rewrite H H0; repeat rewrite bind_ret_l.
      destruct m_declarations; inv Hlen.
      symmetry in H2.

      cbn in Hdup. nodup.
      apply Forall_cons in defs, Hattr; destructb.
      rewrite /defs_names in Hdup. cbn in Hdup.
      nodup. rename H7 into Hnd.
      rename H3 into Hattr, H1 into Hdc_attr.
      iSpecialize ("H" $! m_declarations eq_refl Hnd).
      assert (Hdom_t' := Hdom_t); assert (Hdom_s' := Hdom_s).
      apply contains_keys_cons_inv in Hdom_t, Hdom_s.
      destruct Hdom_t as (Hd_t & Hdom_t).
      destruct Hdom_s as (Hd_s & Hdom_s).

      iApply sim_expr_bind; iApply (sim_expr_mono with "[HR]");
        [ | iApply "H" ]; eauto; cycle 1.
      (* NoDup [target] *)
      { iPureIntro. eapply nodup_codomain_cons_inv; eauto.
        apply NoDup_cons; eauto. }
      { iPureIntro. eapply nodup_codomain_cons_inv; eauto.
        apply NoDup_cons; eauto. }

      iIntros (??) "HI".
      iDestruct "HI" as (??????) "(#Hv & HI)".
      iDestruct "HI" as (??) "#HI"; subst.
      repeat rewrite bind_ret_l.
      iApply sim_expr_base.
      iExists _, _.
      do 2 (iSplitL ""; [ done | ]); iFrame "Hv".
      iFrame "HR".

      iSplitL ""; [iPureIntro | ].
      { cbn.
        eapply mcfg_defs_keys_extend; eauto. }
      iSplitL ""; [iPureIntro | ].
      { eapply mcfg_defs_keys_extend; eauto. }

      iSplitL ""; [iPureIntro | ].
      { subst. rewrite bind_bind bind_trigger.
        eapply Leaf.Leaf_Vis.
        setoid_rewrite bind_ret_l.
        eapply Leaf.Leaf_bind; [ apply H9 | ].
        by econstructor. }

      iSplitL ""; [iPureIntro | ].
      { subst. rewrite bind_bind bind_trigger.
        eapply Leaf.Leaf_Vis.
        setoid_rewrite bind_ret_l.
        eapply Leaf.Leaf_bind; [ apply H10 | ].
        by econstructor. }

      iSplitL "".
      (* fundefs rel *)
      { iDestruct "HI" as "(HI & _)".
        iClear "H".
        iSplitL "".
        { iIntros (????).
          apply lookup_cons_Some in H1. destruct H1.
          { destruct H1; subst; cbn.
            iExists _, _; base; inv H3; iFrame "HR"; base.
            rewrite Hdc_attr H4; done. }
          { destruct H1. cbn.
            iDestruct "HI" as "(H1 & H2)".
            iSpecialize ("H1" $! (i - 1) _ _ H3).
            iDestruct "H1" as (???) "(#Hdv & H1)".
            iDestruct "H1" as (???) "%H'".
            iExists _, _; cbn; base.
            rewrite lookup_cons_Some.
            iSplitL ""; first (iRight; eauto); iFrame "Hdv".
            rewrite lookup_cons_Some.
            do 2 (iSplitL ""; first (iRight; eauto)). done. } }
        { iDestruct "HI" as "(H1 & %H2')".
          iIntros (??). destruct i; cbn in a; inv a.
          cbn. specialize (H2' _ H3). rewrite H2' H3; done. } }

      iSplitL "".
      { iDestruct "HI" as "(H1 & %Ha & %Ha' & _)". iClear "H".
        cbn. rewrite /fundefs_WF.
        do 2 rewrite andb_True; cbn -[NoDup_b].
        rewrite /fundefs_WF in Ha. resolveb.
        iPureIntro. repeat split; eauto.
        { rewrite H1. by rewrite Nat.eqb_refl. }
        { rewrite andb_True. split; auto.
          apply forallb_True; auto. }
        { apply Is_true_true_2. apply NoDup_b_NoDup.
          eapply NoDup_mcfg_extend; eauto. } }

      iSplitL "".
      { iDestruct "HI" as "(H1 & %Ha & %Ha' & _)". iClear "H".
        cbn. rewrite /fundefs_WF.
        do 2 rewrite andb_True; cbn -[NoDup_b].
        rewrite /fundefs_WF in Ha'. resolveb.
        iPureIntro. repeat split; eauto.
        { rewrite H1. by rewrite Nat.eqb_refl. }
        { rewrite andb_True. split; auto.
          apply forallb_True; auto. }
        { apply Is_true_true_2. apply NoDup_b_NoDup.
          eapply NoDup_mcfg_extend; eauto. } }

      iModIntro. clear Hlu_t Hlu_s.
      iIntros (i f_t' f_s' addr_t
                 addr_s attr Hlu_t Hlu_s Hattr_t Hattr_s) "#Hrel".
      iIntros (i_t i_s args_t args_s Hlen)
        "Hs_t Hs_s #Hargs HC".
      destruct i.
      { cbn in Hlu_t, Hlu_s, Hattr_t, Hattr_s.
        inv Hlu_t; inv Hlu_s.
        apply Is_true_true_2 in H4.

        iApply (fun_logrel_refl f_s' H4 $!
                  i_t i_s args_t args_s Hlen with "Hs_t Hs_s Hargs HC"). }
      { cbn in Hlu_t, Hlu_s, Hattr_t, Hattr_s.
        iDestruct "HI" as "(H1 & %Ha & %Ha' & HI)".
        iSpecialize ("HI" $! i f_t' f_s' _ _ attr Hlu_t Hlu_s Hattr_t Hattr_s with "Hrel").
        iSpecialize ("HI" $! i_t i_s args_t args_s Hlen with "Hs_t Hs_s Hargs HC").
        by iApply "HI". } }
  Qed.

  Theorem mcfg_definitions_refl' (defs : CFG.mcfg dtyp) g_t g_s:
    (CFG_WF defs g_t g_s ->
     ⊢ target_globals g_t -∗
     source_globals g_s -∗
     mcfg_definitions defs ⪯ mcfg_definitions defs
      [[ fun e_t e_s =>
          ∃ r_t r_s g_t' g_s',
            ⌜e_t = Ret r_t⌝ ∗ ⌜e_s = Ret r_s⌝ ∗
            ⌜Permutation r_t.*1
              (codomain (filter_keys g_t (CFG_names defs)))⌝ ∗
            ⌜Permutation r_s.*1
              (codomain (filter_keys g_s (CFG_names defs)))⌝ ∗
            ([∗ list] i ↦ v_t; v_s ∈ r_t.*1;r_s.*1, dval_rel v_t v_s) ∗
            ⌜Leaf.Leaf (g_t', r_t) (interp_global (mcfg_definitions defs) g_t)⌝ ∗
            ⌜Leaf.Leaf (g_s', r_s) (interp_global (mcfg_definitions defs) g_s)⌝ ∗
            fundefs_rel_WF r_t r_s
                (CFG_attributes defs) (CFG_attributes defs) ∗
            ⌜fundefs_WF r_t (CFG_attributes defs)⌝ ∗
            ⌜fundefs_WF r_s (CFG_attributes defs)⌝ ∗
            □ (fundefs_logrel r_t r_s (CFG_attributes defs) (CFG_attributes defs) ∅) ]])%I.
  Proof.
    rewrite /mcfg_definitions. iIntros (WF) "#Hg_t #Hg_s". destruct defs.
    cbn in *. rewrite /CFG_WF /CFG_names in WF;
      cbn -[defs_names] in WF. destructb.

    rename H into Hlen, H0 into Hdup, H1 into defs, H2 into Hattr,
      H3 into Hdom_t, H4 into Hdom_s, H5 into NoDup_t, H6 into NoDup_s.

    iApply sim_expr_lift.
    iInduction m_definitions as [ | f l] "H"
        forall (m_declarations Hlen Hdup defs Hattr Hdom_t Hdom_s NoDup_t NoDup_s).
    { cbn. iApply sim_expr_base.
      iExists _, _, _, _.
      do 2 (iSplitL ""; [ done | ]).
      rewrite /fundefs_logrel. cbn.
      destruct m_declarations; try done; cbn.
      iSplitL "".
      { by rewrite filter_keys_nil codomain_empty. }
      iSplitL "".
      { by rewrite filter_keys_nil codomain_empty. }

      iSplitL ""; first done.
      iSplitL "".
      { iPureIntro. rewrite interp_global_ret; constructor; eauto. }

      iSplitL "".
      { iPureIntro. rewrite interp_global_ret; constructor; eauto. }
      iSplitL "".
      { iSplitL ""; auto. iIntros. inv H. }
      do 2 (iSplitL ""; first done).
      iModIntro. iIntros. inversion H0. }

    { cbn. rewrite /CFG_WF; cbn.
      remember (
        b <- address_one_function f;; bs <- map_monad address_one_function l;; Ret (b :: bs)).
      rewrite { 3 4 } Heqi.
      setoid_rewrite bind_bind. rewrite bind_trigger.
      pose proof (global_names_cons_lookup _ _ _  Hdom_t) as Hlu_t.
      destruct Hlu_t as (?&Hlu_t).
      pose proof (global_names_cons_lookup _ _ _  Hdom_s) as Hlu_s.
      destruct Hlu_s as (?&Hlu_s).

      iApply sim_expr_vis; iApply sim_expr_mono;
        [ | iApply (sim_global_read1 with "Hg_t Hg_s") ]; eauto.

      iIntros (??) "HR". iDestruct "HR" as (????) "(#HR & %Hx1 & %Hx2)"; subst.
      rewrite H H0; repeat rewrite bind_ret_l.
      destruct m_declarations; inv Hlen.
      symmetry in H2.

      cbn in Hdup. nodup.
      apply Forall_cons in defs, Hattr; destructb.
      rewrite /defs_names in Hdup. cbn in Hdup.
      nodup. rename H7 into Hnd.
      rename H3 into Hattr, H1 into Hdc_attr.
      iSpecialize ("H" $! m_declarations eq_refl Hnd).
      assert (Hdom_t' := Hdom_t); assert (Hdom_s' := Hdom_s).
      apply contains_keys_cons_inv in Hdom_t, Hdom_s.
      destruct Hdom_t as (Hd_t & Hdom_t).
      destruct Hdom_s as (Hd_s & Hdom_s).

      iApply sim_expr_bind; iApply (sim_expr_mono with "[HR]");
        [ | iApply "H" ]; eauto; cycle 1.
      (* NoDup [target] *)
      { iPureIntro. eapply nodup_codomain_cons_inv; eauto.
        apply NoDup_cons; eauto. }
      { iPureIntro. eapply nodup_codomain_cons_inv; eauto.
        apply NoDup_cons; eauto. }

      iIntros (??) "HI".
      iDestruct "HI" as (????????) "(#Hv & HI)".
      iDestruct "HI" as (??) "#HI"; subst.
      repeat rewrite bind_ret_l.
      iApply sim_expr_base.
      iExists _, _, _,_.
      do 2 (iSplitL ""; [ done | ]); iFrame "Hv".
      iFrame "HR".

      iSplitL ""; [iPureIntro | ].
      { cbn.
        eapply mcfg_defs_keys_extend; eauto. }
      iSplitL ""; [iPureIntro | ].
      { eapply mcfg_defs_keys_extend; eauto. }

      iSplitL ""; [iPureIntro | ].
      { do 2 setoid_rewrite interp_global_bind.
        rewrite bind_bind.
        rewrite interp_global_trigger. cbn. rewrite Hlu_t.
        rewrite bind_ret_l.
        rewrite interp_global_ret.
        setoid_rewrite bind_ret_l.
        rewrite interp_global_bind.
        eapply Leaf.Leaf_bind; [ apply H9 | ].
        cbn. rewrite interp_global_ret.
        by econstructor. }

      iSplitL ""; [iPureIntro | ].
      { do 2 setoid_rewrite interp_global_bind.
        rewrite bind_bind.
        rewrite interp_global_trigger. cbn. rewrite Hlu_s.
        rewrite bind_ret_l.
        rewrite interp_global_ret.
        setoid_rewrite bind_ret_l.
        rewrite interp_global_bind.
        eapply Leaf.Leaf_bind; [ apply H10 | ].
        cbn. rewrite interp_global_ret.
        by econstructor. }

      iSplitL "".
      (* fundefs rel *)
      { iDestruct "HI" as "(HI & _)".
        iClear "H".
        iSplitL "".
        { iIntros (????).
          apply lookup_cons_Some in H1. destruct H1.
          { destruct H1; subst; cbn.
            iExists _, _; base; inv H3; iFrame "HR"; base.
            rewrite Hdc_attr H4; done. }
          { destruct H1. cbn.
            iDestruct "HI" as "(H1 & H2)".
            iSpecialize ("H1" $! (i - 1) _ _ H3).
            iDestruct "H1" as (???) "(#Hdv & H1)".
            iDestruct "H1" as (???) "%H'".
            iExists _, _; cbn; base.
            rewrite lookup_cons_Some.
            iSplitL ""; first (iRight; eauto); iFrame "Hdv".
            rewrite lookup_cons_Some.
            do 2 (iSplitL ""; first (iRight; eauto)). done. } }
        { iDestruct "HI" as "(H1 & %H2')".
          iIntros (??). destruct i; cbn in a; inv a.
          cbn. specialize (H2' _ H3). rewrite H2' H3; done. } }

      iSplitL "".
      { iDestruct "HI" as "(H1 & %Ha & %Ha' & _)". iClear "H".
        cbn. rewrite /fundefs_WF.
        do 2 rewrite andb_True; cbn -[NoDup_b].
        rewrite /fundefs_WF in Ha. resolveb.
        iPureIntro. repeat split; eauto.
        { rewrite H1. by rewrite Nat.eqb_refl. }
        { rewrite andb_True. split; auto.
          apply forallb_True; auto. }
        { apply Is_true_true_2. apply NoDup_b_NoDup.
          eapply NoDup_mcfg_extend; eauto. } }

      iSplitL "".
      { iDestruct "HI" as "(H1 & %Ha & %Ha' & _)". iClear "H".
        cbn. rewrite /fundefs_WF.
        do 2 rewrite andb_True; cbn -[NoDup_b].
        rewrite /fundefs_WF in Ha'. resolveb.
        iPureIntro. repeat split; eauto.
        { rewrite H1. by rewrite Nat.eqb_refl. }
        { rewrite andb_True. split; auto.
          apply forallb_True; auto. }
        { apply Is_true_true_2. apply NoDup_b_NoDup.
          eapply NoDup_mcfg_extend; eauto. } }

      iModIntro. clear Hlu_t Hlu_s.
      iIntros (i f_t' f_s' addr_t
                 addr_s attr Hlu_t Hlu_s Hattr_t Hattr_s) "#Hrel".
      iIntros (i_t i_s args_t args_s Hlen)
        "Hs_t Hs_s #Hargs HC".
      destruct i.
      { cbn in Hlu_t, Hlu_s, Hattr_t, Hattr_s.
        inv Hlu_t; inv Hlu_s.
        apply Is_true_true_2 in H4.

        iApply (fun_logrel_refl f_s' H4 $!
                  i_t i_s args_t args_s Hlen with "Hs_t Hs_s Hargs HC"). }
      { cbn in Hlu_t, Hlu_s, Hattr_t, Hattr_s.
        iDestruct "HI" as "(H1 & %Ha & %Ha' & HI)".
        iSpecialize ("HI" $! i f_t' f_s' _ _ attr Hlu_t Hlu_s Hattr_t Hattr_s with "Hrel").
        iSpecialize ("HI" $! i_t i_s args_t args_s Hlen with "Hs_t Hs_s Hargs HC").
        by iApply "HI". } }
  Qed.

End fundamental.
