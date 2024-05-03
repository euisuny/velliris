From iris.prelude Require Import options.
From iris.proofmode Require Import proofmode.
From stdpp Require Import gmap.

From Vellvm Require Import
  Syntax.DynamicTypes Handlers Utils.Util.

From velliris Require Import vir.util utils.tactics.

(* Misc. Utilities for vir *)

Lemma non_void_allocate_abs:
  forall τ σ s, non_void τ -> ~ (allocate σ τ = inl s).
Proof.
  intros; destruct τ; eauto.
Qed.

Definition new_lb := make_empty_logical_block.

Lemma CFG_find_block_in {A} c i b :
  CFG.find_block (T:= A) c i = Some b -> b ∈ c.
Proof.
  induction c; cbn; intros; [ inversion H | ].
  destruct (Eqv.eqv_dec_p (LLVMAst.blk_id a) i) eqn : Ha;
    inversion H; subst; clear H;
    [ apply elem_of_cons ; by left |].
  apply elem_of_cons; right; eapply IHc; eauto.
Qed.

Definition lb_mem (b : logical_block) : mem_block :=
  match b with
    | LBlock _ m _ => m
  end.

(* ------------------------------------------------------------------------ *)
(** *Utilities for [dtyp] *)

(* Computable function for [dvalue_has_dtyp] is logically equivalent to
 the propositional definition. *)
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

(* Well-formedness for dynamic types. *)

(* Non-zero size dynamic types (with non-zero size fields for struct types)
  that are supported for memory read/writes *)
Inductive dtyp_WF : dtyp → Prop :=
    dtyp_WF_I1 : dtyp_WF (DTYPE_I 1)
  | dtyp_WF_I8 : dtyp_WF (DTYPE_I 8)
  | dtyp_WF_I32 : dtyp_WF (DTYPE_I 32)
  | dtyp_WF_I64 : dtyp_WF (DTYPE_I 64)
  | dtyp_WF_Pointer : dtyp_WF DTYPE_Pointer
  | dtyp_WF_Float : dtyp_WF DTYPE_Float
  | dtyp_WF_Double : dtyp_WF DTYPE_Double
  | dtyp_WF_Array :
    ∀ (sz : N) (τ : dtyp),
      dtyp_WF τ →
      sz <> 0%N ->
      dtyp_WF (DTYPE_Array sz τ)
  | dtyp_WF_Struct :
    ∀ fields : list dtyp,
      length fields <> 0 ->
      Forall dtyp_WF fields →
      dtyp_WF (DTYPE_Struct fields).

Lemma dtyp_WF_implies_is_supported τ:
  dtyp_WF τ -> is_supported τ.
Proof.
  induction τ; intros.
  1-11: inversion H; constructor; eauto.
  1,3: inversion H; constructor; eauto.
  inversion H0; constructor; eauto; subst.
    rewrite Forall_forall in H3.
    rewrite Forall_forall; intros.
    specialize (H3 _ H1).
    eapply H; eauto.
    by rewrite -elem_of_list_In.
Qed.

Lemma dtyp_WF_size_nonzero τ :
  dtyp_WF τ ->
  sizeof_dtyp τ <> 0%N.
Proof.
  induction 0; cbn; eauto; try lia; inversion 1; subst; eauto.
  { specialize (IHτ H2). lia. }
  { rewrite List.Forall_forall in H3.
    induction fields; [ done | ].
    cbn in *.
    rewrite fold_sizeof.

    assert (sizeof_dtyp a <> 0%N).
    { eapply H; eauto. }
    lia. }
Qed.

Fixpoint dtyp_WF_b (d : dtyp) : bool :=
  match d with
  | DTYPE_I 1
  | DTYPE_I 8
  | DTYPE_I 32
  | DTYPE_I 64
  | DTYPE_Pointer
  | DTYPE_Float
  | DTYPE_Double => true
  | DTYPE_Array sz τ => dtyp_WF_b τ && negb (N.eqb sz 0)
  | DTYPE_Struct (x :: tl) => dtyp_WF_b x && forallb dtyp_WF_b tl
  | _ => false
  end.

Lemma dtyp_WF_b_dtyp_WF d :
  dtyp_WF_b d = true <-> dtyp_WF d.
Proof.
  split; intros; induction d; try constructor;
    cbn in *; destruct_match; try constructor;
    inversion H; eauto.
  { apply IHd.
    apply andb_prop in H1; destruct H1; auto. }
  { apply andb_prop in H; destruct H; auto.
    rewrite negb_true_iff in H0.
    intro. rewrite -N.eqb_eq in H2.
    rewrite H0 in H2; inversion H2. }
  { apply andb_prop in H; destruct H; auto.
    apply H0; eauto. apply in_eq. }
  { apply andb_prop in H; destruct H; auto.
    clear H2 H3. revert d H0 H.
    induction l; eauto; cbn. cbn in H1.
    apply andb_prop in H1; destruct H1; auto.
    intros; rewrite Forall_cons; split; eauto. }
  { subst. specialize (IHd H2).
    apply andb_true_intro; split; eauto.
    rewrite negb_true_iff.
    red in H3.
    rewrite -N.eqb_eq in H3.
    destruct ((sz =? 0)%N); eauto.
    exfalso; done. }
  subst. induction fields; eauto.
  rewrite Forall_cons in H3. destruct H3.
  apply andb_true_intro; split.
  { apply H0; eauto. apply in_eq. }
  { destruct fields; eauto.
    cbn. apply IHfields; eauto.
    { intros ; eapply H0; eauto.
      by apply in_cons. }
    { constructor; eauto. } }
Qed.

Definition non_void_b (d : dtyp) : bool :=
  match d with
  | DTYPE_Void => false
  | _ => true
  end.

Lemma non_void_b_non_void d :
  non_void_b d = true <-> non_void d.
Proof.
  split; unfold non_void_b; cbn; intros; destruct d;
    eauto; done.
Qed.

(* ------------------------------------------------------------------------ *)
(** *Utilities for [raw_id] *)

Definition raw_id_eqb (x y : raw_id) : bool :=
  match x, y with
  | Name x, Name y => (x =? y)%string
  | Anon x, Anon y => (x =? y)%Z
  | Raw x, Raw y => (x =? y)%Z
  | _, _ => false
  end.

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

(* ------------------------------------------------------------------------ *)
(** *Utilities for frame manipulation *)

Fixpoint frame_at (i : nat) (F : frame_stack) : mem_frame :=
  match i with
    | 0%nat =>
        (match F with
          | Snoc _ f => f
          | Mem.Singleton f => f
          end)
    | S n =>
      (match F with
      | Snoc F f => frame_at n F
      | Mem.Singleton _ => []
      end)
  end.

Definition peek_frame := frame_at 0.

(** *Utility about frame stacks *)
(* Utility functions on frame stack *)
Definition flatten_frame_stack (m : frame_stack) : mem_frame :=
  let fix _aux (m : frame_stack) (acc : mem_frame) :=
    match m with
      | Mem.Singleton m => (m ++ acc)%list
      | Snoc m f => (f ++ _aux m acc)%list
    end
  in _aux m [].

Fixpoint frame_count (m : frame_stack) : nat :=
  match m with
    | Mem.Singleton m => 1
    | Snoc m f => S (frame_count m)
  end.

Definition add_to_frame_stack (f : frame_stack) (k : Z) : frame_stack :=
  match f with
  | Mem.Singleton f => Mem.Singleton (k :: f)
  | Snoc s f => Snoc s (k :: f)
  end.

Definition delete_from_frame (f : mem_frame) (k : Z) : mem_frame :=
  remove Z.eq_dec k f.

Definition delete_from_frame_stack (f : frame_stack) (k : Z) : frame_stack :=
  match f with
  | Mem.Singleton f => Mem.Singleton (delete_from_frame f k)
  | Snoc s f => Snoc s (delete_from_frame f k)
  end.

Definition free_locations_from_frame (mf d : mem_frame):=
  (fold_left (fun m key => remove Z.eq_dec key m) d mf).

(* ------------------------------------------------------------------------ *)
(* Properties about frame stack *)

Lemma add_to_frame_stack_commute (A : frame_stack) (l : Z) :
  list_to_set (flatten_frame_stack (add_to_frame_stack A l)) =
  ({[ l ]} ∪ list_to_set (flatten_frame_stack A) : gset Z).
Proof.
  induction A; eauto.
Qed.

Lemma add_to_frame_stack_peek_frame_commute (A : frame_stack) (l : Z) :
  list_to_set (peek_frame (add_to_frame_stack A l)) =
  ({[ l ]} ∪ list_to_set (peek_frame A) : gset Z).
Proof.
  induction A; eauto.
Qed.

Lemma list_to_set_delete_from_frame (f : mem_frame) (l : Z) :
  list_to_set (delete_from_frame f l) = (list_to_set f ∖ {[l]} : gset Z).
Proof.
  revert l.
  induction f; cbn; eauto; first set_solver.
  intros. destruct (Z.eq_dec l a); subst; set_solver.
Qed.

Lemma delete_from_frame_stack_subseteq (A : frame_stack) (l : Z) :
  list_to_set (flatten_frame_stack (delete_from_frame_stack A l)) ⊆
  (list_to_set (flatten_frame_stack A) : gset Z).
Proof.
  revert l.
  induction A.
  { intros; cbn; rewrite !app_nil_r; rewrite list_to_set_delete_from_frame.
    set_solver. }
  intros; cbn.
  rewrite !list_to_set_app_L.
  apply union_mono_r. rewrite list_to_set_delete_from_frame.
  set_solver.
Qed.

Lemma delete_from_frame_stack_peek_frame_commute (A : frame_stack) (l : Z) :
  list_to_set (peek_frame (delete_from_frame_stack A l)) =
  (list_to_set (peek_frame A) ∖ {[ l ]} : gset Z).
Proof.
  revert l.
  induction A.
  { intros; cbn. by rewrite list_to_set_delete_from_frame. }
  cbn. intros; by rewrite list_to_set_delete_from_frame.
Qed.

(* ------------------------------------------------------------------------ *)
(* Utility lemma about frames *)

Lemma free_locations_from_frame_all mf' mf:
  NoDup mf ->
  NoDup mf' ->
  (list_to_set mf' : gset _) = list_to_set mf ->
  free_locations_from_frame mf' mf = nil.
Proof.
  revert mf'. induction mf; eauto; cbn.
  { cbn; intros; destruct mf'; set_solver. }
  intros.

  assert (list_to_set mf' = {[a]} ∪ (list_to_set (remove Z.eq_dec a mf'): gset _)).
  { setoid_rewrite list_to_set_delete_from_frame.
    rewrite -union_difference_singleton_L; try done.
    set_solver. }
  rewrite H2 in H1.

  apply NoDup_cons in H; destruct H.
  assert (list_to_set mf = (list_to_set (remove Z.eq_dec a mf') : gset _)).
  { apply union_cancel_l_L in H1.
    2 : rewrite list_to_set_delete_from_frame; set_solver.
    2 : set_solver.
    done. }
  assert (a ∈ mf') by set_solver.

  assert (NoDup (remove Z.eq_dec a mf')).
  { by apply util.NoDup_remove. }
  symmetry in H4.
  specialize (IHmf _ H3 H6 H4).
  symmetry.
  rewrite -IHmf.
  rewrite /free_locations_from_frame.
  done.
Qed.

Lemma free_frame_memory_proper mf mf' g:
  NoDup mf ->
  NoDup mf' ->
  (list_to_set mf : gset _) = list_to_set mf' ->
  free_frame_memory mf g = free_frame_memory mf' g.
Proof.
  revert mf' g.
  induction mf.
  { intros; destruct mf'; set_solver. }
  intros. cbn in H1.
  rewrite /free_frame_memory.
  cbn. destruct g; cbn; f_equiv.
  assert (a ∈ mf') by set_solver.
  assert (list_to_set mf' = {[a]} ∪ (list_to_set (remove Z.eq_dec a mf'): gset _)).
  { setoid_rewrite list_to_set_delete_from_frame.
    rewrite -union_difference_singleton_L; try done.
    set_solver. }
  rewrite H3 in H1.
  apply NoDup_cons in H; destruct H.
  assert (list_to_set mf = (list_to_set (remove Z.eq_dec a mf') : gset _)).
  { apply union_cancel_l_L in H1.
    2 : set_solver.
    2 : rewrite list_to_set_delete_from_frame; set_solver.
    done. }
  assert (NoDup (remove Z.eq_dec a mf')) by (by apply util.NoDup_remove).

  specialize (IHmf _ (delete a l, u) H4 H6 H5).
  inversion IHmf.
  rewrite H8.
  clear -H2 H0.
  rewrite fold_left_delete_comm.
  rewrite -(fold_delete_distr a); eauto.
  set_solver.
Qed.

(* Assumes that τ is not void *)
Definition allocate_non_void τ : mem -> (mem * addr) :=
  fun m =>
    let new_block := make_empty_logical_block τ in
    let key       := next_logical_key m in
    let m         := add_logical_block key new_block m in
    (add_to_frame m key, (key,0)%Z).

From Vellvm.Semantics Require Import InterpretationStack.

(* Utilities for associative map for function lookup at the top-level *)
Definition includes_keys : relation (list (dvalue * D.function_denotation)) :=
  fun fundefs fundefs' =>
  forall key value,
    lookup_defn key fundefs = Some value ->
    exists value', lookup_defn key fundefs' = Some value'.

Definition same_keys : relation (list (dvalue * D.function_denotation)) :=
  fun fundefs fundefs' =>
    includes_keys fundefs fundefs' /\ includes_keys fundefs' fundefs.

Instance same_keys_Symmetric : Symmetric same_keys.
intros x y []; split; eauto.
Qed.

Instance same_keys_Reflexive : Reflexive same_keys.
intros x; intros; split; repeat intro; eauto.
Qed.

Instance includes_keys_Transitive : Transitive includes_keys.
  repeat intro. specialize (H _ _ H1).
  destruct H as (?&?).
  specialize (H0 _ _ H). eauto.
Qed.

Instance same_keys_Transitive : Transitive same_keys.
  intros x y z [] []. split; etransitivity; eauto.
Qed.

Definition doesnt_include_keys {A} : relation (list (dvalue * A)) :=
  fun fundefs fundefs' =>
  forall key value,
    lookup_defn key fundefs = Some value ->
    not (exists value', lookup_defn key fundefs' = Some value').

Definition disjoint_keys {A} : relation (list (dvalue * A)) :=
  fun fundefs fundefs' =>
    doesnt_include_keys fundefs fundefs' /\ doesnt_include_keys fundefs' fundefs.

(* ------------------------------------------------------------------------ *)
(* Util lemmas about uvalues and dvalues *)
Lemma uvalue_to_dvalue_list :
  forall fields,
    (forall u : uvalue,
        List.In u fields ->
        is_concrete u ->
        exists dv : dvalue, uvalue_to_dvalue u = inr dv /\
            concretize_uvalue u = Monad.ret dv) ->
    forallb is_concrete fields = true ->
    exists dfields, Util.map_monad uvalue_to_dvalue fields = inr dfields /\
                  Util.map_monad concretize_uvalue fields = Monad.ret dfields.
Proof.
  induction fields; intros H' ALL.
  - exists nil. split; reflexivity.
  - assert (List.In a (a :: fields)) as IN.
    { constructor; auto. }

    change (a :: fields) with ([a] ++ fields)%list in ALL.
    rewrite forallb_app in ALL.
    apply andb_prop in ALL as (CONC_A & CONC_FIELDS).

    cbn in CONC_A.
    rewrite Bool.andb_true_r in CONC_A.
    apply Is_true_true_2 in CONC_A.
    pose proof (H' a IN CONC_A) as (dv & CONV_A&?).

    assert
      (∀ u : uvalue,
        In u fields
        → is_concrete u
          → ∃ dv : dvalue, uvalue_to_dvalue u = inr dv ∧
                            concretize_uvalue u = Monad.ret dv) as HCONV.
    { intros u INFS CONCU.
      apply H'; auto.
      apply in_cons; auto. }

    pose proof (IHfields HCONV CONC_FIELDS) as (dfields & CONV_DFIELDS & CONV_DFIELDS').
    exists (dv :: dfields).

    change (a :: fields) with ([a] ++ fields)%list.
    rewrite map_monad_app.
    cbn.
    rewrite CONV_A CONV_DFIELDS CONV_DFIELDS' H.
    split; reflexivity.
Qed.

Lemma is_concrete_uvalue_to_dvalue :
  forall uv,
    is_concrete uv ->
    exists dv, uvalue_to_dvalue uv = inr dv /\
          concretize_uvalue uv = Monad.ret dv.
Proof.
  intros uv CONC.
  induction uv;
    try inversion CONC; try (eexists; split; reflexivity).
  - cbn in CONC. cbn.
    pose proof uvalue_to_dvalue_list _ H as (dv & MAP & MAP').
    { by apply Is_true_true_1. }
    exists (DVALUE_Struct dv). rewrite MAP MAP'. split; eauto.
  - cbn.
    pose proof uvalue_to_dvalue_list _ H as (dv & MAP & MAP').
    { by apply Is_true_true_1. }
    exists (DVALUE_Array dv). rewrite MAP MAP'; split; eauto.
Qed.

Lemma uvalue_to_dvalue_inv u dv:
  uvalue_to_dvalue u = inr dv ->
  u = dvalue_to_uvalue dv.
Proof.
  intros H. revert dv H.
  induction u; intros; try solve [inversion H; eauto].
  { cbn in H0.
    destruct (map_monad uvalue_to_dvalue fields) eqn : Hfields; inversion H0; subst.
    clear H0. cbn. f_equiv.
    revert l Hfields H.
    induction fields; intros; cbn in *; [ inversion Hfields; eauto | ].
    destruct (uvalue_to_dvalue a) eqn: Ha; [ inversion Hfields | ].
    destruct (map_monad uvalue_to_dvalue fields) eqn : Hfields'; inversion Hfields; subst.
    cbn. erewrite <-H; eauto.
    rewrite <-IHfields; eauto. }
  { cbn in H0.
    destruct (map_monad uvalue_to_dvalue elts) eqn : Hfields; inversion H0; subst.
    clear H0. cbn. f_equiv.
    revert l Hfields H.
    induction elts; intros; cbn in *; [ inversion Hfields; eauto | ].
    destruct (uvalue_to_dvalue a) eqn: Ha; [ inversion Hfields | ].
    destruct (map_monad uvalue_to_dvalue elts) eqn : Hfields'; inversion Hfields; subst.
    cbn. erewrite <-H; eauto.
    rewrite <-IHelts; eauto. }
  { cbn in *; inversion H0. }
Qed.

Lemma concretize_uvalue_dvalue_to_uvalue u:
  concretize_uvalue (dvalue_to_uvalue u) = Monad.ret u.
Proof.
  induction u; intros; eauto.
  { induction fields; cbn in *; eauto.
    assert (Ha : a = a ∨ In a fields) by eauto.
    pose proof (H a Ha) as H'.
    rewrite H'; cbn.
    assert
      (IHp :
        (∀ u : dvalue, In u fields →
          concretize_uvalue (dvalue_to_uvalue u) =
                {| EitherMonad.unEitherT := inr (inr u) |})).
    { intros; eauto. }
    specialize (IHfields IHp).
    inversion IHfields.
    destruct (EitherMonad.unEitherT
      (Util.map_monad concretize_uvalue (map dvalue_to_uvalue fields)));
      inversion H1.
    destruct s; inversion H1; subst; cbn. eauto. }

  { induction elts; cbn in *; eauto.
    assert (Ha : a = a ∨ In a elts) by eauto.
    pose proof (H a Ha) as H'. rewrite H'; cbn.
    assert
      (IHp :
        (∀ u : dvalue, In u elts →
            concretize_uvalue (dvalue_to_uvalue u) =
                {| EitherMonad.unEitherT := inr (inr u) |})).
    { intros; eauto. }
    specialize (IHelts IHp); inversion IHelts.
    destruct (EitherMonad.unEitherT
      (Util.map_monad concretize_uvalue (map dvalue_to_uvalue elts)));
      inversion H1.
    destruct s; inversion H1; subst; cbn. eauto. }
Qed.

Lemma concretize_uvalue_dvalue_to_uvalue_map l :
  Util.map_monad concretize_uvalue (map dvalue_to_uvalue l) = Monad.ret l.
Proof.
  induction l; eauto.
  cbn. rewrite concretize_uvalue_dvalue_to_uvalue; cbn.
  cbn in IHl.
  destruct (map_monad concretize_uvalue (map dvalue_to_uvalue l)), unEitherT, s;
    inversion IHl; subst; cbn; eauto.
Qed.

Lemma is_concrete_dvalue_to_uvalue v :
  is_concrete (dvalue_to_uvalue v) = true.
Proof.
  induction v; eauto; cbn.
  { induction fields; cbn; auto.
    rewrite H; [ | by constructor].
    rewrite andb_true_l.
    apply IHfields; intros; eauto.
    eapply H; by apply in_cons. }
  { induction elts; cbn; auto.
    rewrite H; [ | by constructor].
    rewrite andb_true_l.
    apply IHelts; intros; eauto.
    eapply H; by apply in_cons. }
Qed.

Lemma is_concrete_imples_uvalue_to_dvalue uv:
  is_concrete uv ->
  exists v, uvalue_to_dvalue uv = inr v.
Proof.
  induction uv; intros; try inversion H; eauto.
  { induction fields; eauto.
    cbn in H0. apply andb_True in H0.
    destruct H0.
    pose proof (H _ (in_eq _ _) H0) as Heq.
    cbn. destruct Heq. rewrite H2.
    assert
      (Hin:
        ∀ u : uvalue,
          In u fields →
          is_concrete u →
          ∃ v : dvalue, uvalue_to_dvalue u = inr v).
    { intros; eapply H; eauto; by apply in_cons. }
    specialize (IHfields Hin H1).
    destruct IHfields.
    cbn in H3.
    destruct (Util.map_monad uvalue_to_dvalue fields);
      subst; inversion H3; eauto. }
  { induction elts; eauto.
    cbn in H0. apply andb_True in H0.
    destruct H0.
    pose proof (H _ (in_eq _ _) H0) as Heq.
    cbn. destruct Heq. rewrite H2.
    assert
      (Hin:
        ∀ u : uvalue,
          In u elts →
          is_concrete u →
          ∃ v : dvalue, uvalue_to_dvalue u = inr v).
    { intros; eapply H; eauto; by apply in_cons. }
    specialize (IHelts Hin H1).
    destruct IHelts.
    cbn in H3.
    destruct (Util.map_monad uvalue_to_dvalue elts);
      subst; inversion H3; eauto. }
  inversion H0.
Qed.

Lemma is_concrete_dvalue_to_uvalue_map l:
  forallb is_concrete (map dvalue_to_uvalue l) = true.
Proof.
  rewrite forallb_forall; intros.
  rewrite in_map_iff in H. destruct H as (?&?&?); subst; eauto.
  apply is_concrete_dvalue_to_uvalue.
Qed.

Lemma is_concrete_concretize_uvalue u :
  is_concrete u ->
  exists x, concretize_uvalue u = Monad.ret x /\ u = dvalue_to_uvalue x.
Proof.
  induction u; intros; try solve [inversion H]; eauto.
  { induction fields; eauto.
    cbn in H0; cbn; rewrite andb_True in H0.
    destruct H0; eauto.
    destruct (H _ (in_eq _ _) H0) as (?&?&?).
    rewrite H2; clear H2; cbn; subst.
    assert
      (∀ u : uvalue,
        In u fields →
        is_concrete u →
        ∃ x : dvalue, concretize_uvalue u = Monad.ret x /\ u = dvalue_to_uvalue x).
    { intros; destruct (H _ (in_cons _ _ _ H2) H3) as (?&?&?); eauto. }
    specialize (IHfields H2 H1); clear H1 H2.
    destruct IHfields as (?&?&?). cbn in H1.
    inversion H1.
    destruct (Util.map_monad concretize_uvalue fields);
      destruct unEitherT, s; inversion H1; subst; cbn; eauto.
    eexists; split; [ done | ]. cbn; do 2 f_equiv.
    cbn in H2. by inversion H2. }

  { induction elts; eauto.
    cbn in H0; cbn; rewrite andb_True in H0.
    destruct H0; eauto.
    destruct (H _ (in_eq _ _) H0) as (?&?&?).
    rewrite H2; clear H2; cbn; subst.
    assert
      (∀ u : uvalue,
        In u elts →
        is_concrete u →
        ∃ x : dvalue, concretize_uvalue u = Monad.ret x /\ u = dvalue_to_uvalue x).
    { intros; destruct (H _ (in_cons _ _ _ H2) H3) as (?&?&?); eauto. }
    specialize (IHelts H2 H1); clear H1 H2.
    destruct IHelts as (?&?&?). cbn in H1.
    inversion H1.
    destruct (Util.map_monad concretize_uvalue elts);
      destruct unEitherT, s; inversion H1; subst; cbn; eauto.
    eexists; split; [ done | ]. cbn; do 2 f_equiv.
    cbn in H2. by inversion H2. }

  cbn in H0; inversion H0.
Qed.

Lemma forallb_is_concrete_concretize_uvalue fields:
  forallb is_concrete fields = true ->
  exists x, (Util.map_monad concretize_uvalue fields) = Monad.ret x.
Proof.
  induction fields; eauto.
  cbn. rewrite andb_true_iff.
  intros (?&?). apply Is_true_true_2 in H.
  apply is_concrete_concretize_uvalue in H; destruct H as (?&?&?).
  rewrite H; cbn.
  specialize (IHfields H0).
  destruct IHfields as (?&IHfields); rewrite IHfields; eauto.
Qed.

Lemma map_monad_dvalue_to_uvalue fields l k x:
  map_monad default_dvalue_of_dtyp fields = inr l ->
  l !! k = Some x ->
  exists v v',
    In v fields /\
    default_dvalue_of_dtyp v = inr v' /\
    x = v'.
Proof.
  revert l k x.
  induction fields; cbn; intros; inversion H;
    subst; [ inversion H0 | ].
  destruct (default_dvalue_of_dtyp a) eqn : Ha; [ inversion H | ].
  destruct (map_monad default_dvalue_of_dtyp fields) eqn: Hfields;
    inversion H; subst; clear H; cbn in H0.
  rewrite lookup_cons in H0.
  destruct k; inversion H0; subst; eauto; [ exists a, x ; eauto | ].
  specialize (IHfields l0 k x eq_refl H0).
  destruct IHfields as (?&?&?&?&?).
  eexists _, _; eauto.
Qed.

(* ------------------------------------------------------------------------ *)
(* Utility about [lookup_defn] *)

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
