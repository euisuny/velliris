(** * Heap representation. *)

From iris.algebra Require Import big_op gmap frac agree numbers gset list.
From iris.algebra Require Import csum excl auth cmra_big_op numbers gmap_view.
From iris.bi Require Import fractional.
From iris.base_logic Require Export lib.own.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From iris.prelude Require Import options.
From iris.proofmode Require Export tactics.

From velliris.vir Require Export vir util vir_util.
Set Default Proof Using "Type".
Import uPred.

From Vellvm Require Import Syntax.DynamicTypes.
From Vellvm Require Import Handlers.Handlers Numeric.Integers.
Open Scope Z_scope.

(* A points-to is a [block id * offset -> list byte] such that points-to's
  can be split and combined.

  We can define a high-level notion of [l ↦ v] with [list-of-bytes] and
  [serialize_dvalue]. *)

Definition heapUR : ucmra :=
  gmapUR Z (prodR fracR (agreeR valO)).

Definition heap := gmap loc logical_block.
Definition to_heap : heap → heapUR := fmap (λ v, (1%Qp, (to_agree v))).

(* Set of names that are relevant to frames *)
Record frame_names := {
  index : nat;
  (* Names related to local environment *)
  local_name : gname;
  ldomain_name : gname;
  (* Names related to [allocaS] *)
  allocaS_name : gname;
}.

Class heapG Σ := HeapGS {
  (* Logical memory *)
  heapGS_inG :> inG Σ (authR heapUR);
  heapGS_block_size_inG :> ghost_mapG Σ loc (option nat);
  (* Keeps track of the stack, and the names associated with each frame on the
    stack *)
  heapGS_stackG :> ghost_varG Σ (list frame_names);
  (* Set of allocated locations in current frame *)
  heapGS_allocaSG :> ghost_varG Σ (gset Z);
  (* Global environment: read-only map *)
  heap_globals_inG :> inG Σ (agreeR (leibnizO global_env));
  (* Local environment *)
  lheapG_localG :> ghost_mapG Σ local_loc local_val;
  (* Domain of local env *)
  lheapG_domain:> ghost_varG Σ (gset local_loc);
  (* Stack for the local environment *)
  lheapG_stackG :> ghost_varG Σ lstack;}.

Definition heapΣ :=
  #[GFunctor (authR heapUR);
    ghost_mapΣ loc (option nat);
    ghost_varΣ (list frame_names);
    ghost_varΣ (gset Z);
    GFunctor (agreeR (leibnizO global_env));
    ghost_mapΣ local_loc local_val;
    ghost_varΣ (gset local_loc);
    ghost_varΣ lstack].

#[global] Instance subG_heapΣ Σ:
  subG heapΣ Σ -> heapG Σ.
Proof. solve_inG. Qed.

Record heap_names := {
  heap_name : gname;
  heap_block_size_name : gname;
  globals_name : gname;
  stack_name : gname;
}.

(* Conversion from [VIR] state to logical view using [gmap]s *)
Definition vir_heap (m : memory_stack) : gmap Z logical_block := m.1.1.
Definition vir_dyn (m : memory_stack) : gset Z := m.1.2.

Definition to_addr (l : loc) := (l, 0)%Z.

Notation "⊙ m" := (vir_heap m) (at level 30).

(* This dummy name will never be inspected because the [heap_WF] states that
    the frame is non-nil *)
Definition dummy_frame_name : frame_names.
  constructor. 1: exact 0%nat. all : exact xH.
Qed.

Definition heap_block_size_rel (σ: heap * gset Z) (hF : gmap loc (option nat)) : Prop :=
  (forall b o, hF !! b = Some o -> b ∈ σ.2) /\
  (∀ b, is_Some (σ.1 !! b) -> ∃ o, hF !! b = Some (Some o)).

Definition heap_WF (σ:heap) (A: frame_stack) (F : list frame_names) :=
  (* Everything in the allocaS frame can be found in memory *)
  NoDup (flatten_frame_stack A) /\
  let MF : gset Z := list_to_set (flatten_frame_stack A) in
  (MF = dom σ) ∧
  (* (forall (z : Z), z ∈ MF -> is_Some (σ !! z)) ∧ *)
  (* current frame is unique from other frame names (might need to state more uniqueness) *)
  (* [F] should correspond to the length of the frame stack,
    indicating "availability of popping a frame"*)
  (length F) = frame_count A /\ length F > 0%nat
  /\ (forall n, n < length F ->
      (nth n F dummy_frame_name).(index) = length F - n - 1)%nat.

Fixpoint dtyp_of_dvalue (dv : dvalue) : dtyp :=
  match dv with
  | DVALUE_Addr _ => DTYPE_Pointer
  | DVALUE_I1 _ => DTYPE_I 1%N
  | DVALUE_I8 _ => DTYPE_I 8%N
  | DVALUE_I32 _ => DTYPE_I 32%N
  | DVALUE_I64 _ => DTYPE_I 64%N
  | DVALUE_Double _ => DTYPE_Double
  | DVALUE_Float  _ => DTYPE_Float
  | DVALUE_Struct l => DTYPE_Struct (dtyp_of_dvalue <$> l)
  (* Note simplified assumption: an empty array should be a polymorphic array *)
  | DVALUE_Array (a :: l) => DTYPE_Array (N.of_nat (length l)) (dtyp_of_dvalue a)
  | _ => DTYPE_Void
  end.

(** *Definition of [mapsto] for heap :
    The heap stores bytes, offset by an allocaStion id (Z) and an offset (Z).
    Using [maps_bytes_source]/[maps_bytes_target], bytes can be directly stored
    in the heap. Otherwise [maps_source]/[maps_target] stores dvalues which are
    serialized into bytes.

    N.B. for simplicity, we do not use [undefined values (uvalues)] for the
    heap representations. *)
Section definitions.
  Context `{!heapG Σ} `{!FUpd (iProp Σ)} (γ : heap_names).

  Definition mapsto_def (l : Z) (q : Qp) (b : val) : iProp Σ :=
    own γ.(heap_name) (◯ {[ l := (q, to_agree b) ]}).
  Definition mapsto_aux : seal (@mapsto_def). by eexists. Qed.
  Definition mapsto:= unseal mapsto_aux.
  Definition mapsto_eq : @mapsto = @mapsto_def :=
    seal_eq mapsto_aux.

  Definition dvalue_to_block (v : dvalue) : logical_block :=
    let bytes := add_all_index (serialize_dvalue v) 0%Z
            (init_block (N.of_nat (length (serialize_dvalue v)))) in
    LBlock (N.of_nat (length (serialize_dvalue v))) bytes None.

  Definition mapsto_dval_def (l : loc) (q : Qp) (v : dvalue) : iProp Σ :=
    mapsto l q (dvalue_to_block v).

  Definition mapsto_dval_aux : seal (@mapsto_dval_def). Proof. by eexists. Qed.
  Definition mapsto_dval:= mapsto_dval_aux.(unseal).
  Definition mapsto_dval_eq : @mapsto_dval = @mapsto_dval_def := mapsto_dval_aux.(seal_eq).

  Definition heap_block_size_def (l : loc) (q : Qp) (n : option nat) : iProp Σ :=
    l ↪[ γ.(heap_block_size_name) ]{# q } n.
  Definition heap_block_size_aux : seal (@heap_block_size_def). Proof. by eexists. Qed.
  Definition heap_block_size := unseal heap_block_size_aux.
  Definition heap_block_size_eq : @heap_block_size = @heap_block_size_def :=
    seal_eq heap_block_size_aux.

  Definition globals_def g : iProp Σ :=
    own γ.(globals_name) (to_agree g).
  Definition globals_aux : seal (@globals_def). Proof. by eexists. Qed.
  Definition globals:= globals_aux.(unseal).
  Definition globals_eq : @globals = @globals_def := globals_aux.(seal_eq).

  Definition global_def (g : LLVMAst.global_id) (v : dvalue) : iProp Σ :=
    ∃ gs, ⌜gs !! g = Some v⌝ ∗ globals gs.
  Definition global_aux : seal (@global_def). Proof. by eexists. Qed.
  Definition global := unseal global_aux.
  Definition global_eq : @global = @global_def :=
    seal_eq global_aux.

  Definition allocaS_def (γ : heap_names) (i : frame_names) (z : gset Z) :=
    (ghost_var i.(allocaS_name) (1/2) z)%I.
  Definition allocaS_aux : seal (@allocaS_def). Proof. by eexists. Qed.
  Definition allocaS:= allocaS_aux.(unseal).
  Definition allocaS_eq : @allocaS = @allocaS_def := allocaS_aux.(seal_eq).

  Definition lmapsto_def (γ : heap_names) (i : frame_names) (l : local_loc) (v : local_val) : iProp Σ :=
    l ↪[i.(local_name)] v.
  Definition lmapsto_aux : seal (@lmapsto_def). by eexists. Qed.
  Definition lmapsto := unseal lmapsto_aux.
  Definition lmapsto_eq : @lmapsto = @lmapsto_def :=
    seal_eq lmapsto_aux.

  Definition stack (F : list frame_names) : iProp Σ :=
    ghost_var γ.(stack_name) (1/2) (F).

  Definition ldomain (γ : heap_names) i (S: gset local_loc) : iProp Σ :=
    ghost_var i.(ldomain_name) (1/2) (S).

  Definition current_frame (F : list frame_names) : frame_names :=
    List.hd dummy_frame_name F.

  Definition heap_ctx
    (σ : heap * gset Z)
    (mf : frame_stack)
    (G : global_env)
    (L : local_env)
    (LS : lstack) : iProp Σ :=
    let allocated_at_current_frame :=
      (list_to_set (peek_frame mf) : gset _) in
    (∃ i hF,
      (* Memory *)
      own γ.(heap_name) (● to_heap σ.1)
      ∗ ghost_map_auth γ.(heap_block_size_name) 1 hF
      (* Resources for current frame *)
      ∗ stack i
      ∗ ghost_var (current_frame i).(allocaS_name) (1/2) allocated_at_current_frame
      ∗ ghost_map_auth (current_frame i).(local_name) 1 (list_to_map L)
      ∗ ldomain γ (current_frame i) (list_to_set L.*1)
        (* Resources on the stack *)
      ∗ ([∗ list] i ↦ f; env ∈ tl i; LS,
          ghost_map_auth f.(local_name) 1 (list_to_map env)
          ∗ ldomain γ f (list_to_set env.*1)
          ∗ ⌜NoDup env.*1⌝
          ∗ ghost_var f.(allocaS_name) (1/2) (list_to_set (frame_at (S i) mf) : gset _))
      (* Global env *)
      ∗ globals G
      ∗ ⌜NoDup L.*1⌝
      ∗ ⌜heap_block_size_rel σ hF⌝
      ∗ ⌜heap_WF σ.1 mf i⌝)%I.

End definitions.

Ltac destruct_HC s :=
  iDestruct s as (cf hF)
    "(Hσ&Hb&HCF&HA&HL&HD&HSA&HG&%Hdup&%Hbs&%Hwf)".

Typeclasses Opaque mapsto.
Global Instance: Params (@mapsto) 4 := {}.

Section to_heap.

  Lemma to_heap_valid σ : ✓ to_heap σ.
  Proof. intros l. rewrite lookup_fmap. case (σ !! l)=> [|] //=. Qed.

  Lemma to_heap_insert h l v:
    to_heap (<[l:=v]> h) = <[l:=(1%Qp, to_agree v)]> (to_heap h).
  Proof. by rewrite /to_heap fmap_insert. Qed.

  Lemma lookup_to_heap_None σ l : σ !! l = None → to_heap σ !! l = None.
  Proof. by rewrite /to_heap lookup_fmap=> ->. Qed.

  Lemma to_heap_delete σ l : to_heap (base.delete l σ) = base.delete l (to_heap σ).
  Proof. by rewrite /to_heap fmap_delete. Qed.

  Lemma to_heap_fold_delete σ f :
    to_heap (fold_left (fun m key => base.delete key m) f σ) =
    fold_left (fun m key => base.delete key m) f (to_heap σ).
  Proof.
    revert σ.
    induction f; eauto.
    cbn. intros. rewrite !fold_left_delete_comm.
    rewrite to_heap_delete. by rewrite IHf.
  Qed.

End to_heap.


(** *Utility lemmas *)
Section logical_view.

  Lemma map_fmap {A B} (f : A -> B) (l : list A) :
    map f l = fmap f l.
  Proof.
    induction l; auto.
  Qed.

  Lemma next_logical_key_None_heap m :
    (vir_heap m) !! next_logical_key m = None.
  Proof.
    unfold next_logical_key, next_logical_key_mem, logical_next_key.
    cbn.
    rewrite /vir_heap; destruct m; cbn.

    pose proof (next_logical_key_fresh_logical_mem m).
    apply not_elem_of_dom in H. done.
  Qed.

  Lemma next_logical_key_None_dyn m :
    next_logical_key m ∉ (vir_dyn m).
  Proof.
    unfold next_logical_key, next_logical_key_mem, logical_next_key.
    cbn.
    rewrite /vir_heap; destruct m; cbn.

    pose proof (next_logical_key_fresh_dyn m).
    done.
  Qed.

  Lemma vir_logical_frame_add_to_frame l f m :
    vir_heap (add_logical_block l f m) =
    vir_heap (add_to_frame (add_logical_block l f m) l).
  Proof.
    destruct m; cbn.
    rewrite /vir_heap; cbn.
    destruct m as (m & ?); cbn.
    rewrite /add_logical_block_mem; cbn.
    destruct f0; eauto.
  Qed.

  Lemma get_logical_block_logical_view_None l m :
    vir_heap m !! l = None <->
    get_logical_block m l = None.
  Proof.
    destruct m; cbn. done.
  Qed.

  Lemma get_logical_block_logical_view m l v:
    vir_heap m !! l = Some v <->
    get_logical_block m l = Some v.
  Proof.
    destruct m; cbn. done.
  Qed.

  Lemma vir_heap_add_logical_block l m f:
    <[ l := f ]> (vir_heap m) =
    (vir_heap (add_logical_block l f m)).
  Proof.
    rewrite /vir_heap. rewrite /add_logical_block.
    destruct m; eauto.
  Qed.

  Lemma vir_heap_delete x (m : memory_stack):
    base.delete x (vir_heap m) =
    (vir_heap ((delete x m.1.1, m.1.2), m.2)).
  Proof. eauto. Qed.

  Lemma vir_heap_free_frame (f0 : mem_frame) m f:
    (⊙ (free_frame_memory f0 m, f) =
    (fold_left (λ m key, base.delete key m) f0 (⊙ (m, f)))).
  Proof.
    rewrite /vir_heap; cbn.
    rewrite /free_frame_memory. done.
  Qed.

  Lemma read_uvalue_logical_view (v : dvalue) τ m l:
    is_supported τ ->
    dvalue_has_dtyp v τ ->
    vir_heap m !! l = Some (dvalue_to_block v) ->
    read m (to_addr l) τ = inr (dvalue_to_uvalue v).
  Proof.
    intros Hs Hτ Hr.
    apply get_logical_block_logical_view in Hr.
    rewrite /read. cbn. setoid_rewrite Hr; cbn.
    rewrite /read_in_mem_block; cbn.
    rewrite deserialize_serialize; eauto.
  Qed.

  Lemma vir_heap_insert l m f:
    <[ l := f ]> (vir_heap m) =
    (vir_heap (add_to_frame (add_logical_block l f m) l)).
  Proof.
    intros. rewrite -vir_logical_frame_add_to_frame.
    apply vir_heap_add_logical_block.
  Qed.

End logical_view.

Section globals.
  Context `{!heapG Σ} (γ : heap_names).

  Global Instance globals_persistent gs : Persistent (globals γ gs).
  Proof. rewrite globals_eq. apply _. Qed.
  Global Instance globals_timeless gs : Timeless (globals γ gs).
  Proof. rewrite globals_eq. apply _. Qed.

  Lemma global_intro g gs :
    g ∈ dom gs ->
    globals γ gs -∗
    ∃ v, global γ g v.
  Proof.
    rewrite global_eq. iIntros (?) "?".
    rewrite elem_of_dom in H; inversion H.
    iExists _; iFrame; iExists _; iFrame.
    by iPureIntro.
  Qed.

  Lemma globals_agree gs1 gs2 :
    globals γ gs1 -∗ globals γ gs2 -∗ ⌜gs1 = gs2⌝.
  Proof.
    rewrite globals_eq. iIntros "H1 H2".
    iCombine "H1 H2" gives %Hvalid.
    by move: Hvalid => /to_agree_op_valid.
  Qed.

  Lemma global_in gs g v:
    globals γ gs -∗ global γ g v -∗ ⌜gs !! g = Some v⌝.
  Proof.
    rewrite global_eq.
    iIntros "Hgs (%gs' &%&Hgs')".
    by iDestruct (globals_agree with "Hgs Hgs'") as %->.
  Qed.

End globals.

Section local_properties.

  Context `{!heapG Σ} {γ : heap_names}.

  Notation "❲ % l := v ❳ i" := (lmapsto γ (current_frame i) l v)
                          (at level 20, format "❲ % l := v ❳ i") : bi_scope.

  #[global] Instance lmapsto_timeless l i v : Timeless (❲ %l := v ❳ i).
  Proof. rewrite lmapsto_eq /lmapsto_def. apply _. Qed.

  Lemma list_to_map_lookup (L' : local_env) l l1:
    (list_to_map L' : gmap _ _) !! l = Some l1 -> ∃ n, L' !! n = Some (l, l1).
  Proof.
    induction L'; cbn; intros.
    { rewrite lookup_empty in H; inversion H. }
    destruct (decide (a.1 = l)).
    { subst. rewrite lookup_insert in H. inversion H; subst.
      exists 0%nat. cbn. destruct a; auto. }
    { rewrite lookup_insert_ne in H; auto.
      specialize (IHL' H). destruct IHL'.
      exists (S x).
      by rewrite lookup_cons. }
  Qed.

  Lemma elem_of_fst l (L : local_env):
    l ∈ L.*1 -> exists v, (l, v) ∈ L.
  Proof.
    induction L; cbn; intros; eauto.
    { by apply elem_of_nil in H. }
    { destruct a. cbn in *.
      destruct (decide (l = r)); subst.
      { setoid_rewrite elem_of_cons. eauto. }
      { apply elem_of_cons in H. destruct H; [ done | ].
        specialize (IHL H). destruct IHL.
        setoid_rewrite elem_of_cons; eauto. } }
  Qed.

  Lemma lmapsto_alloc h l v (i : list frame_names):
    h !! l = None ->
    ⊢ ghost_map_auth (current_frame i).(local_name) 1 h ==∗
    ghost_map_auth (current_frame i).(local_name) 1 (<[l := v]>h) ∗ ❲ %l := v ❳ i.
  Proof.
    iIntros (?) "H".
    rewrite lmapsto_eq.
    by iApply ghost_map_insert.
  Qed.

  Lemma lmapsto_lookup h l v i:
    ghost_map_auth i.(local_name) 1 h -∗
    lmapsto γ i l v -∗
    ⌜h !! l = Some v⌝.
  Proof.
    rewrite lmapsto_eq /lmapsto_def.
    iApply ghost_map_lookup.
  Qed.

  Lemma lheap_lookup h mf g L LS l v i:
    heap_ctx γ h mf g L LS -∗
    stack γ i -∗
    ❲ %l := v ❳ i -∗
    ⌜(list_to_map L: gmap _ _) !! l = Some v⌝.
  Proof.
    iIntros "HC Hcf Hl".
    destruct_HC "HC".

    iDestruct (ghost_var_agree with "Hcf HCF") as %H; subst.

    iDestruct (lmapsto_lookup with "HL Hl") as %H; by iFrame.
  Qed.

  Lemma lmapsto_no_dup L cf:
     ([∗ list] '(l, v) ∈ L, lmapsto γ cf l v) -∗ ⌜NoDup L.*1⌝.
  Proof.
    iIntros "H".
    iInduction L as [ | n L] "IHn".
    { cbn. iPureIntro. apply NoDup_nil_2. }
    { cbn. destruct n. cbn.
      iDestruct "H" as "(H&H')".
      iDestruct ("IHn" with "H'") as "%H".
      rewrite NoDup_cons.
      iSplit; [ | done].
      iIntros (?). apply elem_of_fst in H0.
      destruct H0.
      iPoseProof (big_sepL_elem_of with "H'") as "H'"; eauto.
      cbn. rewrite lmapsto_eq /lmapsto_def.
      by iPoseProof (ghost_map_elem_ne with "H H'") as "%H'". }
  Qed.

  Lemma ldomain_ctx h mf G L LS LD i:
    heap_ctx γ h mf G L LS -∗
    stack γ i -∗
    ldomain γ (current_frame i) LD -∗
    ⌜LD = list_to_set L.*1⌝.
  Proof.
    iIntros "HC Hcf Hd".
    destruct_HC "HC".
    iDestruct (ghost_var_agree with "Hcf HCF") as %H; subst.
    iDestruct (ghost_var_agree with "Hd HD") as %H; by subst.
  Qed.

  Lemma lheap_write_vs h l v v' i:
    ghost_map_auth (local_name (current_frame i)) 1 h -∗ ❲ %l :=  v ❳ i ==∗
    ghost_map_auth (local_name (current_frame i)) 1 (<[l:=v']> h)
    ∗ ❲ % l := v' ❳ i.
  Proof.
    rewrite lmapsto_eq. iApply ghost_map_update.
  Qed.

  Lemma alist_add_domain_stable:
    ∀ (L : local_env) (l : local_loc) (v v': local_val),
      (list_to_map L : gmap _ _) !! l = Some v ->
      (list_to_set (FMapAList.alist_add AstLib.eq_dec_raw_id l v' L).*1 =
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

  Lemma lheap_write h l v v' i mf g L LS:
    heap_ctx γ h mf g L LS -∗
    stack γ i -∗
    ❲ %l := v ❳ i ==∗
    heap_ctx γ h mf g (FMapAList.alist_add AstLib.eq_dec_raw_id l v' L) LS ∗
    stack γ i ∗
    ❲ %l := v' ❳ i.
  Proof.
    iIntros "Hσ Hcf Hmt".
    iDestruct (lheap_lookup with "Hσ Hcf Hmt") as %?; auto.
    destruct_HC "Hσ".

    iDestruct (ghost_var_agree with "Hcf HCF") as %H'; subst.
    iMod (lheap_write_vs with "HL Hmt") as "[HL $]".
    iModIntro. unfold heap_ctx; iFrame.
    repeat iExists _. iFrame.
    erewrite alist_add_domain_stable; eauto.

    rewrite list_to_map_insert; iFrame.

    iSplitR; [ | done]; iPureIntro.
    by apply no_dup_alist_add.
  Qed.

  Lemma lheap_domain_alloc h l v D mf g L LS i :
    l ∉ D ->
    ldomain γ (current_frame i) D -∗
    stack γ i -∗
    heap_ctx γ h mf g L LS ==∗
    heap_ctx γ h mf g (FMapAList.alist_add AstLib.eq_dec_raw_id l v L) LS ∗
    ❲ %l := v ❳ i ∗
    stack γ i ∗
    ldomain γ (current_frame i) ({[ l ]} ∪ D).
  Proof.
    iIntros (Hin) "Hd Hf Hσ".
    destruct_HC "Hσ".

   iDestruct (ghost_var_agree with "Hf HCF") as %<-.
    iDestruct (ghost_var_agree with "Hd HD") as %->.

    assert ((list_to_map L : gmap _ _)!! l = None).
    { apply not_elem_of_list_to_map_1; set_solver. }

    iMod (lmapsto_alloc _ _ _ _ H with "HL") as "[H Hp]".
    iMod (ghost_var_update_halves ({[l]} ∪ (list_to_set L.*1)) with "Hd HD") as "[Hd Hd']".
    iModIntro; iFrame.
    rewrite list_to_set_insert.
    rewrite list_to_map_insert. iFrame.
    repeat iExists _; iFrame.

    iSplitR; [ | done]; iPureIntro.
    by apply no_dup_alist_add.
  Qed.

End local_properties.

Section heap.
  Context `{!heapG Σ} (γ : heap_names).

  Notation "l ↦ v" := (mapsto_dval γ l 1 v)
                        (at level 20, format "l  ↦  v") : bi_scope.
  Notation "l ↦{ q } v" := (mapsto_dval γ l q v)
                        (at level 20, format "l  ↦{ q }  v") : bi_scope.
  Notation "l ↦ [ b ]" := (vir_state.mapsto γ l 1 b)
                        (at level 20, format "l  ↦  [ b ]") : bi_scope.
  Notation "l ↦{ q } [ b ]" := (vir_state.mapsto γ l q b )
                        (at level 20, format "l  ↦{ q }  [ b ]") : bi_scope.
  Local Notation block_size := (heap_block_size γ).

  (** General properties of mapsto and block_size *)
  Global Instance mapsto_timeless l v : Timeless (l ↦ [ v  ]).
  Proof. rewrite mapsto_eq /mapsto_def. apply _. Qed.

  Lemma mapsto_valid l dq v : l ↦{dq} [v] -∗ ⌜✓ dq⌝%Qp.
  Proof.
    rewrite mapsto_eq. iIntros "Hl".
    iDestruct (own_valid with "Hl") as %?auth_frag_valid.
    rewrite auth_frag_valid in auth_frag_valid.
    iPureIntro.
    rewrite singleton_valid pair_valid in auth_frag_valid.
    destruct auth_frag_valid; auto.
  Qed.

  Lemma heap_mapsto_split l q q1 q2 v:
    q = (q1 + q2)%Qp →
    l ↦{q} [v] ⊣⊢ l ↦{q1} [v] ∗ l ↦{q2} [v].
  Proof.
    intros ->.
    rewrite mapsto_eq -own_op -auth_frag_op singleton_op -!pair_op
      agree_idemp /= //.
  Qed.

  Lemma heap_mapsto_combine_0 l q1 q2 v:
    l ↦{q1} [v] ⊢ l ↦{q2} [v] -∗
    l ↦{q1 + q2} [v].
  Proof.
    apply: wand_intro_r.
    rewrite mapsto_eq -own_op -auth_frag_op singleton_op -!pair_op agree_idemp /= //.
  Qed.

  Global Instance heap_mapsto_fractional l v: Fractional (λ q, l ↦{q} [v])%I.
  Proof. intros p q. by rewrite heap_mapsto_split /= //. Qed.
  Global Instance heap_mapsto_as_fractional l q v:
    AsFractional (l ↦{q} [v]) (λ q, l ↦{q} [v])%I q.
  Proof. split; first done. apply _. Qed.

  Global Instance heap_block_size_timeless q b n : Timeless (heap_block_size γ b q n).
  Proof. rewrite heap_block_size_eq /heap_block_size_def. apply _. Qed.

  Lemma mapsto_block_to_dvalue l dv dt:
    dvalue_has_dtyp dv dt ->
    l ↦ [LBlock (sizeof_dtyp dt)
          (add_all_index (serialize_dvalue dv) 0 (make_empty_mem_block dt)) None] ⊣⊢
    l ↦ dv.
  Proof.
    rewrite mapsto_dval_eq.
    rewrite /mapsto_dval_def /dvalue_to_block. intros.
    apply sizeof_serialized in H. rewrite H.
    by rewrite /make_empty_mem_block.
  Qed.

  Lemma mapsto_bytes_agree l q1 q2 v1 v2 :
    l ↦{q1} [ v1 ] ∗ l ↦{q2} [ v2 ] ⊢ ⌜v1 = v2⌝.
  Proof.
    rewrite mapsto_eq.
    unfold mapsto_def.
    rewrite -own_op -auth_frag_op own_valid uPred.discrete_valid.
    eapply bi.pure_elim; [done|]. move => /auth_frag_valid /=.
    rewrite singleton_op singleton_valid.
    rewrite -pair_op => -[? /to_agree_op_inv_L->]; eauto.
  Qed.

  Lemma mapsto_lookup_byte l h q b:
    own γ.(heap_name) (● to_heap h) -∗
    l ↦{q} [ b ] -∗
    ⌜h !! l = Some b⌝.
  Proof.
    iIntros "H● H◯".
    rewrite mapsto_eq /mapsto_def.
    iDestruct (own_valid_2 with "H● H◯") as %[Hl?]%auth_both_valid_discrete.
    iPureIntro. move: Hl=> /singleton_included_l [ls' ].
    rewrite /to_heap lookup_fmap fmap_Some_equiv.
    move=> [[ls'' [? v']] ]; simplify_eq. intros. rewrite v' in b0; clear v'.
    pose proof (Some_pair_included _ _ _ _ b0) as (?&?).
    rewrite Some_included_total
           to_agree_included in H1.
    inversion b0; cbn in *. eauto.

    Typeclasses eauto := 3. rewrite H1; auto.
    Typeclasses eauto := .
  Qed.

  Lemma mapsto_lookup l h q v:
    own γ.(heap_name) (● to_heap h) -∗
    l ↦{q} v -∗
    ⌜h !! l = Some (dvalue_to_block v)⌝.
  Proof.
    iIntros "H● H◯".
    rewrite mapsto_dval_eq /mapsto_dval_def.
    iApply (mapsto_lookup_byte with "H● H◯").
  Qed.

  Lemma heap_block_size_excl l l' n n' :
    l = l' →
    block_size l 1 n -∗ block_size l' 1 n' -∗ False.
  Proof.
    rewrite heap_block_size_eq.
    iIntros (->) "Hl1 Hl2"; simplify_eq/=.
    by iCombine "Hl1 Hl2" gives %[? ?].
  Qed.

  Definition logical_block_size (b : logical_block) : nat :=
    match b with
    | LBlock size bytes concrete_id => N.to_nat size
    end.

  Lemma fold_left_delete_some {A} f hF b o:
    fold_left (λ (m : gmap loc A) (key : Z), delete key m) f hF !! b = Some o ->
    hF !! b = Some o.
  Proof.
    revert hF b o.
    induction f; eauto.
    intros. cbn in H.
    rewrite fold_left_delete_comm in H.

    destruct (decide (a = b)) as [->|?].
    - rewrite lookup_delete in H; inversion H.
    - rewrite lookup_delete_ne in H; eauto.
  Qed.

  Lemma heap_WF_stable σ A F l p:
    heap_WF σ A F → is_Some (σ !! l) →
    heap_WF (<[l := p]> σ) A F.
  Proof.
    intros (? & REL & H & ?) Hσ.
    do 2 (split; auto).
    by rewrite dom_insert_lookup_L.
  Qed.

  Lemma heap_WF_extend_stable σ A F l p:
    heap_WF σ A F → σ !! l = None →
    heap_WF (<[l := p]> σ) (add_to_frame_stack A l) F.
  Proof.
    intros (? & REL & Hs & ? & ?) Hσ; repeat split; auto; cycle 2.
    { rewrite Hs. rewrite /add_to_frame_stack /frame_count; destruct A; eauto. }
    { rewrite /flatten_frame_stack /add_to_frame_stack; cbn; destruct A; eauto.
      - rewrite app_nil_r. cbn in H.
        rewrite app_nil_r in H.
        rewrite NoDup_cons; split; eauto.
        apply not_elem_of_dom_2 in Hσ. rewrite -REL in Hσ. cbn in Hσ.
        rewrite app_nil_r in Hσ.
        by eapply not_elem_of_list_to_set.
      - cbn. cbn in H. rewrite NoDup_cons; split; eauto.
        apply not_elem_of_dom_2 in Hσ. rewrite -REL in Hσ. cbn in Hσ.
        by eapply not_elem_of_list_to_set. }

    rewrite dom_insert_L. destruct A; cbn; eauto.
    - rewrite app_nil_r. f_equiv; cbn in REL.
      by rewrite app_nil_r in REL.
    - by cbn in REL; rewrite REL.
      Unshelve. all : typeclasses eauto.
  Qed.

  Lemma heap_WF_allocaS_stable:
    ∀ (τ : DynamicTypes.dtyp) (m0 : memory_stack) F,
      heap_WF (vir_heap m0) m0.2 F →
      heap_WF
      (vir_heap
        (add_to_frame
            (add_logical_block (next_logical_key m0) (make_empty_logical_block τ) m0)
            (next_logical_key m0))) (add_to_frame_stack m0.2 (next_logical_key m0)) F.
  Proof.
    intros. rewrite -vir_logical_frame_add_to_frame.
    rewrite -vir_heap_add_logical_block.
    apply heap_WF_extend_stable; eauto;
      last apply next_logical_key_None_heap.
  Qed.

  Lemma heap_WF_free_frame (m : memory) (f : frame_stack) (f0: mem_frame) F i:
    heap_WF (⊙ (m, Snoc f f0)) (Snoc f f0) (i :: F) ->
    heap_WF (⊙ (free_frame_memory f0 m, f)) f F.
  Proof.
    intros (REL & Hs & ? & ? & ?). constructor; repeat split; auto.
    { destruct f; cbn in *.
      - apply NoDup_app in REL. destruct REL as (?&?&?); eauto.
      - apply NoDup_app in REL. destruct REL as (?&?&?); eauto. }
    { cbn in Hs. rewrite /free_frame_memory.
      rewrite list_to_set_app_L in Hs. cbn.
      clear -REL Hs. revert m f Hs REL.
      induction f0; eauto; cbn in *.
      - intros; rewrite -Hs. set_solver.
      - intros; cbn in *.
        specialize (IHf0 (delete a m.1, m.2)).
        apply IHf0.
        { rewrite dom_delete_L.
          rewrite -Hs.
          do 2 rewrite difference_union_distr_l_L.
          rewrite difference_diag_L.
          rewrite union_empty_l_L.
          apply NoDup_cons in REL.
          destruct REL as (?&?). set_solver. }
        apply NoDup_cons in REL; destruct REL as (?&?); eauto. }

    { cbn in H; inversion H; subst; cbn in H0.
      destruct f; cbn in H3; rewrite H3; eauto. }

    intros; cbn in H1.
    destruct F; cbn.
    { cbn in H2; lia. }
    cbn in *. specialize (H1 (S n)); cbn in H1.
    apply H1. lia.
  Qed.

  Lemma heap_WF_free_frame_nil (m : memory) (f : frame_stack) (f0: mem_frame) :
    heap_WF (⊙ (m, Snoc f f0)) (Snoc f f0) [] ->
    heap_WF (⊙ (free_frame_memory f0 m, f)) f [].
  Proof.
    intros (? & REL & Hs & ?). cbn in *. inversion Hs.
  Qed.

  Lemma heap_WF_new_frame m mf j F:
    j.(index) = length F ->
    heap_WF (⊙ (m, mf)) mf F ->
    heap_WF (⊙ (m, Snoc mf [])) (Snoc mf []) (j :: F).
  Proof.
    intros Hfresh (?&?&?&?&?).
    rewrite /heap_WF.
    repeat split.
    { intros; rewrite /vir_heap.
      rewrite /vir_heap in H. cbn. auto. }
    { cbn. by rewrite -H0. }
    { cbn. by rewrite -H1. }
    { destruct H1. intros; eauto. cbn in *.
      destruct F; cbn in *; [lia | ].

      destruct n; cbn; subst; eauto.
      destruct n; cbn; subst; eauto.
      { specialize (H3 0%nat).
        assert ((0 < S (length F))%nat) by lia.
        specialize (H3 H4).
        cbn in H2. auto. }
      { rewrite -PeanoNat.Nat.succ_lt_mono in H1.
        specialize (H3 _ H1). auto. } }
  Qed.

  Lemma heap_WF_free_mem σ A F (l : Z):
    l ∉ (flatten_frame_stack A) ->
    heap_WF σ A F →
    heap_WF (base.delete l σ) A F.
  Proof.
    intros Hl (? & REL & Hf & ? & ?); cbn; repeat (split; auto).
    destruct A; cbn; eauto.
    { cbn in *. rewrite REL. set_solver. }
    { cbn in *. rewrite REL. set_solver. }
  Qed.

  Lemma heap_alloc l v m :
    m !! l = None ->
    own γ.(heap_name)(● to_heap m) ==∗
    own γ.(heap_name) (● (to_heap (<[ l := v ]> m)))
    ∗ l ↦ [ v ].
  Proof.
    intros Hin.
    rewrite mapsto_eq /mapsto_def.
    rewrite -own_op. rewrite to_heap_insert.
    apply bi.entails_wand, own_update, auth_update_alloc.
    apply lookup_to_heap_None in Hin.
    epose proof
      (alloc_local_update (to_heap m) _ _ _ Hin).
    by eapply H.
  Qed.

  Lemma heap_allocate m τ m' addr:
    allocate m τ = inr (m', addr) ->
    own γ.(heap_name)(● to_heap (vir_heap m)) ==∗
    own γ.(heap_name) (● to_heap (vir_heap m'))
      ∗ addr.1 ↦ [ make_empty_logical_block τ ].
  Proof.
    intros ALLOC.
    rewrite mapsto_eq /mapsto_def.
    rewrite -own_op. apply bi.entails_wand, own_update, auth_update_alloc.
    apply allocate_inv in ALLOC.
    destruct ALLOC as (Hnv & Halloc & Hv); subst; cbn.
    rewrite -vir_heap_insert.
    rewrite to_heap_insert.
    pose proof (next_logical_key_None_heap m).
    apply lookup_to_heap_None in H.

    epose proof
      (alloc_local_update (to_heap (vir_heap m))
            gmap_unit_instance (next_logical_key m) _ H).
    by eapply H0.
  Qed.

  Lemma frame_at_add_to_frame_stack k mf l:
    (frame_at (S k) (add_to_frame_stack mf l)) = frame_at (S k) mf.
  Proof.
    revert k. rewrite /frame_at; cbn.
    induction mf; eauto.
  Qed.

  Lemma frame_at_delete_from_frame_stack k mf l :
    (frame_at (S k) mf) =
    (frame_at (S k)  (delete_from_frame_stack mf l)).
  Proof.
    revert k.
    induction mf; cbn; eauto.
  Qed.

  Lemma heap_block_size_rel_none h hF l:
    heap_block_size_rel h hF ->
    l ∉ h.2 ->
    hF !! l = None.
  Proof.
    intros.
    destruct (hF !! l) eqn: HhF; auto.
    destruct H.
    specialize (H _ _ HhF); done.
  Qed.

  Lemma heap_block_size_rel_stable h hF u n k o:
    heap_block_size_rel (h, u) hF ->
    heap_block_size_rel (<[k := o]>h, {[k]} ∪ u) (<[k:= Some n]> hF).
  Proof.
    repeat intro. red in H. destruct H.
    split; intros.
    { destruct (decide (k = b)); subst.
      { rewrite lookup_insert in H1; inversion H1; subst.
        set_solver. }
      { rewrite lookup_insert_ne in H1; auto.
        specialize (H _ _ H1); set_solver. } }
    { destruct H1; cbn in H1.
      destruct (decide (k = b)); subst.
      { rewrite lookup_insert in H1; inversion H1; subst.
        rewrite lookup_insert.
        cbn in *.
        eauto. }
      { rewrite lookup_insert_ne in H1; auto.
        rewrite lookup_insert_ne; eauto. } }
  Qed.

  Lemma heap_ctx_alloc l v m i A_s mf G L LS τ:
    vir_heap m !! l = None ->
    l ∉ vir_dyn m ->
    dvalue_has_dtyp v τ ->
    allocaS γ (current_frame i) A_s ∗ stack γ i ∗
    heap_ctx γ (vir_heap m, vir_dyn m) mf G L LS ==∗
    heap_ctx γ (<[ l := dvalue_to_block v ]> (vir_heap m),
                {[l]} ∪ vir_dyn m) (add_to_frame_stack mf l) G L LS
      ∗ ⌜l ∉ A_s⌝
      ∗ allocaS γ (current_frame i) ({[l]} ∪ A_s)
      ∗ stack γ i
      ∗ l ↦ v
      ∗ block_size l 1 (Some (N.to_nat (sizeof_dtyp τ))).
  Proof.
    iIntros (ALLOC Hin Hτ) "(Ha & Hcf & H)".
    destruct_HC "H".
    iDestruct (heap_alloc _ _ _ ALLOC with "Hσ") as ">(Ho' & Ha')".

    rewrite allocaS_eq /allocaS_def.
    iDestruct (ghost_var_agree with "HCF Hcf") as %H; subst.
    iDestruct (ghost_var_agree with "HA Ha") as %H'; subst.
    iMod (ghost_var_update_halves ({[ l ]} ∪ (list_to_set (peek_frame mf)))
           with "HA Ha") as "[Ha1 Ha2]".

    pose proof (heap_block_size_rel_none _ _ _ Hbs Hin).

    iDestruct (ghost_map_insert with "Hb") as ">(Hi & Hb)"; eauto.

    iModIntro.
    rewrite heap_block_size_eq /heap_block_size_def; iFrame.
    rewrite mapsto_dval_eq /mapsto_dval_def; iFrame.

    iSplitR ""; cycle 1.
    { cbn.
      iPureIntro. destruct Hwf as (?&?&?).
      destruct mf; cbn in *.
      { rewrite app_nil_r in H1.
        apply not_elem_of_dom in ALLOC. set_solver. }
      { apply not_elem_of_dom in ALLOC. set_solver. } }

    cbn.
    iExists _,
      (<[l := Some (N.to_nat (sizeof_dtyp τ))]> hF); iFrame.
    iSplitL "Ha1".
    { rewrite add_to_frame_stack_peek_frame_commute.
      done. }

    iSplitR ""; cycle 1.
    { cbn.
      iSplit; iPureIntro; [ done | ].

      destruct m as ((?&?)&?); cbn in *.
      split; cycle 1.
      { cbn. apply heap_WF_extend_stable; eauto. }
      { destruct f; cbn; by apply heap_block_size_rel_stable. } }

    iApply big_sepL2_proper; [ | done ].
    intros.
    destruct mf; by try rewrite frame_at_add_to_frame_stack.
  Qed.

  Lemma heap_allocate_1 m τ m' addr mf G L LS i A_s:
    allocate m τ = inr (m', addr) ->
    allocaS γ (current_frame i) A_s ∗ stack γ i ∗
    heap_ctx γ (vir_heap m, vir_dyn m) mf G L LS ==∗
    heap_ctx γ (vir_heap m', vir_dyn m') (add_to_frame_stack mf addr.1) G L LS
      ∗ ⌜addr.1 ∉ A_s⌝
      ∗ allocaS γ (current_frame i) ({[addr.1]} ∪ A_s)
      ∗ stack γ i
      ∗ addr.1 ↦ [ make_empty_logical_block τ ]
      ∗ block_size addr.1 1 (Some (N.to_nat (sizeof_dtyp τ))).
  Proof.
    iIntros (ALLOC) "(Ha & Hcf & H)".
    destruct_HC "H".
    iDestruct (heap_allocate _ _ _ _ ALLOC with "Hσ") as ">(Ho' & Ha')".

    rewrite allocaS_eq /allocaS_def.
    iDestruct (ghost_var_agree with "HCF Hcf") as %H; subst.
    iDestruct (ghost_var_agree with "HA Ha") as %H'; subst.
    iMod (ghost_var_update_halves ({[ addr.1 ]} ∪ (list_to_set (peek_frame mf)))
           with "HA Ha") as "[Ha1 Ha2]".

    apply allocate_inv in ALLOC.
    destruct ALLOC as (Hnv & Halloc & Hv); subst.
    pose proof (next_logical_key_None_dyn m).
    pose proof (heap_block_size_rel_none _ _ _ Hbs H).

    iDestruct (ghost_map_insert with "Hb") as ">(Hi & Hb)"; eauto.

    iModIntro.
    rewrite heap_block_size_eq /heap_block_size_def; iFrame.

    iSplitR ""; cycle 1.
    { cbn.
      iPureIntro. destruct Hwf as (?&?&?).
      destruct mf; cbn in *.
      { pose proof (next_logical_key_None_heap m).
        apply not_elem_of_dom in H4. set_solver. }
      { pose proof (next_logical_key_None_heap m).
        apply not_elem_of_dom in H4. set_solver. } }

    cbn.
    iExists _, (<[(next_logical_key m):= Some (N.to_nat (sizeof_dtyp τ))]> hF); iFrame.
    iSplitL "Ha1".
    { rewrite add_to_frame_stack_peek_frame_commute.
      done. }

    iSplitR ""; cycle 1.
    { cbn.
      rewrite -vir_logical_frame_add_to_frame.
      rewrite -vir_heap_add_logical_block.
      iSplit; iPureIntro; [ done | ].

      destruct m as ((?&?)&?); cbn in *.
      split; cycle 1.
      { cbn. apply heap_WF_extend_stable; eauto.
        apply next_logical_key_None_heap. }
      { destruct f; cbn; by apply heap_block_size_rel_stable. } }

    iApply big_sepL2_proper; [ | done ].
    intros.
    destruct mf; by try rewrite frame_at_add_to_frame_stack.
  Qed.

  Lemma allocaS_push h g l AS v i mf L LS:
    h.1 !! l = None ->
    l ∉ h.2 ->
    heap_ctx γ h mf g L LS ∗ allocaS γ (current_frame i) AS ∗ stack γ i ==∗
    heap_ctx γ (<[ l := v ]> h.1, {[ l ]} ∪ h.2)
        (add_to_frame_stack mf l) g L LS∗
    l ↦ [ v ]
    ∗ allocaS γ (current_frame i) ({[l]} ∪ AS)
    ∗ stack γ i
    ∗ block_size l 1 (Some (logical_block_size v)).
  Proof.
    iIntros (Hin1 Hin2) "(H & Ha & Hcf)".
    destruct_HC "H".
    iDestruct (heap_alloc _ v _ Hin1 with "Hσ") as ">(Hσ & Hl)".

    rewrite allocaS_eq /allocaS_def.

    iDestruct (ghost_var_agree with "HCF Hcf") as %H; subst.

    iDestruct (ghost_var_agree with "HA Ha") as %H; subst.
    iMod (ghost_var_update_halves ({[l]} ∪ (list_to_set (peek_frame mf)))
           with "HA Ha") as "[Ha1 Ha2]".

    rewrite /heap_ctx; iFrame.

    rewrite add_to_frame_stack_peek_frame_commute.
    iMod (ghost_map_insert l (Some (logical_block_size v)) with "Hb") as
      "[Hb Hbs]".
    { eapply heap_block_size_rel_none; try set_solver. }
    iSplitR "Hbs"; [ | by rewrite heap_block_size_eq].

    iExists _, (<[l := Some (logical_block_size v)]> hF); iFrame.

    iSplitR ""; cycle 1.
    { iModIntro; iSplit; [ done | ] ;iPureIntro; split;
        [ by apply heap_block_size_rel_stable |
          by apply heap_WF_extend_stable ]. }

    iModIntro.
    iApply big_sepL2_proper; [ | done ].
    intros. by rewrite (frame_at_add_to_frame_stack k mf l).
  Qed.

  Lemma elem_of_delete_from_frame x f l:
    x ∈ delete_from_frame f l ->
    x ∈ f.
  Proof.
    revert x l.
    induction f; eauto.
    intros. cbn in H.

    rewrite elem_of_cons.
    destruct (Z.eq_dec l a); subst; try eauto.
    rewrite elem_of_cons in H. destruct H; eauto.
  Qed.

  Lemma not_elem_of_delete_from_frame f l a:
    a ∉ f ->
    a ∉ delete_from_frame f l.
  Proof.
    revert a l.
    induction f; eauto.
    intros. cbn.

    apply not_elem_of_cons in H. destruct H as (?&?).
    destruct (Z.eq_dec l a); subst; try eauto.
    set_solver.
  Qed.

  Lemma no_dup_delete_from_frame f l:
    NoDup f ->
    NoDup (delete_from_frame f l).
  Proof.
    revert l.
    induction f; cbn; eauto.
    intros.
    apply NoDup_cons in H.
    destruct H as (?&?);
      destruct (Z.eq_dec l a); subst; try eauto.
    apply NoDup_cons; split; eauto.
    by apply not_elem_of_delete_from_frame.
  Qed.

  Lemma heap_WF_delete σ A F (l : Z):
    l ∈ peek_frame A ->
    heap_WF σ A F →
    heap_WF (base.delete l σ) (delete_from_frame_stack A l) F.
  Proof.
    intros ? (? & REL & Hsize & ? & ?); repeat split; auto; cycle 1.
    { destruct A; cbn.
      - rewrite app_nil_r. cbn in REL. rewrite app_nil_r in REL.
        rewrite dom_delete_L. rewrite /delete_from_frame.
        rewrite -REL.
        by rewrite list_to_set_delete_from_frame.
      - cbn in REL.
        rewrite list_to_set_app_L in REL.
        rewrite list_to_set_app_L.
        rewrite dom_delete_L.
        rewrite list_to_set_delete_from_frame. rewrite -REL.
        rewrite difference_union_distr_l_L.
        f_equiv. cbn in H, H0.
        rewrite NoDup_app in H0. destruct H0 as (?&?&?).
        specialize (H3 _ H). set_solver. }
    { rewrite Hsize. rewrite /delete_from_frame_stack; destruct A; by cbn. }

    destruct A; cbn in H0; cbn; eauto.
    - rewrite app_nil_r. rewrite app_nil_r in H0.
      by apply no_dup_delete_from_frame.
    - rewrite NoDup_app. apply NoDup_app in H0. destruct H0 as (?&?&?).
      split.
      + by apply no_dup_delete_from_frame.
      + split; eauto.
        intros; eapply H3.
        by eapply elem_of_delete_from_frame.
  Qed.

  Lemma heap_block_size_rel_free h hF l:
    is_Some (h.1 !! l) ->
    heap_block_size_rel h hF ->
    heap_block_size_rel (delete l h.1, h.2) (<[l:=None]> hF).
  Proof.
    repeat intro.
    split; intros.
    { destruct (decide (l = b)); subst.
      { rewrite lookup_insert in H1; inversion H1; subst; cbn.
        destruct H0. specialize (H2 _ H). destruct H2.
        by specialize (H0 _ _ H2). }
      { destruct H0. rewrite lookup_insert_ne in H1; cbn; eauto. } }
    { cbn in *. destruct H0.
      destruct (decide (l = b)); subst.
      { rewrite lookup_delete in H1. by inversion H1. }
      { rewrite lookup_delete_ne in H1; eauto.
        rewrite lookup_insert_ne; eauto. } }
  Qed.

  Lemma heap_free1 h AS g l v i mf L S n:
    l ∈ AS ->
    ⊢ heap_ctx γ h mf g L S
      ∗ l ↦ [ v ]
      ∗ allocaS γ (current_frame i) AS
      ∗ stack γ i
      ∗ block_size l 1 n ==∗
      block_size l 1 None ∗
      heap_ctx γ (base.delete l h.1, h.2) (delete_from_frame_stack mf l) g L S ∗
      allocaS γ (current_frame i) (AS ∖ {[l]}) ∗ stack γ i.
  Proof.
    iIntros (Hin) "(H & Hl & Ha & Hcf & Hbs)".
    destruct_HC "H".
    rewrite allocaS_eq /allocaS_def.
    iDestruct (ghost_var_agree with "HCF Hcf") as %H; subst.
    iDestruct (ghost_var_agree with "HA Ha") as %H; subst.
    iMod (ghost_var_update_halves ((list_to_set (peek_frame mf))∖ {[ l]}) with "HA Ha") as "[Ha1 Ha2]".
    rewrite heap_block_size_eq /heap_block_size_def.
    iDestruct (ghost_map_update with "Hb Hbs") as ">(Hb & Hbs)".
    iCombine "Hσ Hl" as "H".
    iFrame.
    rewrite mapsto_eq /mapsto_def.
    rewrite -own_op.
    iExists _, (<[l := None]> hF).
    iSplitL "H".

    { iRevert "H".
      iApply own_update. apply auth_update_dealloc.
      rewrite to_heap_delete.
      etrans.
      { apply (delete_local_update _ _ l ((1%Qp, to_agree v)
                   : (prodR fracR (agreeR valO)))).
        by rewrite lookup_insert. }
      rewrite delete_insert; [ | done].
    rewrite -to_heap_delete. done. } iFrame.
    rewrite delete_from_frame_stack_peek_frame_commute; iFrame.

    iSplitR ""; cycle 1.
    { iModIntro; iSplit; [ done|]; iPureIntro; split;
      last apply heap_WF_delete; eauto; try set_solver.
      cbn. apply heap_block_size_rel_free; eauto.
      destruct Hwf as (?&?&?). clear -H0 Hin.
      apply elem_of_dom. destruct mf; set_solver. }

    iModIntro.
    iApply big_sepL2_proper; [ | done ].
    intros. by rewrite -frame_at_delete_from_frame_stack.
  Qed.

  Lemma heap_free h AS g l v i mf L S n:
    l ∈ AS ->
    ⊢ heap_ctx γ h mf g L S
      ∗ l ↦ v
      ∗ allocaS γ (current_frame i) AS
      ∗ stack γ i
      ∗ block_size l 1 n ==∗
      block_size l 1 None ∗
      heap_ctx γ (base.delete l h.1, h.2) (delete_from_frame_stack mf l) g L S ∗
      allocaS γ (current_frame i) (AS ∖ {[l]}) ∗ stack γ i.
  Proof.
    iIntros (Hin) "(H & Hl & Ha & Hcf & Hbs)".
    destruct_HC "H".
    rewrite allocaS_eq /allocaS_def.
    iDestruct (ghost_var_agree with "HCF Hcf") as %H; subst.
    iDestruct (ghost_var_agree with "HA Ha") as %H; subst.
    iMod (ghost_var_update_halves ((list_to_set (peek_frame mf))∖ {[ l]}) with "HA Ha") as "[Ha1 Ha2]".
    rewrite heap_block_size_eq /heap_block_size_def.
    iDestruct (ghost_map_update with "Hb Hbs") as ">(Hb & Hbs)".
    iCombine "Hσ Hl" as "H".
    iFrame.
    rewrite mapsto_dval_eq /mapsto_dval_def.
    rewrite mapsto_eq /mapsto_def.
    rewrite -own_op.
    iExists _, (<[l := None]> hF).
    iSplitL "H".

    { iRevert "H".
      iApply own_update. apply auth_update_dealloc.
      rewrite to_heap_delete.
      etrans.
      { apply (delete_local_update _ _ l ((1%Qp, to_agree (dvalue_to_block v))
                   : (prodR fracR (agreeR valO)))).
        by rewrite lookup_insert. }
      rewrite delete_insert; [ | done].
    rewrite -to_heap_delete. done. } iFrame.
    rewrite delete_from_frame_stack_peek_frame_commute; iFrame.

    iSplitR ""; cycle 1.
    { iModIntro; iSplit; [ done|]; iPureIntro; split;
      last apply heap_WF_delete; eauto; try set_solver.
      cbn. apply heap_block_size_rel_free; eauto.
      destruct Hwf as (?&?&?). clear -H0 Hin.
      apply elem_of_dom. destruct mf; set_solver. }

    iModIntro.
    iApply big_sepL2_proper; [ | done ].
    intros. by rewrite -frame_at_delete_from_frame_stack.
  Qed.

  Lemma can_free_frame F' m mf g L S:
    (1 < length F')%nat ->
    stack γ F' -∗
    heap_ctx γ (⊙ (m, mf), vir_dyn (m, mf)) mf g L S -∗
    ∃ m', ⌜free_frame (m, mf) = inr m'⌝.
  Proof.
    iIntros (Hsize) "Hf Hc".
    destruct_HC "Hc".
    rewrite /free_frame.

    iDestruct (ghost_var_agree with "HCF Hf") as %H; subst.

    destruct mf eqn: H; [ | iExists _; by cbn]; exfalso.
    destruct Hwf as (?&?&?&?). cbn in H1. inversion H1.
    subst. rewrite app_nil_r in H5.
    rewrite H2 in Hsize. cbn in Hsize.
    lia.
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

  Lemma fold_left_delete_comm {K} `{!EqDecision K} `{!Countable K}
    `{Countable K} (f : list K) a {A} (m : gmap K A):
    fold_left (fun m key => base.delete key m) f (base.delete a m) =
    base.delete a (fold_left (fun m key => base.delete key m) f m).
  Proof.
    revert a m.
    induction f; cbn; auto.
    intros.
    setoid_rewrite delete_commute. by rewrite IHf.
  Qed.

  Lemma foldl_delete_comm {K} `{!EqDecision K} `{!Countable K}
    `{Countable K} (f : list K) a {A} (m : gmap K A):
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

  Axiom leibniz_heap : LeibnizEquiv heapUR.

  Lemma big_opM_fold_left_delete_domain
    (d : list loc) (m : heap) :
    NoDup d ->
    dom m ≡ list_to_set d ->
    fold_left (fun m k => base.delete k m) d
      ([^op map] k↦x ∈ m, ({[k := (1%Qp, to_agree x)]} : heapUR))
      ≡ ε.
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
          (fun k x => {[ k := (1%Qp, to_agree x)]} : heapUR) _ i x H) as H'.
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
    Unshelve. apply leibniz_heap.
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

  Lemma heap_block_size_rel_free_frame h hF f:
    heap_block_size_rel h hF ->
    heap_block_size_rel
      (fold_left (λ (m0 : logical_memory) (key : Z), delete key m0) f h.1, h.2)
      hF.
  Proof.
    repeat intro.
    split; destruct H; intros; cbn.
    { by eapply H. }
    { cbn in *.
      destruct H1.
      apply H0.
      apply fold_left_delete_some in H1; auto. }
  Qed.

  Lemma free_frame i (m m' : memory) (mf mf': frame_stack) g AS FA L S :
    (1 < length i)%nat ->
    free_frame (m, mf) = inr (m', mf') ->
      stack γ i
      ∗ heap_ctx γ (⊙ (m, mf), vir_dyn (m, mf)) mf g L S
      ∗ allocaS γ (current_frame i) AS
      ∗ ⌜dom FA ≡ AS⌝
      ∗ ([∗ map] l ↦ v ∈ FA,
          l ↦ [ v ] ∗ block_size l 1 (Some (logical_block_size v)))
      ==∗
    heap_ctx γ (⊙ (m', mf'), vir_dyn (m', mf'))
    mf' g (List.hd L S) (List.tl S) ∗
      let F' := List.tl i in
      stack γ F'.
  Proof.
    iIntros (Hlen Hf) "(HFr & Hσ & Ha & %Hdom & Hm)".
    rewrite /free_frame in Hf.
    destruct mf; inversion Hf; subst; cbn -[frame_at].
    destruct_HC "Hσ".

    (* Update allocaS set *)
    rewrite allocaS_eq /allocaS_def.

    iDestruct (ghost_var_agree with "HFr HCF") as %H'; subst.
    iDestruct (ghost_var_agree with "HA Ha") as %H'; subst.

    pose proof (Hwf' := Hwf).
    destruct Hwf. cbn in H0. inversion H0; clear H0. clear Hf.

    iMod (ghost_var_update_halves (tail cf) with "HFr HCF") as "[HFr HF]".
    iFrame.

    destruct cf. { cbn in Hlen; lia. }
    destruct cf. { cbn in Hlen; lia. }

    iPoseProof (big_sepL2_cons_inv_l with "HSA") as (???) "(HC & HS)";
      subst.
    iDestruct "HC" as "(HC_L&HC_D&%HC_WF&HC_La&HC_M)".

    iExists (f1 :: cf), hF.
    iDestruct (big_sepM_sep with "Hm") as "(Hm & Hbs)".
    iFrame.

    iSplitL "Hσ Hm".
    { destruct f.
      { (* There was nothing allocated in the new frame *)
        destruct m; cbn; by rewrite /vir_heap. }

      { (* Something was allocated! Let's free 'em *)
        rewrite mapsto_eq /mapsto_def.
        iPoseProof (big_opM_own with "Hm") as "H".
        { (* Allocated set is non-empty *)
          intro; subst. rewrite dom_empty in Hdom.
          symmetry in Hdom. cbn in Hdom.
          set_solver. }

        rewrite -big_opM_auth_frag.
        iCombine "Hσ H" as "H".

        iRevert "H". iApply own_update.
        eapply auth_update_dealloc.
        rewrite to_heap_fold_delete.
        cbn in Hdom.

        remember ([^ op map] k↦x ∈ FA, {[k := (1%Qp, to_agree x)]}).

        Typeclasses eauto := 5.
        rewrite <- big_opM_fold_left_delete_domain; cycle 1.
        { apply NoDup_cons in H. destruct H as (?&?).
          apply NoDup_app in H0. destruct H0 as (?&?).
          Unshelve. 3 : exact (z :: f). 2 : shelve.
          rewrite NoDup_cons; split; eauto.
          apply not_elem_of_app in H. destruct H; eauto. }
        { setoid_rewrite Hdom; by cbn. }
        subst.
        apply delete_fold_local_update.
        { cbn in H.
          apply NoDup_cons in H. destruct H as (?&?).
          apply NoDup_app in H0. destruct H0 as (?&?).
          apply NoDup_cons; split; auto. set_solver. }

        { intros. cbn in Hdom.
          clear -H Hdom H0.
          cbn in H.
          apply NoDup_cons in H. destruct H as (?&?).
          apply NoDup_app in H1. destruct H1 as (?&?).
          apply not_elem_of_app in H. destruct H as (?&_).
          clear H2.
          revert z FA i Hdom H0 H H1.
          induction f; intros; cbn in *.
          - rewrite union_empty_r in Hdom.
            apply dom_singleton_inv in Hdom.
            destruct Hdom as (?&?).
            rewrite H2. exists (1%Qp, to_agree x); split; cycle 1.
            { apply pair_exclusive_l. apply frac_full_exclusive. }

            rewrite big_op.big_opM_unseal.
            rewrite /big_op.big_opM_def.
            rewrite map_to_list_singleton. cbn.
            rewrite lookup_op. rewrite lookup_empty.
            rewrite op_None_right_id.
            repeat red.
            match goal with
              | |- option_Forall2 equiv ?l _ => destruct l eqn: Hl
            end; try constructor.
            + rewrite lookup_singleton_Some in Hl.
              destruct Hl; by subst.
            + rewrite lookup_singleton_None in Hl.
              set_solver.
          - apply NoDup_cons in H1. destruct H1 as (?&?).
            destruct (decide (i = z)); subst; cycle 1.
            { apply elem_of_cons in H0. destruct H0; try done.
              specialize (IHf a (delete z FA)).
              assert (dom (delete z FA) ≡ {[ a ]} ∪ list_to_set f).
              { rewrite dom_delete. rewrite Hdom.
                do 2 rewrite difference_union_distr_l.
                rewrite difference_diag.
                rewrite union_empty_l.
                rewrite difference_disjoint_L; last set_solver.
                by rewrite difference_disjoint_L; last set_solver. }
              specialize (IHf _ H3 H0 H1 H2).
              destruct IHf as (?&?&?). exists x; split; auto.
              rewrite -H4.
              assert (z <> i) by eauto.
              epose proof (big_opM_delete_singleton_lookup
                       _ FA (fun y => (1%Qp, to_agree y))  z i H6).
              repeat red in H7. inversion H7; cycle 1.
              { by rewrite -H9 -H10. }
              { try rewrite -H8 -H9; eauto. f_equiv. done. } }
            { apply elem_of_cons in H0. destruct H0; try done.
              specialize (IHf z (delete a FA)).
              assert (dom (delete a FA) ≡ {[ z ]} ∪ list_to_set f).
              { rewrite dom_delete. rewrite Hdom.
                do 2 rewrite difference_union_distr_l.
                rewrite difference_diag.
                rewrite union_empty_l.
                rewrite difference_disjoint_L; last set_solver.
                by rewrite difference_disjoint_L; last set_solver. }
              specialize (IHf z H3).
              assert (z ∈ z :: f) by set_solver.
              assert (z ∉ f) by set_solver.
              specialize (IHf H4 H5 H2).
              destruct IHf as (?&?&?). exists x; split; auto.
              rewrite -H6.

              apply not_elem_of_cons in H. destruct H.
              assert (a <> z) by eauto.
              pose proof (big_opM_delete_singleton_lookup
                       _ FA (fun y => (1%Qp, to_agree y))  a z H9).
              repeat red in H10. inversion H10; cycle 1.
              { by rewrite -H12 -H13. }
              { try rewrite -H11 -H12; eauto. f_equiv. done. } } } } }

    iPureIntro.

    cbn.
    split; [done | ]; split; cbn; eauto;
    last eapply heap_WF_free_frame; eauto.
    by eapply heap_block_size_rel_free_frame.
  Qed.

  Lemma allocaS_new_frame i m mf g L LS LN:
    NoDup LN.*1 ->
    heap_ctx γ (⊙ (m, mf), m.2) mf g L LS
      ∗ stack γ i ==∗
    ∃ j, heap_ctx γ (⊙ (m, (Snoc mf [])), m.2) (Snoc mf []) g LN (L :: LS)
      ∗ stack γ (j :: i)
      ∗ allocaS γ j ∅
      ∗ ldomain γ j (list_to_set LN.*1)
      ∗ ([∗ list] '(l,v) ∈ LN, lmapsto γ j l v).
  Proof.
    iIntros (Hnodup) "(HC & Hf)".
    destruct_HC "HC".

    rewrite allocaS_eq /allocaS_def.

    iDestruct (ghost_var_agree with "Hf HCF") as %H; subst.

    iMod (ghost_map_alloc (list_to_map LN)) as (j) "Hlj".

    iMod (ghost_var_alloc ∅) as (γallocaS) "Hv".
    iMod (ghost_var_alloc (list_to_set LN.*1)) as (γldomain) "Hv'".
    set (γnew :=
        {| index := length cf;
         local_name := j;
         ldomain_name := γldomain;
         allocaS_name := γallocaS
        |}).
    iExists γnew.

    iMod (ghost_var_update_halves (γnew :: cf) with "HCF Hf") as "[Hf1 Hf2]".

    rewrite -{9 10}Qp.half_half.
    iDestruct (ghost_var_split with "Hv") as "[Hd1 Hd2]".
    iDestruct (ghost_var_split with "Hv'") as "[Hld1 Hld2]".

    iFrame.

    iDestruct "Hlj" as "(Hlj1 & Hlj2)".
    iSplitR "Hlj2 Hld1"; cycle 1.
    { rewrite lmapsto_eq /lmapsto_def. clear -Hnodup.
      Typeclasses eauto :=.
      rewrite big_opM_map_to_list.
      rewrite map_to_list_to_map; eauto.
      iFrame.
      iApply (big_sepL_mono with "Hlj2"); intros.
      by destruct y. }

    iExists (γnew :: cf), hF. iFrame.

    cbn -[peek_frame frame_at].
    destruct cf.
    { cbn. destruct LS; eauto. cbn.
      destruct Hwf as (?&?&?). cbn in H1; lia. }

    rewrite big_sepL2_cons; iFrame.

    iModIntro.
    iPureIntro.
    repeat (split; first done).
    by eapply heap_WF_new_frame.
  Qed.

  (* Read *)
  Lemma heap_read_st_1 h l q v mf g L LS:
    heap_ctx γ h mf g L LS -∗
    l ↦{q} [ v ] -∗
    ⌜h.1 !! l = Some v⌝.
  Proof.
    iIntros "Hσ"; destruct_HC "Hσ"; iIntros "Hmt".
    by iPoseProof (mapsto_lookup_byte with "Hσ Hmt") as "h".
  Qed.

  Lemma heap_read h l q v g mf L LS:
    heap_ctx γ h mf g L LS -∗
    l ↦{q} v -∗
    ⌜h.1 !! l = Some (dvalue_to_block v)⌝.
  Proof.
    iIntros "Hσ"; destruct_HC "Hσ"; iIntros "Hmt".
    by iPoseProof (mapsto_lookup with "Hσ Hmt") as "h".
  Qed.

  Lemma heap_write_vs h l v v' :
    h !! l = Some v →
    own γ.(heap_name) (● to_heap h) -∗ l ↦ [ v ]
    ==∗ own γ.(heap_name) (● to_heap (<[l:=v']> h))
        ∗ l ↦ [ v' ].
  Proof.
    rewrite mapsto_eq /mapsto_def.
    intros Hσv.
    apply bi.entails_wand, wand_intro_r. rewrite -!own_op to_heap_insert.
    eapply own_update, auth_update, singleton_local_update.
    { by rewrite /to_heap lookup_fmap Hσv. }
    eapply exclusive_local_update. done.
  Qed.

  Lemma heap_block_size_rel_stable1 h hF u k o:
    is_Some (h !! k) ->
    heap_block_size_rel (h, u) hF ->
    heap_block_size_rel (<[k := o]>h, u) (hF).
  Proof.
    repeat intro. red in H. destruct H.
    split; intros.
    { cbn. destruct H0. cbn in H0.
      eapply H0; eauto. }
    { cbn in *. destruct H0; cbn in *.
      apply H2.
      destruct (decide (k = b)); subst.
      { rewrite lookup_insert in H1; inversion H1; subst.
        eauto. }
      { rewrite lookup_insert_ne in H1; auto. } }
  Qed.

  Lemma heap_write h g l v v' mf L LS :
    heap_ctx γ h mf g L LS -∗
    l ↦ [ v ] ==∗
    heap_ctx γ (<[l :=v']> h.1, h.2) mf g L LS ∗ l ↦ [ v' ].
  Proof.
    intros.
    iIntros "Hσ Hmt".
    iDestruct (heap_read_st_1 with "Hσ Hmt") as %?; auto.
    destruct_HC "Hσ".
    iMod (heap_write_vs with "Hσ Hmt") as "[Hσ $]"; first done.
    iModIntro. unfold heap_ctx.
    iExists _, hF;
    repeat iFrame; iSplit;
      eauto 8 using heap_WF_stable, heap_block_size_rel_stable1.
  Qed.

  Lemma heap_write1 h g l v v' mf L LS :
    heap_ctx γ h mf g L LS -∗
    l ↦ [ v ] ==∗
    heap_ctx γ (<[l :=v']> h.1, {[ l ]} ∪ h.2) mf g L LS ∗ l ↦ [ v' ].
  Proof.
    intros.
    iIntros "Hσ Hmt".
    iDestruct (heap_read_st_1 with "Hσ Hmt") as %?; auto.
    destruct_HC "Hσ".
    iMod (heap_write_vs with "Hσ Hmt") as "[Hσ $]"; first done.

    assert ({[ l ]} ∪ h.2 = h.2).
    { destruct Hbs. cbn in *.
      cbn in *.
      assert (l ∈ h.2).
      { specialize (H1 l (ltac:(eauto))).
        destruct H1.
        eapply H0; eauto. }
      set_solver. }
    rewrite H0.

    iModIntro. unfold heap_ctx.
    iExists _, hF;
    repeat iFrame; iSplit;
      eauto 8 using heap_WF_stable, heap_block_size_rel_stable1.
  Qed.

  Lemma heap_write_dval h mf g l v v' L LS:
    heap_ctx γ h mf g L LS -∗ l ↦ v ==∗
    heap_ctx γ (<[ l := dvalue_to_block v' ]> h.1, h.2) mf g L LS ∗ l ↦ v'.
  Proof.
    intros.
    iIntros "Hσ Hmt".
    iDestruct (heap_read with "Hσ Hmt") as %?; auto.
    destruct_HC "Hσ".
    rewrite mapsto_dval_eq /mapsto_dval_def.

    iMod (heap_write_vs with "Hσ Hmt") as "[Hσ $]"; first done.
    iModIntro. unfold heap_ctx.
    repeat iExists _; repeat iFrame;
      eauto 8 using heap_WF_stable, heap_block_size_rel_stable1.
  Qed.

  Lemma heap_ctx_alloca_agree i A h mf g L LS:
    stack γ i -∗
    allocaS γ (current_frame i) A -∗
    heap_ctx γ h mf g L LS -∗
    ⌜list_to_set (peek_frame mf) = A⌝.
  Proof.
    iIntros "Hs Ha HC".
    destruct_HC "HC".
    rewrite allocaS_eq /allocaS_def.
    rewrite /stack.
    iDestruct (ghost_var_agree with "Hs HCF") as %Hcf; subst.
    iDestruct (ghost_var_agree with "Ha HA") as %HA.
    done.
  Qed.

  Lemma heap_ctx_block_size h b mf g L LS n:
    is_Some (h.1 !! b) ->
    heap_ctx γ h mf g L LS -∗
    block_size b 1 n -∗
    ⌜is_Some n⌝.
  Proof.
    iIntros (Hh) "HC Hbs".
    destruct_HC "HC".
    destruct Hbs.
    specialize (H0 _ Hh).
    destruct H0.
    rewrite heap_block_size_eq /heap_block_size_def.
    iDestruct (ghost_map_lookup with "Hb Hbs") as %Hb.
    rewrite H0 in Hb; inversion Hb; eauto.
  Qed.

End heap.

Lemma heap_init `{heapG Σ} (gs : global_env):
  ⊢ |==> ∃ (γ : heap_names) (γf : frame_names),
      heap_ctx γ (gmap_empty, gset_empty) (Singleton []) gs [] [] ∗
      own γ.(heap_name) (◯ to_heap gmap_empty) ∗
      ([∗ map] k↦v ∈ gmap_empty, k ↪[γ.(heap_block_size_name)] v) ∗
      own (globals_name γ)
        (to_agree (gs) : agreeR (leibnizO global_env)) ∗
      ghost_var γ.(stack_name) (1 / 2) [γf] ∗
      ([∗ map] k↦v ∈ gmap_empty, k ↪[γf.(local_name)] v) ∗
      ghost_var γf.(ldomain_name) (1 / 2) (gset_empty : gset local_loc) ∗
      ghost_var γf.(allocaS_name) (1 / 2) (gset_empty : gset Z).
Proof.
  iMod (own_alloc (● (to_heap gmap_empty) ⋅ ◯ (to_heap gmap_empty))) as (γheap) "[Hheap Hfrag]".
  { apply auth_both_valid_discrete. split; first done. apply to_heap_valid. }

  iMod (ghost_map_alloc (gmap_empty : gmap loc (option nat)))
    as (γblocksize) "(Hblock_auth & Hblock)".
  iMod (ghost_var_alloc (gset_empty : gset Z))
    as (γalloca) "Halloca".
  iMod (own_alloc (to_agree (gs : leibnizO _))) as (γg) "Hg" => //.
  iMod (ghost_map_alloc (gmap_empty : gmap local_loc local_val))
    as (γlocal) "(Hlocal_auth & Hlocal)".
  iMod (ghost_var_alloc (gset_empty : gset local_loc))
    as (γdomain) "Hdomain".
  iMod (ghost_var_alloc ([[]]: lstack)) as (γlstack) "Hlstack".

  set (fn :=
         {| index := 0;
            local_name := γlocal;
            ldomain_name := γdomain;
            allocaS_name := γalloca |}:
         frame_names).

  iMod (ghost_var_alloc [fn]) as (γstack) "Hstack".
  rewrite -{4 7 8 9}Qp.half_half.

  iDestruct (ghost_var_split
               (ghost_varG0 := heapGS_stackG) with "Hstack")
    as "[Hstack1 Hstack2]".
  iDestruct (ghost_var_split
               (ghost_varG0 := lheapG_stackG) with "Hlstack")
    as "[Hlstack1 Hlstack2]".
  iDestruct (ghost_var_split
               (ghost_varG0 := heapGS_allocaSG) with "Halloca")
    as "[Halloca1 Halloca2]".
  iDestruct (ghost_var_split
               (ghost_varG0 := lheapG_domain) with "Hdomain")
    as "[Hdom1 Hdom2]".

  iExists {| heap_name := γheap;
             heap_block_size_name := γblocksize;
             globals_name := γg;
             stack_name := γstack; |}.
  iModIntro. rewrite /heap_ctx globals_eq /=.

  iPoseProof "Hg" as "#Hg".

  iExists fn. iFrame. cbn; iFrame.
  iSplitR "Hblock"; cycle 1.
  { iSplitL "Hblock"; done. }
  iExists [fn], gmap_empty; repeat iFrame.
  cbn.
  iSplitL "".
  { iPureIntro; set_solver. }
  iFrame "Hg".
  iSplitL "".
  { iPureIntro; by apply NoDup_nil. }
  iSplitL "".
  { iPureIntro; repeat intro.
    split; intros; inversion H0; try done. }
  iPureIntro; cbn.
  rewrite /heap_WF.
  split; repeat intro; try inversion H0; eauto; try set_solver.
  { cbn; by apply NoDup_nil. }
  cbn. try (repeat split; eauto).
  intros. destruct n; eauto. lia.
Qed.

