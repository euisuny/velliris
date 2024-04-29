From velliris.utils Require Export tactics.
From velliris.vir Require Export vir vir_state tactics vir_util.
From velliris.program_logic Require Import program_logic.

From iris.algebra.lib Require Import gset_bij.
From iris.bi Require Import fixpoint.
From iris.prelude Require Import options.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gset_bij.

From Vellvm Require Import Syntax.DynamicTypes Handlers.Handlers Utils.Util.

Set Default Proof Using "Type*".

Class heapbijGS (Σ : gFunctors) := HeapBijGS {
  heapbijG_bijG :> gset_bijG Σ loc loc;
  heapbijG_bij_name : gname;
}.
Class heapbijGpreS (Σ: gFunctors) := HeapBijGpreS {
  sbij_pre_progG :> gset_bijG Σ loc loc;
}.
Definition heapbijΣ := #[gset_bijΣ loc loc].
Global Instance subG_heapbijΣ Σ :
  subG heapbijΣ Σ → heapbijGpreS Σ.
Proof. solve_inG. Qed.

Section definitions.
  Context `{heapbijGS Σ}.

  Definition heapbij_auth (L : gset (loc * loc)) :=
    gset_bij_own_auth heapbijG_bij_name (DfracOwn 1) L.
  Definition block_rel (l_t : loc) (l_s : loc) :=
    gset_bij_own_elem heapbijG_bij_name l_t l_s.
End definitions.

Definition loc_rel `{heapbijGS Σ} (l_t l_s : loc * loc) : iProp Σ :=
  block_rel l_t.1 l_s.1 ∗ ⌜l_t.2 = l_s.2⌝.
Notation "l_t '↔h' l_s" := (loc_rel l_t l_s) (at level 30) : bi_scope.

Section laws.
  Context `{!heapbijGS Σ}.
  Implicit Types (b_t b_s : loc) (l_t l_s : loc * loc).

  Lemma heapbij_agree b_t1 b_t2 b_s1 b_s2 :
    block_rel b_t1 b_s1 -∗ block_rel b_t2 b_s2 -∗ ⌜b_t1 = b_t2 ↔ b_s1 = b_s2⌝.
  Proof.
    iIntros "H1 H2". iApply (gset_bij_own_elem_agree with "H1 H2").
  Qed.

  Lemma heapbij_loc_agree l_t1 l_t2 l_s1 l_s2 :
    l_t1 ↔h l_s1 -∗ l_t2 ↔h l_s2 -∗ ⌜l_t1 = l_t2 ↔ l_s1 = l_s2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct "H1" as "(H1&%H1)".
    iDestruct "H2" as "(H2&%H2)".
    iPoseProof (heapbij_agree with "H1 H2") as "%Ha".
    destruct l_t1, l_s1, l_t2, l_s2; cbn in *; subst. iPureIntro; naive_solver.
  Qed.

  Lemma heapbij_func b_t b_s1 b_s2 :
    block_rel b_t b_s1 -∗ block_rel b_t b_s2 -∗ ⌜b_s1 = b_s2⌝.
  Proof.
    iIntros "H1 H2". iPoseProof (heapbij_agree with "H1 H2") as "<-"; done.
  Qed.

  Lemma heapbij_loc_func l_t l_s1 l_s2 :
    l_t ↔h l_s1 -∗ l_t ↔h l_s2 -∗ ⌜l_s1 = l_s2⌝.
  Proof.
    iIntros "H1 H2". iPoseProof (heapbij_loc_agree with "H1 H2") as "<-"; done.
  Qed.

  Lemma heapbij_inj b_s b_t1 b_t2 :
    block_rel b_t1 b_s -∗ block_rel b_t2 b_s -∗ ⌜b_t1 = b_t2⌝.
  Proof.
    iIntros "H1 H2". iPoseProof (heapbij_agree with "H1 H2") as "->"; done.
  Qed.
  Lemma heapbij_loc_inj l_s l_t1 l_t2 :
    l_t1 ↔h l_s -∗ l_t2 ↔h l_s -∗ ⌜l_t1 = l_t2⌝.
  Proof.
    iIntros "H1 H2". iPoseProof (heapbij_loc_agree with "H1 H2") as "->"; done.
  Qed.

End laws.

Definition determine_uvalue (v : uvalue) (dv : dvalue) : Prop :=
  if is_concrete v
  then uvalue_to_dvalue v = inr dv
  else concretize_uvalue v = Monad.ret dv.

(* General util lemmas *)
Lemma map_repeat_Some {A B} sz d k x (f : A -> B):
  map f (repeat d sz) !! k = Some x ->
  x = f d.
Proof.
  revert d k x.
  induction sz; cbn; eauto; intros; inversion H.
  rewrite lookup_cons in H.
  destruct k; inversion H; eauto.
Qed.

Lemma repeat_Some {A} sz d k (x :A ):
  repeat d sz !! k = Some x ->
  x = d.
Proof.
  revert d k x.
  induction sz; cbn; eauto; intros; inversion H.
  rewrite lookup_cons in H.
  destruct k; inversion H; eauto.
Qed.

(** **Value relation
  The value relation characterizes related values defined in terms of ghost
  state. *)
Section val_rel_definitions.

  Context {Σ : gFunctors} `{HB: heapbijGS Σ}.

  Definition val_rel (v1 v2 : SByte): iProp Σ :=
    (match v1, v2 with
     | Byte b1, Byte b2 => ⌜b1 = b2⌝
     | Ptr a1, Ptr a2 => loc_rel a1 a2
     | PtrFrag, PtrFrag => True
     | SUndef, SUndef => True
     | _, _ => False
     end)%I.

  Definition Forall2 {Σ A} (R: A -> A -> iProp Σ) (l1 l2 : list A) : (iProp Σ) :=
    ([∗ list] k↦y1;y2 ∈ l1;l2, R y1 y2).

  (* Refinement relation for concrete uvalues, where poison/undef values refine
    every uvalue, and otherwise serialized values are related under the value relation *)
  Definition dval_relF (dval_rel : dvalue -d> dvalue -d> iPropI Σ) : dvalue -d> dvalue -d> iPropI Σ :=
    fun v_t v_s  =>
      (match v_t, v_s with
      | DVALUE_Addr a1, DVALUE_Addr a2 => a1 ↔h a2
      | DVALUE_I1 v1, DVALUE_I1 v2
      | DVALUE_I8 v1, DVALUE_I8 v2
      | DVALUE_I32 v1, DVALUE_I32 v2
      | DVALUE_I64 v1, DVALUE_I64 v2
      | DVALUE_Float v1, DVALUE_Float v2
      | DVALUE_Double v1, DVALUE_Double v2 => ⌜v1 = v2⌝
      | DVALUE_Struct l1, DVALUE_Struct l2
      | DVALUE_Array l1, DVALUE_Array l2 =>
          Forall2 dval_rel l1 l2
      | DVALUE_None, DVALUE_None
      | DVALUE_Poison, DVALUE_Poison => True
      | _, _ => False
      end)%I.

  Canonical Structure dvalueO := leibnizO dvalue.

  Definition dval_rel : dvalue -d> dvalue -d> iPropI Σ :=
    curry (bi_least_fixpoint
      (fun (least_rec: (prodO dvalueO dvalueO) -d> iPropI Σ) =>
         uncurry (dval_relF (curry least_rec)))).

  Definition uval_rel (v_t v_s : uvalue) : iPropI Σ :=
    (∀ dv, ⌜concretize_uvalue v_s = Monad.ret dv⌝ -∗
      ∃ dv', ⌜concretize_uvalue v_t = Monad.ret dv'⌝ ∗ dval_rel dv' dv ).

  (* Relating results on the hole. *)
  Definition logrel_post : expr vir_lang uvalue → expr vir_lang uvalue → iPropI Σ :=
    lift_post uval_rel.

  Fixpoint val_rel_prop (v1 v2 : SByte) : Prop :=
    (match v1, v2 with
      | Byte b1, Byte b2 => b1 = b2
      (* Pointer and pointer fragments are not observable *)
      | Ptr a1, Ptr a2 => True
      | PtrFrag, PtrFrag => True
      | SUndef, SUndef => True
      | _, _ => False
      end).

  (* Relation between uvalues where the details of locations are not observable *)
  Definition obs_val (v_t v_s : uvalue) : Prop :=
    (∀ dv, concretize_uvalue v_s = Monad.ret dv ->
     forall dv', concretize_uvalue v_t = Monad.ret dv' ->
      List.Forall2 val_rel_prop (serialize_dvalue dv') (serialize_dvalue dv)).

  (* Relating results on the closed context. *)
  Definition obs_val_res {X}: X * uvalue -> X * uvalue -> Prop :=
    fun '(_, x) '(_, y) => obs_val x y.

End val_rel_definitions.

Section val_rel_properties.

  Context {Σ : gFunctors} `{HB: heapbijGS Σ}.

  #[local] Instance dvalue_func_ne (F : dvalue -d> dvalue -d> iPropI Σ) `{Hne : !NonExpansive F}:
    (forall n, Proper (dist n ==> dist n ==> dist n) F).
  Proof.
    intros n Φ Φ' HΦ e_t e_t' ->%discrete_iff%leibniz_equiv ; [|apply _..].
    eapply Hne, HΦ.
  Qed.

  Ltac dval_rel_ind_mono_listcase e1 e2 :=
    destruct e1, e2; try done;
    iDestruct "H" as "[Hl Hr]"; iSplitL "Hl"; by iApply "HF".

  Lemma big_sepL2_mono_pred :
    ∀ (PROP: bi) (A B : Type) (Φ Ψ : A → B → PROP) (l1 : list A) (l2 : list B),
    ⊢ □ (∀ y1 y2, Φ y1 y2 -∗ Ψ y1 y2) -∗
      ([∗ list] k ↦ y1;y2 ∈ l1;l2, Φ y1 y2) -∗ [∗ list] k ↦ y1;y2 ∈ l1;l2, Ψ y1 y2.
  Proof.
    intros H. setoid_rewrite big_sepL2_alt.
    iIntros (??????) "#H".
    iIntros "(%H' & H')"; subst.
    iSplit; [ done | ].
    remember (zip l1 l2).
    clear Heql.
    iInduction l as [] "IH"; [ done | ].
    cbn in *.
    iDestruct "H'" as "(HΦ & H')".
    iSplitL "HΦ"; [ iApply ("H" with "HΦ") | ].
    iApply ("IH" with "H'").
  Qed.

  (* monotonicity of dval_rel_ind *)
  Lemma dval_relF_mono (l1 l2 : dvalue -d> dvalue -d> iPropI Σ):
    ⊢ □ (∀ e_t e_s, l1 e_t e_s -∗ l2 e_t e_s)
    → ∀ e_t e_s, dval_relF l1 e_t e_s -∗ dval_relF l2 e_t e_s.
  Proof.
    iIntros "#HF" (e_t e_s) "H".
    rewrite /dval_relF.
    destruct e_s eqn: He_s; eauto.
    all: destruct e_t; cbn; eauto;
      by iApply big_sepL2_mono_pred.
  Qed.

  #[local] Instance dval_relF_ne :
    forall n,
      Proper ((dist n ==> dist n ==> dist n) ==>
        dist n ==> dist n ==> dist n) dval_relF.
  Proof.
    intros n L1 L2 HL e_s e_s' ->%discrete_iff%leibniz_equiv e_t e_t'
      ->%discrete_iff%leibniz_equiv; [ | eapply _..].
    rewrite /dval_relF /Forall2.
    all : repeat (f_equiv || eapply HL || reflexivity).
  Qed.

  #[local] Instance dval_relF_proper :
    Proper ((base.equiv ==> base.equiv ==> base.equiv) ==>
            base.equiv ==> base.equiv ==> base.equiv) dval_relF.
  Proof.
    intros L1 L2 HL e_s e_s' ->%leibniz_equiv e_t e_t' ->%leibniz_equiv;
      [ | eapply _..].
    rewrite /dval_relF /Forall2.
    all : repeat (f_equiv || eapply HL || reflexivity).
  Qed.

  #[global] Instance dval_rel_ne :
    NonExpansive2 dval_rel.
  Proof.
    rewrite /dval_rel; intros n x y Heq ???.
    rewrite {1 3}/curry.
    apply least_fixpoint_ne; last by repeat split.
    intros ? [? ?]; simpl.
    rewrite /dval_relF /Forall2.
    all : repeat (f_equiv || eapply HL || reflexivity).
  Qed.

  #[global] Instance dval_rel_proper :
    Proper (eq ==> eq ==> (≡)) dval_rel.
  Proof.
    intros e e' -> e1 e1' ->.
    done.
  Qed.

  #[local] Instance dval_rel_body_mono:
    BiMonoPred
      (fun (least_rec : (prodO dvalueO dvalueO) -d> iPropI Σ) =>
         uncurry (dval_relF (curry least_rec))).
  Proof.
    constructor.
    - intros L1 L2 HL1. iIntros (Hg) "#H %x Hl".
      destruct x as (e_t & e_s); simpl.
      iApply (dval_relF_mono with "[] [Hl]"); [ | done].
      iModIntro. clear. unfold curry, Datatypes.curry.
      iIntros (e_t e_s) "HL". by iApply "H".
    - intros Φ Hne n x y Heq.
      destruct x as (e_t & e_s); simpl.
      destruct y as (e_t' & e_s'); simpl.
      destruct Heq as [Heq1 Heq2]; simpl in Heq1, Heq2.
      eapply dval_relF_ne; eauto.
      intros ??????; unfold curry, Datatypes.curry.
      by eapply Hne.
  Qed.

  Lemma dval_rel_strong_ind (F : dvalue -d> dvalue -d> iPropI Σ):
    NonExpansive F ->
    ⊢ (□ ∀ e_t e_s,
           dval_relF (fun e_t e_s => F e_t e_s ∧ dval_rel e_t e_s)%I e_t e_s -∗ F e_t e_s)
      -∗ ∀ e_t e_s, dval_rel e_t e_s -∗ F e_t e_s.
  Proof.
    iIntros (Hprop) "#HPre". iIntros (e_t e_s) "HF".
    rewrite {2}/dval_rel /curry /Datatypes.curry.
    change (F e_t e_s) with (uncurry F (e_t, e_s)).
    remember (e_t, e_s) as p eqn:Heqp. rewrite -Heqp.
    clear e_t e_s Heqp.
    iApply (least_fixpoint_ind _ (uncurry F) with "[] HF").
    iModIntro. iIntros ([e_t e_s]) "Hf"; simpl.
    iApply ("HPre" $! e_t e_s with "Hf").
  Qed.

  Lemma dval_rel_ind (F : dvalue -d> dvalue -d> iPropI Σ):
    NonExpansive F ->
    ⊢ (□ ∀ e_t e_s, dval_relF F e_t e_s -∗ F e_t e_s)
      -∗ ∀ e_t e_s, dval_rel e_t e_s -∗ F e_t e_s.
  Proof.
    iIntros (Hne) "#HPre". iApply dval_rel_strong_ind.
    iModIntro. iIntros (e_t e_s) "Hsim".
    iApply "HPre".
    iApply dval_relF_mono; [ | done].
    iModIntro. iIntros (e_t' e_s') "H". iApply bi.and_elim_l. iApply "H".
  Qed.

  Lemma dval_rel_unfold e_t e_s :
    dval_rel e_t e_s ≡ dval_relF dval_rel e_t e_s.
  Proof.
    intros; rewrite {1}/dval_rel {1}/curry.
    setoid_rewrite least_fixpoint_unfold ; [ | typeclasses eauto].
    rewrite {1}/uncurry //=.
  Qed.

  Lemma unfold_dval_rel e_t e_s :
    dval_rel e_t e_s ⊣⊢
      (match e_t, e_s with
      | DVALUE_Addr a1, DVALUE_Addr a2 => a1 ↔h a2
      | DVALUE_I1 v1, DVALUE_I1 v2
      | DVALUE_I8 v1, DVALUE_I8 v2
      | DVALUE_I32 v1, DVALUE_I32 v2
      | DVALUE_I64 v1, DVALUE_I64 v2
      | DVALUE_Float v1, DVALUE_Float v2
      | DVALUE_Double v1, DVALUE_Double v2 => ⌜v1 = v2⌝
      | DVALUE_Struct l1, DVALUE_Struct l2
      | DVALUE_Array l1, DVALUE_Array l2 =>
          Forall2 dval_rel l1 l2
      | DVALUE_None, DVALUE_None
      | DVALUE_Poison , DVALUE_Poison => True
      | _, _ => False
      end)%I.
  Proof.
  rewrite dval_rel_unfold /dval_relF //.
  Qed.

  Lemma dval_rel_array l_t l_s:
    Forall2 dval_rel l_t l_s -∗
    dval_rel (DVALUE_Array l_t) (DVALUE_Array l_s).
  Proof.
    iIntros "Hl".
    by setoid_rewrite unfold_dval_rel.
  Qed.

  Lemma dval_rel_array_cons v_t v_s l_t l_s:
    dval_rel v_t v_s -∗
    dval_rel (DVALUE_Array l_t) (DVALUE_Array l_s) -∗
    dval_rel (DVALUE_Array (v_t :: l_t)) (DVALUE_Array (v_s :: l_s)).
  Proof.
    iIntros "Hl H".
    setoid_rewrite unfold_dval_rel at 2 3; cbn.
    iFrame.
  Qed.

  Lemma dval_rel_struct l_t l_s:
    Forall2 dval_rel l_t l_s -∗
    dval_rel (DVALUE_Struct l_t) (DVALUE_Struct l_s).
  Proof.
    iIntros "Hl".
    by setoid_rewrite unfold_dval_rel.
  Qed.

  Lemma dval_rel_struct_cons v_t v_s l_t l_s:
    dval_rel v_t v_s -∗
    dval_rel (DVALUE_Struct l_t) (DVALUE_Struct l_s) -∗
    dval_rel (DVALUE_Struct (v_t :: l_t)) (DVALUE_Struct (v_s :: l_s)).
  Proof.
    iIntros "Hv Hl".
    setoid_rewrite unfold_dval_rel at 2 3; iFrame.
  Qed.

  Lemma dval_rel_none :
    ⊢ dval_rel DVALUE_None DVALUE_None.
  Proof.
    by rewrite dval_rel_unfold /dval_relF.
  Qed.

  Lemma dval_rel_I32 i :
    ⊢ dval_rel (DVALUE_I32 i) (DVALUE_I32 i).
  Proof.
    rewrite dval_rel_unfold; iStartProof; done.
  Qed.

  Lemma dval_rel_addr i i':
    i ↔h i' -∗
    dval_rel (DVALUE_Addr i) (DVALUE_Addr i').
  Proof.
    rewrite dval_rel_unfold /dval_relF.
    by iIntros "H".
  Qed.

  Lemma dval_rel_addr' ptr' ptr:
    dval_rel (DVALUE_Addr ptr') (DVALUE_Addr ptr) -∗
    ptr' ↔h ptr.
  Proof.
    rewrite unfold_dval_rel; cbn; eauto.
  Qed.

  Lemma addr_bij ptr ptr':
    val_rel.Forall2 val_rel.val_rel
      (serialize_dvalue (DVALUE_Addr ptr'))
      (serialize_dvalue (DVALUE_Addr ptr)) -∗
    ptr' ↔h ptr.
  Proof.
    by iIntros "(H&_)".
  Qed.

  Lemma val_rel_defined v_t v_s:
    val_rel v_t v_s -∗
    ⌜Sbyte_defined v_s = Sbyte_defined v_t⌝.
  Proof.
    iIntros "Hv".
    rewrite /val_rel.
    destruct v_s, v_t; try done.
  Qed.

  Lemma val_rel_byte_inv_r v i:
    val_rel v (Byte i) -∗
    ⌜v = Byte i⌝.
  Proof.
    rewrite /val_rel.
    destruct v; iIntros "%H"; subst; done.
  Qed.

  Lemma val_rel_ptr_inv_r v i:
    val_rel v (Ptr i) -∗
    ∃ i', ⌜v = Ptr i'⌝ ∗ loc_rel i' i.
  Proof.
    rewrite /val_rel.
    destruct v; iIntros "H"; try done.
    iExists _; iSplitL ""; done.
  Qed.

  Lemma val_rel_ptrfrag_inv_r v :
    val_rel v PtrFrag -∗
    ⌜v = PtrFrag⌝.
  Proof.
    rewrite /val_rel.
    destruct v; iIntros "%H"; subst; done.
  Qed.

  Lemma val_rel_sundef_inv_r v :
    val_rel v SUndef -∗
    ⌜v = SUndef⌝.
  Proof.
    rewrite /val_rel.
    destruct v; iIntros "%H"; subst; done.
  Qed.


  Lemma loc_uval_rel l_t o_t l_s o_s:
    (l_t, o_t) ↔h (l_s, o_s) ⊣⊢
      uval_rel (UVALUE_Addr (l_t, o_t)) (UVALUE_Addr (l_s, o_s)).
  Proof.
    iSplit; iIntros "H"; rewrite /uval_rel.
    { iIntros.
      cbn in H. inversion H; subst.
      iExists _; iSplitL ""; first done.
      by iApply dval_rel_addr. }
    { cbn.
      iSpecialize ("H" $! _ eq_refl).
      iDestruct "H" as (?) "(%H & Hv)".
      inv H.
      by iApply dval_rel_addr'. }
  Qed.

  Lemma dval_rel_I1_inv :
    forall dv i, dval_rel dv (DVALUE_I1 i) -∗
    ⌜dv = DVALUE_I1 i⌝.
  Proof.
    iIntros (dv i) "H".
    cbn -[serialize_dvalue];
      rewrite dval_rel_unfold /dval_relF.
    destruct dv; iDestruct "H" as %H; subst; eauto.
  Qed.

  Lemma dval_rel_I1_inv' :
    forall dv i, dval_rel (DVALUE_I1 i) dv -∗
    ⌜dv = DVALUE_I1 i⌝.
  Proof.
    iIntros (dv i) "H".
    cbn -[serialize_dvalue];
      rewrite dval_rel_unfold /dval_relF.
    destruct dv; iDestruct "H" as %H; subst; eauto.
  Qed.

  Lemma dval_rel_I8_inv :
    forall dv i, dval_rel dv (DVALUE_I8 i) -∗
    ⌜dv = DVALUE_I8 i⌝.
  Proof.
    iIntros (dv i) "H".
    cbn -[serialize_dvalue];
      rewrite dval_rel_unfold /dval_relF.
    destruct dv; iDestruct "H" as %H; subst; eauto.
  Qed.

  Lemma dval_rel_I8_inv' :
    forall dv i, dval_rel (DVALUE_I8 i) dv -∗
    ⌜dv = DVALUE_I8 i⌝.
  Proof.
    iIntros (dv i) "H".
    cbn -[serialize_dvalue];
      rewrite dval_rel_unfold /dval_relF.
    destruct dv; iDestruct "H" as %H; subst; eauto.
  Qed.

  Lemma dval_rel_I32_inv :
    forall dv i, dval_rel dv (DVALUE_I32 i) -∗
    ⌜dv = DVALUE_I32 i⌝.
  Proof.
    iIntros (dv i) "H".
    cbn -[serialize_dvalue];
      rewrite dval_rel_unfold /dval_relF.
    destruct dv; iDestruct "H" as %H; subst; eauto.
  Qed.

  Lemma dval_rel_I32_inv' :
    forall dv i, dval_rel (DVALUE_I32 i) dv -∗
    ⌜dv = DVALUE_I32 i⌝.
  Proof.
    iIntros (dv i) "H".
    cbn -[serialize_dvalue];
      rewrite dval_rel_unfold /dval_relF.
    destruct dv; iDestruct "H" as %H; subst; eauto.
  Qed.

  Lemma dval_rel_I64_inv :
    forall dv i, dval_rel dv (DVALUE_I64 i) -∗
    ⌜dv = DVALUE_I64 i⌝.
  Proof.
    iIntros (dv i) "H".
    cbn -[serialize_dvalue];
      rewrite dval_rel_unfold /dval_relF.
    destruct dv; iDestruct "H" as %H; subst; eauto.
  Qed.

  Lemma dval_rel_I64_inv' :
    forall dv i, dval_rel (DVALUE_I64 i) dv -∗
    ⌜dv = DVALUE_I64 i⌝.
  Proof.
    iIntros (dv i) "H".
    cbn -[serialize_dvalue];
      rewrite dval_rel_unfold /dval_relF.
    destruct dv; iDestruct "H" as %H; subst; eauto.
  Qed.

  Lemma dval_rel_poison_inv :
    forall dv, dval_rel dv DVALUE_Poison -∗
    ⌜dv = DVALUE_Poison⌝.
  Proof.
    iIntros (dv) "H".
    cbn -[serialize_dvalue];
      rewrite dval_rel_unfold /dval_relF.
    destruct dv; eauto.
  Qed.

  Lemma dval_rel_poison_inv' :
    forall dv, dval_rel DVALUE_Poison dv -∗
    ⌜dv = DVALUE_Poison⌝.
  Proof.
    iIntros (dv) "H".
    cbn -[serialize_dvalue];
      rewrite dval_rel_unfold /dval_relF.
    destruct dv; eauto.
  Qed.

  Lemma dval_rel_poison_neg_inv :
    forall dv dv', dval_rel dv dv' -∗
    ⌜dv' <> DVALUE_Poison -> dv <> DVALUE_Poison⌝.
  Proof.
    iIntros (dv dv') "H".
    cbn -[serialize_dvalue];
      rewrite dval_rel_unfold /dval_relF.
    destruct dv; destruct dv'; eauto.
  Qed.

  Lemma dval_rel_addr_inv :
    forall dv ptr, dval_rel dv (DVALUE_Addr ptr) -∗
    ∃ ptr', ⌜dv = DVALUE_Addr ptr'⌝.
  Proof.
    iIntros (dv i) "H".
    cbn -[serialize_dvalue];
      rewrite dval_rel_unfold /dval_relF.
    destruct dv; eauto.
  Qed.

  Lemma dval_rel_addr_inv' :
    forall dv ptr, dval_rel (DVALUE_Addr ptr) dv -∗
    ∃ ptr', ⌜dv = DVALUE_Addr ptr'⌝.
  Proof.
    iIntros (dv i) "H".
    cbn -[serialize_dvalue];
      rewrite dval_rel_unfold /dval_relF.
    destruct dv; eauto.
  Qed.

  Lemma dval_rel_double_inv :
    forall dv d, dval_rel dv (DVALUE_Double d) -∗
     ⌜dv = DVALUE_Double d⌝.
  Proof.
    iIntros (dv i) "H".
    cbn -[serialize_dvalue];
      rewrite dval_rel_unfold /dval_relF.
    destruct dv; iDestruct "H" as %H; subst; eauto.
  Qed.

  Lemma dval_rel_double_inv' :
    forall dv d, dval_rel (DVALUE_Double d) dv -∗
     ⌜dv = DVALUE_Double d⌝.
  Proof.
    iIntros (dv i) "H".
    cbn -[serialize_dvalue];
      rewrite dval_rel_unfold /dval_relF.
    destruct dv; iDestruct "H" as %H; subst; eauto.
  Qed.

  Lemma dval_rel_float_inv :
    forall dv f, dval_rel dv (DVALUE_Float f) -∗
    ⌜dv = DVALUE_Float f⌝.
  Proof.
    iIntros (dv i) "H".
    cbn -[serialize_dvalue];
      rewrite dval_rel_unfold /dval_relF.
    destruct dv; iDestruct "H" as %H; subst; eauto.
  Qed.

  Lemma dval_rel_float_inv' :
    forall dv f, dval_rel (DVALUE_Float f) dv -∗
    ⌜dv = DVALUE_Float f⌝.
  Proof.
    iIntros (dv i) "H".
    cbn -[serialize_dvalue];
      rewrite dval_rel_unfold /dval_relF.
    destruct dv; iDestruct "H" as %H; subst; eauto.
  Qed.

  Lemma dval_rel_None_inv dv :
    dval_rel dv DVALUE_None -∗
    ⌜dv = DVALUE_None⌝.
  Proof.
    iIntros "H".
    cbn -[serialize_dvalue];
      rewrite dval_rel_unfold /dval_relF.
    destruct dv; iDestruct "H" as %H; subst; eauto.
  Qed.

  Lemma dval_rel_None_inv' dv :
    dval_rel DVALUE_None dv -∗
    ⌜dv = DVALUE_None⌝.
  Proof.
    iIntros "H".
    cbn -[serialize_dvalue];
      rewrite dval_rel_unfold /dval_relF.
    destruct dv; iDestruct "H" as %H; subst; eauto.
  Qed.

  Lemma dval_rel_array_inv dv l:
    dval_rel dv (DVALUE_Array l) -∗
    ∃ l', ⌜dv = DVALUE_Array l'⌝.
  Proof.
    rewrite unfold_dval_rel.
    iIntros "H"; destruct dv; eauto.
  Qed.

  Lemma dval_rel_array_inv' dv l:
    dval_rel (DVALUE_Array l) dv -∗
    ∃ l', ⌜dv = DVALUE_Array l'⌝.
  Proof.
    rewrite unfold_dval_rel.
    iIntros "H"; destruct dv; eauto.
  Qed.

  Lemma dval_rel_array_cons_inv d xs0 a xs:
    dval_rel (DVALUE_Array (d :: xs0)) (DVALUE_Array (a :: xs)) -∗
    dval_rel (DVALUE_Array xs0) (DVALUE_Array xs) ∗
    dval_rel d a.
  Proof.
    rewrite (unfold_dval_rel (DVALUE_Array (d :: xs0)));
      cbn; iIntros "(?&H)"; iFrame.
    rewrite unfold_dval_rel; cbn; iFrame.
  Qed.

  Lemma dval_rel_struct_inv dv l:
    dval_rel dv (DVALUE_Struct l) -∗
    ∃ l', ⌜dv = DVALUE_Struct l'⌝.
  Proof.
    rewrite unfold_dval_rel.
    iIntros "H"; destruct dv; eauto.
  Qed.

  Lemma dval_rel_struct_inv' dv l:
    dval_rel (DVALUE_Struct l) dv -∗
    ∃ l', ⌜dv = DVALUE_Struct l'⌝.
  Proof.
    rewrite unfold_dval_rel.
    iIntros "H"; destruct dv; eauto.
  Qed.

  Lemma dval_rel_struct_cons_inv d xs0 a xs:
    dval_rel (DVALUE_Struct (d :: xs0)) (DVALUE_Struct (a :: xs)) -∗
    dval_rel (DVALUE_Struct xs0) (DVALUE_Struct xs) ∗
    dval_rel d a.
  Proof.
    rewrite (unfold_dval_rel (DVALUE_Struct (d :: xs0))).
      cbn; iIntros "(?&H)"; iFrame.
    rewrite unfold_dval_rel; cbn; iFrame.
  Qed.

  Lemma monad_fold_right_cons {m} `{Monad.Monad m}
    {A B} (f : B -> A -> m B) (l:list A) (b : B) a:
    monad_fold_right f (a :: l) b =
      Monad.bind (monad_fold_right f l b) (fun x => f x a).
  Proof.
    revert f b a.
    induction l; eauto; cbn; eauto.
  Qed.

  Lemma eval_int_op_dval_rel_I1
    op (x x0 : DynamicValues.Int1.int) dv:
    ⌜eval_int_op op x x0 = inr dv⌝ -∗
    dval_rel dv dv.
  Proof.
    iIntros (H).
    rewrite /eval_int_op in H.
    destruct op.
    all : try solve
      [inversion H; destruct_if; rewrite unfold_dval_rel; eauto;
       iPureIntro; constructor].
  Qed.

  Lemma eval_int_op_dval_rel_I8
    op (x x0 : DynamicValues.Int8.int) dv:
    ⌜eval_int_op op x x0 = inr dv⌝ -∗
    dval_rel dv dv.
  Proof.
    iIntros (H).
    rewrite /eval_int_op in H.
    destruct op.
    all : try solve
      [inversion H; destruct_if; rewrite unfold_dval_rel; eauto;
       iPureIntro; constructor].
  Qed.

  Lemma eval_int_op_dval_rel_I32
    op (x x0 : DynamicValues.Int32.int) dv:
    ⌜eval_int_op op x x0 = inr dv⌝ -∗
    dval_rel dv dv.
  Proof.
    iIntros (H).
    rewrite /eval_int_op in H.
    destruct op.
    all : try solve
      [inversion H; destruct_if; rewrite unfold_dval_rel; eauto;
       iPureIntro; constructor].
  Qed.

  Lemma eval_int_op_dval_rel_I64
    op (x x0 : DynamicValues.Int64.int) dv:
    ⌜eval_int_op op x x0 = inr dv⌝ -∗
    dval_rel dv dv.
  Proof.
    iIntros (H).
    rewrite /eval_int_op in H.
    destruct op.
    all : try solve
      [inversion H; destruct_if; rewrite unfold_dval_rel; eauto;
       iPureIntro; constructor].
  Qed.

  Lemma uval_rel_binop op v1 v2 v1' v2':
    uval_rel v1' v1 -∗
    uval_rel v2' v2 -∗
    uval_rel (UVALUE_IBinop op v1' v2') (UVALUE_IBinop op v1 v2).
  Proof.
    rewrite /uval_rel.
    iIntros "H1 H2"; iIntros (??); inversion H; destruct_match.
    destruct (concretize_uvalue v1) eqn: Hv1;
      destruct unEitherT, s; inversion H0; subst; clear H0.
    destruct (concretize_uvalue v2) eqn: Hv2;
      destruct unEitherT, s; inversion H2; subst; clear H2.
    iSpecialize ("H1" $! _ eq_refl).
    iSpecialize ("H2" $! _ eq_refl).
    iDestruct "H1" as (??) "H1"; iDestruct "H2" as (??) "H2".
    cbn. rewrite H0 H2; cbn.
    destruct (eval_iop op d d0) eqn: Hop;
      destruct unEitherT, s; inversion H1; clear H1; subst.
    clear H3 H5 H6 H8.
    destruct dv; subst.
    { rewrite /eval_iop in Hop; destruct_match.
      rewrite /eval_iop_integer_h in Hop; destruct_match.
      all: rewrite /eval_int_op in H1; destruct_match; inversion H1. }
    { rewrite /eval_iop in Hop; destruct_match.
      rewrite /eval_iop_integer_h in Hop; destruct_match.

      { iDestruct (dval_rel_I1_inv with "H1") as %Hi.
        iDestruct (dval_rel_I1_inv with "H2") as %Hi'; subst.
        cbn. rewrite H1; eauto.
        iExists _; iSplitL ""; [ done | ].

        by rewrite (unfold_dval_rel (DVALUE_I1 x)). }

      { iDestruct (dval_rel_I8_inv with "H1") as %Hi.
        iDestruct (dval_rel_I8_inv with "H2") as %Hi'; subst.
        cbn. rewrite H1; eauto.
        iExists _; iSplitL ""; [ done | ].

        by rewrite (unfold_dval_rel (DVALUE_I1 x)). }

      { iDestruct (dval_rel_I32_inv with "H1") as %Hi.
        iDestruct (dval_rel_I32_inv with "H2") as %Hi'; subst.
        cbn. rewrite H1; eauto.
        iExists _; iSplitL ""; [ done | ].

        by rewrite (unfold_dval_rel (DVALUE_I1 x)). }

      { iDestruct (dval_rel_I64_inv with "H1") as %Hi.
        iDestruct (dval_rel_I64_inv with "H2") as %Hi'; subst.
        cbn. rewrite H1; eauto.
        iExists _; iSplitL ""; [ done | ].

        by rewrite (unfold_dval_rel (DVALUE_I1 x)). } }

    { rewrite /eval_iop in Hop; destruct_match.
      rewrite /eval_iop_integer_h in Hop; destruct_match.

      { iDestruct (dval_rel_I1_inv with "H1") as %Hi.
        iDestruct (dval_rel_I1_inv with "H2") as %Hi'; subst.
        cbn. rewrite H1; eauto.
        iExists _; iSplitL ""; [ done | ].

        by rewrite (unfold_dval_rel (DVALUE_I8 x)). }

      { iDestruct (dval_rel_I8_inv with "H1") as %Hi.
        iDestruct (dval_rel_I8_inv with "H2") as %Hi'; subst.
        cbn. rewrite H1; eauto.
        iExists _; iSplitL ""; [ done | ].

        by rewrite (unfold_dval_rel (DVALUE_I8 x)). }

      { iDestruct (dval_rel_I32_inv with "H1") as %Hi.
        iDestruct (dval_rel_I32_inv with "H2") as %Hi'; subst.
        cbn. rewrite H1; eauto.
        iExists _; iSplitL ""; [ done | ].

        by rewrite (unfold_dval_rel (DVALUE_I8 x)). }

      { iDestruct (dval_rel_I64_inv with "H1") as %Hi.
        iDestruct (dval_rel_I64_inv with "H2") as %Hi'; subst.
        cbn. rewrite H1; eauto.
        iExists _; iSplitL ""; [ done | ].

        by rewrite (unfold_dval_rel (DVALUE_I8 x)). } }

    { rewrite /eval_iop in Hop; destruct_match.
      rewrite /eval_iop_integer_h in Hop; destruct_match.

      { iDestruct (dval_rel_I1_inv with "H1") as %Hi.
        iDestruct (dval_rel_I1_inv with "H2") as %Hi'; subst.
        cbn. rewrite H1; eauto.
        iExists _; iSplitL ""; [ done | ].

        by rewrite (unfold_dval_rel (DVALUE_I32 x)). }

      { iDestruct (dval_rel_I8_inv with "H1") as %Hi.
        iDestruct (dval_rel_I8_inv with "H2") as %Hi'; subst.
        cbn. rewrite H1; eauto.
        iExists _; iSplitL ""; [ done | ].

        by rewrite (unfold_dval_rel (DVALUE_I32 x)). }

      { iDestruct (dval_rel_I32_inv with "H1") as %Hi.
        iDestruct (dval_rel_I32_inv with "H2") as %Hi'; subst.
        cbn. rewrite H1; eauto.
        iExists _; iSplitL ""; [ done | ].

        by rewrite (unfold_dval_rel (DVALUE_I32 x)). }

      { iDestruct (dval_rel_I64_inv with "H1") as %Hi.
        iDestruct (dval_rel_I64_inv with "H2") as %Hi'; subst.
        cbn. rewrite H1; eauto.
        iExists _; iSplitL ""; [ done | ].

        by rewrite (unfold_dval_rel (DVALUE_I32 x)). } }

    { rewrite /eval_iop in Hop; destruct_match.
      rewrite /eval_iop_integer_h in Hop; destruct_match.

      { iDestruct (dval_rel_I1_inv with "H1") as %Hi.
        iDestruct (dval_rel_I1_inv with "H2") as %Hi'; subst.
        cbn. rewrite H1; eauto.
        iExists _; iSplitL ""; [ done | ].

        by rewrite (unfold_dval_rel (DVALUE_I64 x)). }

      { iDestruct (dval_rel_I8_inv with "H1") as %Hi.
        iDestruct (dval_rel_I8_inv with "H2") as %Hi'; subst.
        cbn. rewrite H1; eauto.
        iExists _; iSplitL ""; [ done | ].

        by rewrite (unfold_dval_rel (DVALUE_I64 x)). }

      { iDestruct (dval_rel_I32_inv with "H1") as %Hi.
        iDestruct (dval_rel_I32_inv with "H2") as %Hi'; subst.
        cbn. rewrite H1; eauto.
        iExists _; iSplitL ""; [ done | ].

        by rewrite (unfold_dval_rel (DVALUE_I64 x)). }

      { iDestruct (dval_rel_I64_inv with "H1") as %Hi.
        iDestruct (dval_rel_I64_inv with "H2") as %Hi'; subst.
        cbn. rewrite H1; eauto.
        iExists _; iSplitL ""; [ done | ].

        by rewrite (unfold_dval_rel (DVALUE_I64 x)). } }

    all: try solve [clear -Hop; rewrite /eval_iop in Hop;
          destruct_match;
          rewrite /eval_iop_integer_h in Hop; destruct_match;
          try rewrite /eval_int_op in H; destruct_match].

    {  rewrite /eval_iop in Hop;
        destruct_match;
        rewrite /eval_iop_integer_h in Hop; destruct_match.
       all:
          try iDestruct (dval_rel_I1_inv with "H1") as %Hi;
          try iDestruct (dval_rel_I1_inv with "H2") as %Hi';
          try iDestruct (dval_rel_I8_inv with "H1") as %Hi;
          try iDestruct (dval_rel_I8_inv with "H2") as %Hi';
          try iDestruct (dval_rel_I16_inv with "H1") as %Hi;
          try iDestruct (dval_rel_I16_inv with "H2") as %Hi';
          try iDestruct (dval_rel_I32_inv with "H1") as %Hi;
          try iDestruct (dval_rel_I32_inv with "H2") as %Hi';
          try iDestruct (dval_rel_I64_inv with "H1") as %Hi;
          try iDestruct (dval_rel_I64_inv with "H2") as %Hi';
          try iDestruct (dval_rel_poison_inv with "H1") as %Hi;
          try iDestruct (dval_rel_poison_inv with "H2") as %Hi';
         subst; cbn; try rewrite H1.
       all: try (iExists _; iSplitL ""; [ done | ];
                   by rewrite (unfold_dval_rel DVALUE_Poison)). }
  Qed.

  Lemma eval_int_icmp_dval_rel_I1 cmp (x x0 : DynamicValues.int1) dv:
    ⌜eval_int_icmp cmp x x0 = dv⌝ -∗
    dval_rel dv dv.
  Proof.
    iIntros (H).
    rewrite /eval_int_icmp in H.
    destruct cmp.
    all : try solve
      [inversion H; destruct_if; by rewrite unfold_dval_rel].
  Qed.

  Lemma eval_int_icmp_dval_rel_I8 cmp (x x0 : DynamicValues.int8) dv:
    ⌜eval_int_icmp cmp x x0 = dv⌝ -∗
    dval_rel dv dv.
  Proof.
    iIntros (H).
    rewrite /eval_int_icmp in H.
    destruct cmp.
    all : try solve
      [inversion H; destruct_if; by rewrite unfold_dval_rel].
  Qed.

  Lemma eval_int_icmp_dval_rel_I32 cmp (x x0 : DynamicValues.int32) dv:
    ⌜eval_int_icmp cmp x x0 = dv⌝ -∗
    dval_rel dv dv.
  Proof.
    iIntros (H).
    rewrite /eval_int_icmp in H.
    destruct cmp.
    all : try solve
      [inversion H; destruct_if; by rewrite unfold_dval_rel].
  Qed.

  Lemma eval_int_icmp_dval_rel_I64 cmp (x x0 : DynamicValues.int64) dv:
    ⌜eval_int_icmp cmp x x0 = dv⌝ -∗
    dval_rel dv dv.
  Proof.
    iIntros (H).
    rewrite /eval_int_icmp in H.
    destruct cmp.
    all : try solve
      [inversion H; destruct_if; by rewrite unfold_dval_rel].
  Qed.

  Lemma uval_rel_icmp cmp v1 v2 v1' v2':
    uval_rel v1' v1 -∗
    uval_rel v2' v2 -∗
    uval_rel (UVALUE_ICmp cmp v1' v2') (UVALUE_ICmp cmp v1 v2).
  Proof.
    rewrite /uval_rel.
    iIntros "H1 H2"; iIntros (??); inversion H; destruct_match.
    destruct (concretize_uvalue v1) eqn: Hv1;
      destruct unEitherT, s; inversion H0; subst; clear H0.
    destruct (concretize_uvalue v2) eqn: Hv2;
      destruct unEitherT, s; inversion H2; subst; clear H2.
    iSpecialize ("H1" $! _ eq_refl).
    iSpecialize ("H2" $! _ eq_refl).
    iDestruct "H1" as (??) "H1"; iDestruct "H2" as (??) "H2".
    cbn. rewrite H0 H2; cbn.
    destruct (eval_icmp cmp d d0) eqn: Hop;
      destruct unEitherT, s; inversion H1; clear H1; subst.
    clear H3 H5 H6 H8.

    destruct dv; subst.
    all: try solve [rewrite /eval_icmp in Hop; cbn in Hop;
      destruct_match; rewrite /eval_int_icmp in H5; destruct_if].

    { (* Int *)
      rewrite /eval_icmp in Hop; cbn in Hop;
        destruct_match; rewrite /eval_int_icmp in H5.
      1-4: try
        (iDestruct (dval_rel_addr_inv with "H1") as (?) "%Hi";
        iDestruct (dval_rel_addr_inv with "H2") as (?) "%Hi'";
          subst; rewrite !unfold_dval_rel).

      (* Addr eq *)
      1,3: iDestruct (heapbij_loc_inj with "H1 H2") as %Heq; subst;
        destruct (Addr.eq_dec ptr'0 ptr'0) eqn: Hptr; [ | done];
        cbn; rewrite Hptr; iExists _; iSplitL ""; [ done | ];
        by rewrite unfold_dval_rel.

      (* Addr neq *)
      { iDestruct (heapbij_loc_agree with "H1 H2") as %Heq; subst.

        destruct Heq.
        assert (ptr' <> ptr'0).
        { intro; apply n; eauto. }

        destruct (Addr.eq_dec ptr' ptr'0) eqn: Hptr; [ done | ].
        cbn. rewrite Hptr. iExists _; iSplitL ""; [ done | ].
        by rewrite unfold_dval_rel. }

      { iDestruct (heapbij_loc_agree with "H1 H2") as %Heq; subst.

        destruct Heq.
        assert (ptr' <> ptr'0).
        { intro; apply n; eauto. }

        destruct (Addr.eq_dec ptr' ptr'0) eqn: Hptr; [ done | ].
        cbn. rewrite Hptr. iExists _; iSplitL ""; [ done | ].
        by rewrite unfold_dval_rel. }

      { (* I1 *)
        iDestruct (dval_rel_I1_inv with "H1") as %Hi.
        iDestruct (dval_rel_I1_inv with "H2") as %Hi'; subst.

        cbn.
        inversion Hop; cbn.
        rewrite H3.
        iExists (DVALUE_I1 x); iSplitL ""; [ done | ].
        by iApply eval_int_icmp_dval_rel_I1. }

      { (* I8 *)
        iDestruct (dval_rel_I8_inv with "H1") as %Hi.
        iDestruct (dval_rel_I8_inv with "H2") as %Hi'; subst.

        cbn.
        inversion Hop; cbn.
        rewrite H3.
        iExists (DVALUE_I1 x); iSplitL ""; [ done | ].
        by iApply eval_int_icmp_dval_rel_I8. }

      { (* I32 *)
        iDestruct (dval_rel_I32_inv with "H1") as %Hi.
        iDestruct (dval_rel_I32_inv with "H2") as %Hi'; subst.

        cbn.
        inversion Hop; cbn.
        rewrite H3.
        iExists (DVALUE_I1 x); iSplitL ""; [ done | ].
        by iApply eval_int_icmp_dval_rel_I32. }

      { (* I64 *)
        iDestruct (dval_rel_I64_inv with "H1") as %Hi.
        iDestruct (dval_rel_I64_inv with "H2") as %Hi'; subst.

        cbn.
        inversion Hop; cbn.
        rewrite H3.
        iExists (DVALUE_I1 x); iSplitL ""; [ done | ].
        by iApply eval_int_icmp_dval_rel_I64. } }


    { rewrite /eval_icmp in Hop;
        destruct_match;
        rewrite /eval_int_icmp in Hop; inversion Hop;
        destruct_if.
       all:
          try iDestruct (dval_rel_I1_inv with "H1") as %Hi;
          try iDestruct (dval_rel_I1_inv with "H2") as %Hi';
          try iDestruct (dval_rel_I8_inv with "H1") as %Hi;
          try iDestruct (dval_rel_I8_inv with "H2") as %Hi';
          try iDestruct (dval_rel_I16_inv with "H1") as %Hi;
          try iDestruct (dval_rel_I16_inv with "H2") as %Hi';
          try iDestruct (dval_rel_I32_inv with "H1") as %Hi;
          try iDestruct (dval_rel_I32_inv with "H2") as %Hi';
          try iDestruct (dval_rel_I64_inv with "H1") as %Hi;
          try iDestruct (dval_rel_I64_inv with "H2") as %Hi';
          try iDestruct (dval_rel_poison_inv with "H1") as %Hi;
          try iDestruct (dval_rel_poison_inv with "H2") as %Hi';
         subst; cbn; try rewrite H1.
       all: try (iExists _; iSplitL ""; [ done | ];
                   by rewrite (unfold_dval_rel DVALUE_Poison)). }
  Qed.

  Lemma uval_rel_none:
    ⊢ uval_rel UVALUE_None UVALUE_None.
  Proof.
    rewrite /uval_rel; cbn; iIntros; inversion H; subst; eauto.
    iExists _; iSplitL ""; [ done |]. by rewrite unfold_dval_rel.
  Qed.

  Lemma uval_rel_array l_t l_s:
    Forall2 uval_rel l_t l_s -∗
    uval_rel (UVALUE_Array l_t) (UVALUE_Array l_s).
  Proof.
    iIntros "Hl"; iIntros (??).
    iInduction l_s as [] "IH" forall (l_t dv H).
    { cbn in *; inversion H; clear H.
      rewrite /Forall2.
      iDestruct (big_sepL2_nil_inv_r with "Hl") as "%Ht"; subst.
      cbn. iExists _; iSplitL ""; [ done | ].
      by rewrite unfold_dval_rel. }

    iDestruct (big_sepL2_cons_inv_r with "Hl") as (???) "(H & Hl)"; subst.
    cbn in H; inversion H; clear H.
    cbn.
    destruct (concretize_uvalue a) eqn: Ha; destruct unEitherT, s;
      inversion H1; clear H1.
    destruct (map_monad concretize_uvalue l_s) eqn: Hl_s; destruct unEitherT, s;
      inversion H0; clear H0. cbn.
    iDestruct ("IH" $! _ _ eq_refl with "Hl") as (??) "Hl".
    inversion H; clear H.
    iDestruct ("H" $! _ Ha) as (??) "H".
    rewrite H; cbn.
    destruct (map_monad concretize_uvalue l1') eqn: Hl1'; destruct unEitherT, s;
      inversion H2; clear H2. cbn.
    iExists _; iSplitL ""; [ done | ].
    iApply dval_rel_array; cbn; iFrame.
    by rewrite unfold_dval_rel.
  Qed.

  Lemma uval_rel_array_cons v_t v_s l_t l_s:
    uval_rel v_t v_s -∗
    uval_rel (UVALUE_Array l_t) (UVALUE_Array l_s) -∗
    uval_rel (UVALUE_Array (v_t :: l_t)) (UVALUE_Array (v_s :: l_s)).
  Proof.
    iIntros "Hl H". rewrite /uval_rel; cbn.
    iIntros (??).
    destruct (concretize_uvalue v_s) eqn: Hv_s; destruct unEitherT, s;
      inversion H; clear H.
    destruct (map_monad concretize_uvalue l_s) eqn: Hl_s;
      destruct unEitherT, s; inversion H1; clear H1.
    iSpecialize ("Hl" $! _ eq_refl).
    iDestruct "Hl" as (??) "Hl".
    rewrite H; cbn.
    iSpecialize ("H" $! _ eq_refl).
    iDestruct "H" as (??) "H".
    inversion H1; clear H1. destruct_match_sum.
    iExists _; iSplitL ""; [done | ].
    iApply (dval_rel_array_cons with "Hl H").
  Qed.

  Lemma uval_rel_struct l_t l_s:
    Forall2 uval_rel l_t l_s -∗
    uval_rel (UVALUE_Struct l_t) (UVALUE_Struct l_s).
  Proof.
    iIntros "Hl"; iIntros (??).
    iInduction l_s as [] "IH" forall (l_t dv H).
    { cbn in *; inversion H; clear H.
      rewrite /Forall2.
      iDestruct (big_sepL2_nil_inv_r with "Hl") as "%Ht"; subst.
      cbn. iExists _; iSplitL ""; [ done | ].
      by rewrite unfold_dval_rel. }

    iDestruct (big_sepL2_cons_inv_r with "Hl") as (???) "(H & Hl)"; subst.
    cbn in H; inversion H; clear H.
    cbn.
    destruct (concretize_uvalue a) eqn: Ha; destruct unEitherT, s;
      inversion H1; clear H1.
    destruct (map_monad concretize_uvalue l_s) eqn: Hl_s; destruct unEitherT, s;
      inversion H0; clear H0. cbn.
    iDestruct ("IH" $! _ _ eq_refl with "Hl") as (??) "Hl".
    inversion H; clear H.
    iDestruct ("H" $! _ Ha) as (??) "H".
    rewrite H; cbn.
    destruct (map_monad concretize_uvalue l1') eqn: Hl1'; destruct unEitherT, s;
      inversion H2; clear H2. cbn.
    iExists _; iSplitL ""; [ done | ].
    iApply dval_rel_struct; cbn; iFrame.
    by rewrite unfold_dval_rel.
  Qed.

  Lemma uval_rel_struct_cons v_t v_s l_t l_s:
    uval_rel v_t v_s -∗
    uval_rel (UVALUE_Struct l_t) (UVALUE_Struct l_s) -∗
    uval_rel (UVALUE_Struct (v_t :: l_t)) (UVALUE_Struct (v_s :: l_s)).
  Proof.
    iIntros "Hl H". rewrite /uval_rel; cbn.
    iIntros (??).
    destruct (concretize_uvalue v_s) eqn: Hv_s; destruct unEitherT, s;
      inversion H; clear H.
    destruct (map_monad concretize_uvalue l_s) eqn: Hl_s;
      destruct unEitherT, s; inversion H1; clear H1.
    iSpecialize ("Hl" $! _ eq_refl).
    iDestruct "Hl" as (??) "Hl".
    rewrite H; cbn.
    iSpecialize ("H" $! _ eq_refl).
    iDestruct "H" as (??) "H".
    inversion H1; clear H1. destruct_match_sum.
    iExists _; iSplitL ""; [done | ].
    iApply (dval_rel_struct_cons with "Hl H").
  Qed.

  Lemma dval_rel_length_serialize_dvalue dv1 dv2:
    dval_rel dv1 dv2 -∗
    ⌜length (serialize_dvalue dv1) = length (serialize_dvalue dv2)⌝.
  Proof.
    iIntros "H".
    iInduction dv2 as [] "IH" forall (dv1).
    { iDestruct (dval_rel_addr_inv with "H") as (?) "%Hi"; by subst. }
    { iDestruct (dval_rel_I1_inv with "H") as %Hi; by subst. }
    { iDestruct (dval_rel_I8_inv with "H") as %Hi; by subst. }
    { iDestruct (dval_rel_I32_inv with "H") as %Hi; by subst. }
    { iDestruct (dval_rel_I64_inv with "H") as %Hi; by subst. }
    { iDestruct (dval_rel_double_inv with "H") as "%Hi"; by subst. }
    { iDestruct (dval_rel_float_inv with "H") as "%Hi"; by subst. }
    { iDestruct (dval_rel_poison_inv with "H") as "%Hi"; by subst. }
    { rewrite unfold_dval_rel.
      destruct dv1; try done. }
    { rewrite unfold_dval_rel.
      destruct dv1; try done.
      iInduction fields as [] "IHfields" forall (fields0).
      { iDestruct (big_sepL2_nil_inv_r with "H") as "%Ht"; by subst. }
      { iDestruct (big_sepL2_cons_inv_r with "H") as (???)
            "(H & Hl)"; subst.
        iPoseProof "IH" as "IH'".
        iSpecialize ("IH" $! _ (in_eq _ _) with "H").
        iDestruct "IH" as %IH.
        iAssert (
          □(∀ x : dvalue,
              ⌜In x fields⌝ →
              ∀ a1 : dvalue, dval_rel a1 x -∗
              ⌜length (serialize_dvalue a1) =
                length (serialize_dvalue x)⌝))%I as "IHfieldspre".
        { iModIntro. iIntros (? Hin ?) "H".
          by iSpecialize ("IH'" $! _ (in_cons _ _ _ Hin) with "H"). }
        iDestruct ("IHfields" with "IHfieldspre Hl") as %H.
        rewrite !app_length.
        rewrite H; auto. } }
    { rewrite unfold_dval_rel.
      destruct dv1; try done.
      iInduction elts as [] "IHelts" forall (elts0).
      { iDestruct (big_sepL2_nil_inv_r with "H") as "%Ht"; by subst. }
      { iDestruct (big_sepL2_cons_inv_r with "H") as (???)
            "(H & Hl)"; subst.
        iPoseProof "IH" as "IH'".
        iSpecialize ("IH" $! _ (in_eq _ _) with "H").
        iDestruct "IH" as %IH.
        iAssert (
          □(∀ x : dvalue,
              ⌜In x elts⌝ →
              ∀ a1 : dvalue, dval_rel a1 x -∗
              ⌜length (serialize_dvalue a1) =
                length (serialize_dvalue x)⌝))%I as "IHeltspre".
        { iModIntro. iIntros (? Hin ?) "H".
          by iSpecialize ("IH'" $! _ (in_cons _ _ _ Hin) with "H"). }
        iDestruct ("IHelts" with "IHeltspre Hl") as %H.
        rewrite !app_length.
        rewrite H; auto. } }
  Qed.

  Lemma dval_rel_val_rel_index dv1 dv2:
    dval_rel dv1 dv2 -∗
    ∀ n, val_rel (nth n (serialize_dvalue dv1) SUndef)
            (nth n (serialize_dvalue dv2) SUndef).
  Proof.
    iIntros "H %n".
    iInduction dv2 as [] "IH" forall (dv1 n).
    { iDestruct (dval_rel_addr_inv with "H") as (?) "%Hi"; subst;
        cbn; rewrite unfold_dval_rel; repeat (destruct n; eauto). }
    { iDestruct (dval_rel_I1_inv with "H") as %Hi; subst;
        cbn; rewrite unfold_dval_rel; repeat (destruct n; eauto). }
    { iDestruct (dval_rel_I8_inv with "H") as %Hi;
        subst; cbn; rewrite unfold_dval_rel; repeat (destruct n; eauto). }
    { iDestruct (dval_rel_I32_inv with "H") as %Hi;
        subst; cbn; rewrite unfold_dval_rel; repeat (destruct n; eauto). }
    { iDestruct (dval_rel_I64_inv with "H") as %Hi;
        subst; cbn; rewrite unfold_dval_rel; repeat (destruct n; eauto). }
    { iDestruct (dval_rel_double_inv with "H") as  "%Hi";
        subst; cbn; rewrite unfold_dval_rel; iDestruct "H" as %H; subst;
       repeat (destruct n; eauto). }
    { iDestruct (dval_rel_float_inv with "H") as  "%Hi";
        subst; cbn; rewrite unfold_dval_rel; iDestruct "H" as %H; subst;
       repeat (destruct n; eauto). }
    { iDestruct (dval_rel_poison_inv with "H") as "%Hi";
        subst; cbn; rewrite unfold_dval_rel; repeat (destruct n; eauto). }
    { rewrite unfold_dval_rel.
      destruct dv1; cbn; try done.
      destruct n; auto. }
    { iPoseProof (dval_rel_length_serialize_dvalue with "H") as "%Hlen".
      rewrite unfold_dval_rel.
      destruct dv1; try done.
      iInduction fields as [] "IHfields" forall (n fields0 Hlen).
      { iDestruct (big_sepL2_nil_inv_r with "H") as "%Ht"; subst.
        subst; cbn; repeat (destruct n; eauto). }
      { iDestruct (big_sepL2_cons_inv_r with "H") as (???)
            "(H & Hl)"; subst.
        iPoseProof (dval_rel_length_serialize_dvalue with "H") as
          "%Hlen_".

        iPoseProof "IH" as "IH'".
        iSpecialize ("IH" $! _ (in_eq _ _) with "H").
        cbn in Hlen. do 2 rewrite app_length in Hlen.
        rewrite Hlen_ in Hlen.
        apply plus_reg_l in Hlen.

        assert (n < length (serialize_dvalue x1) \/
                  length (serialize_dvalue x1) <= n) by lia.
        destruct H.
        { cbn. by do 2 (rewrite app_nth1; [ | lia]). }
        { cbn. do 2 (rewrite app_nth2; [ | try lia]).
          rewrite Hlen_.

        iAssert (
          □(∀ x : dvalue,
              ⌜In x fields⌝ →
              ∀ a0 a1, dval_rel a0 x -∗
              val_rel (nth a1 (serialize_dvalue a0) SUndef)
                (nth a1 (serialize_dvalue x) SUndef)))%I as "IHfieldspre".
        { iModIntro. iIntros (? Hin ? ?) "H".
          by iSpecialize ("IH'" $! _ (in_cons _ _ _ Hin) with "H"). }

          iSpecialize ("IHfields" $! _ _ Hlen with "IHfieldspre").
          iApply "IHfields"; try done. } } }
    { iPoseProof (dval_rel_length_serialize_dvalue with "H") as "%Hlen".
      rewrite unfold_dval_rel.
      destruct dv1; try done.
      iInduction elts as [] "IHelts" forall (n elts0 Hlen).
      { iDestruct (big_sepL2_nil_inv_r with "H") as "%Ht"; subst.
        subst; cbn; repeat (destruct n; eauto). }
      { iDestruct (big_sepL2_cons_inv_r with "H") as (???)
            "(H & Hl)"; subst.
        iPoseProof (dval_rel_length_serialize_dvalue with "H") as
          "%Hlen_".

        iPoseProof "IH" as "IH'".
        iSpecialize ("IH" $! _ (in_eq _ _) with "H").
        cbn in Hlen. do 2 rewrite app_length in Hlen.
        rewrite Hlen_ in Hlen.
        apply plus_reg_l in Hlen.

        assert (n < length (serialize_dvalue x1) \/
                  length (serialize_dvalue x1) <= n) by lia.
        destruct H.
        { cbn. by do 2 (rewrite app_nth1; [ | lia]). }
        { cbn. do 2 (rewrite app_nth2; [ | try lia]).
          rewrite Hlen_.

        iAssert (
          □(∀ x : dvalue,
              ⌜In x elts⌝ →
              ∀ a0 a1, dval_rel a0 x -∗
              val_rel (nth a1 (serialize_dvalue a0) SUndef)
                (nth a1 (serialize_dvalue x) SUndef)))%I as "IHeltspre".
        { iModIntro. iIntros (? Hin ? ?) "H".
          by iSpecialize ("IH'" $! _ (in_cons _ _ _ Hin) with "H"). }

          iSpecialize ("IHelts" $! _ _ Hlen with "IHeltspre").
          iApply "IHelts"; try done. } } }
  Qed.

  Lemma dvalue_is_not_poison:
    forall dv, dv ≠ DVALUE_Poison -> InterpretationStack.D.dvalue_is_poison dv = false.
  Proof.
    intros dv H; destruct dv; eauto.
    exfalso; auto.
  Qed.

  Global Instance block_rel_persistent b_t b_s :
    Persistent (block_rel b_t b_s).
  Proof. apply _. Qed.
  Global Instance loc_rel_persistent l_t l_s:
    Persistent (l_t ↔h l_s).
  Proof. apply _. Qed.
  Global Instance val_rel_persistent v_t v_s :
    Persistent (val_rel v_t v_s).
  Proof. induction v_s; induction v_t; apply _. Qed.

  #[global] Instance dval_rel_persistent u_t u_s :
    Persistent (dval_rel u_t u_s).
  Proof.
    rewrite /Persistent.
    pose (F_ind :=
      (fun e_t e_s => <pers> dval_rel e_t e_s)%I).
    assert (NonExpansive (F_ind :
                (dvalue -d> dvalue -d> iPropI Σ))).
    { repeat intro. rewrite /F_ind.
      pose proof dval_relF_ne.
      by repeat f_equiv. }

    iIntros "H".
    iApply (dval_rel_ind F_ind); [ | done].
    iModIntro.

    iIntros (??) "H".
    rewrite /F_ind.
    destruct e_s; rewrite /dval_relF; eauto.
    1-7,9,10:
      destruct e_t; try done; iDestruct "H" as "#H";
        rewrite unfold_dval_rel;
        try done.

    2,3: destruct e_t eqn: Ht; try done.
    3: rewrite unfold_dval_rel;
      by iApply big_sepL2_persistently.
    1: by iApply big_sepL2_persistently.
    rewrite unfold_dval_rel; by iModIntro.
  Qed.

  #[global] Instance uval_rel_persistent dv_t dv_s :
    Persistent (uval_rel dv_t dv_s).
  Proof. apply _. Qed.

  Lemma dval_rel_implies_val_rel dv1 dv2:
    dval_rel dv1 dv2 -∗
    Forall2 val_rel (serialize_dvalue dv1) (serialize_dvalue dv2).
  Proof.
    rewrite /Forall2.
    iIntros "#HV". rewrite big_sepL2_forall.
    iDestruct (dval_rel_length_serialize_dvalue with "HV") as %H.
    iSplit; auto.
    iDestruct (dval_rel_val_rel_index with "HV") as "H".
    iIntros.
    iSpecialize ("H" $! k).
    eapply nth_lookup_Some in H0, H1.
    by rewrite H0 H1.
    Unshelve. all : exact SUndef.
  Qed.

  Lemma repeat_some_inv {A} (d : A) n k x:
    repeat d n !! k = Some x ->
    d = x.
  Proof.
    revert d n x.
    induction k; eauto; cbn.
    { intros; destruct n; eauto; cbn in H; by inversion H. }
    { intros. destruct n; cbn in H; eauto; inversion H. }
  Qed.

  Lemma zero_initializer_uval_refl :
    forall d v (H : InterpretationStack.D.dv_zero_initializer d = inr v),
    Addr.null ↔h Addr.null -∗
    dval_rel v v.
  Proof.
    rewrite /InterpretationStack.D.dv_zero_initializer.
    intros. iIntros "#H".
    iInduction d as [] "IH" forall (v H); try solve [inversion H].
    1-5:
      rewrite /DV.default_dvalue_of_dtyp in H; cbn in H;
      try solve [inversion H].
    { cbn. rewrite /DV.default_dvalue_of_dtyp_i in H.
      destruct_if; by rewrite dval_rel_unfold. }
    { inversion H; subst; cbn.
      by iApply dval_rel_addr. }
    { inversion H.
      by iApply dval_rel_none. }
    1-2: inversion H;
      by rewrite dval_rel_unfold.
    all: rewrite dval_rel_unfold.
    { cbn in H.
      destruct (DV.default_dvalue_of_dtyp d) eqn : He;
        inversion H; cbn.
      iApply big_sepL2_forall.
      iSplitL ""; [ done | ].
      iIntros (?????). iSpecialize ("IH" $! _ eq_refl).
      rewrite H0 in H2. inversion H2; subst.
      by apply repeat_some_inv in H0; subst. }
    { inversion H; clear H.
      destruct (map_monad DV.default_dvalue_of_dtyp fields) eqn: Hfields;
        inversion H1; subst; clear H1; cbn.
      iInduction fields as [] "IH'" forall (l Hfields).
      { cbn in *; subst; inversion Hfields; subst; by cbn. }
      cbn in Hfields; destruct_match.
      cbn.
      iSplitL "IH".
      { iApply "IH"; eauto. }
      iApply "IH'"; eauto.
      iModIntro. iIntros (??); iApply "IH"; eauto. }
  Qed.

  Lemma default_dvalue_dval_rel τ uv:
   default_dvalue_of_dtyp τ = inr uv ->
    Addr.null ↔h Addr.null -∗
    dval_rel uv uv.
  Proof.
    iIntros (?) "#Hnull".
    iInduction τ as [] "IH" forall (uv H); inversion H.
    { cbn in H.
      rewrite /default_dvalue_of_dtyp_i in H.
      destruct ((a =? 64)%N);
        [ inversion H; rewrite unfold_dval_rel; cbn; by iPureIntro | ].
      destruct ((a =? 32)%N);
        [ inversion H; rewrite unfold_dval_rel; cbn; by iPureIntro | ].
      destruct ((a =? 8)%N);
        [ inversion H; rewrite unfold_dval_rel; cbn; by iPureIntro | ].
      destruct ((a =? 1)%N);
        [ inversion H; rewrite unfold_dval_rel; cbn; by iPureIntro | ].
      inversion H. }
    1-4: by rewrite unfold_dval_rel.
    { destruct ((0 <=? sz)%N); inversion H1.
      destruct (default_dvalue_of_dtyp τ); inversion H1.
      rewrite unfold_dval_rel; cbn.
      iSpecialize ("IH" $! _ eq_refl).
      rewrite /Forall2.
      rewrite big_sepL2_forall.
      iSplitL ""; [ done | ].
      iIntros; rewrite H0 in H4; inversion H4; subst.
      apply repeat_Some in H0; by subst. }
    { destruct (map_monad default_dvalue_of_dtyp fields) eqn: Hfields;
        inversion H1; subst; clear H1.
      rewrite unfold_dval_rel; cbn.
      rewrite /Forall2.
      rewrite big_sepL2_forall.
      iSplitL ""; [ done | ].
      iIntros; rewrite H0 in H1; inversion H1; subst; clear H1.
      destruct (map_monad_dvalue_to_uvalue _ _ _ _ Hfields H0)
        as (?&?&?&?&?); subst.
      iApply "IH"; eauto. }
  Qed.

  Lemma uval_rel_undef τ:
    Addr.null ↔h Addr.null -∗
    uval_rel (UVALUE_Undef τ) (UVALUE_Undef τ).
  Proof.
    rewrite /uval_rel.
    iIntros "#Hn" (??). cbn in H; cbn.
    inversion H. iExists dv; iSplitL ""; [ done | ].
    clear H.
    destruct (default_dvalue_of_dtyp τ) eqn: H;
      inversion H1; subst.
    by iApply default_dvalue_dval_rel.
  Qed.

  Lemma dval_rel_inj dv dv' dv'':
    dval_rel dv' dv -∗ dval_rel dv'' dv -∗ ⌜dv' = dv''⌝.
  Proof.
    iInduction dv as [] "H" forall (dv' dv''); iIntros "H1 H2".
    { iDestruct (dval_rel_addr_inv with "H1") as %H.
      destruct H; subst.
      iDestruct (dval_rel_addr_inv with "H2") as %H.
      destruct H; subst.
      rewrite !dval_rel_unfold; cbn.
      iDestruct (heapbij_loc_agree with "H1 H2") as "%H".
      destruct H. specialize (H0 eq_refl). subst; auto. }
    { iDestruct (dval_rel_I1_inv with "H1") as %H; subst.
      iDestruct (dval_rel_I1_inv with "H2") as %H; subst. done. }
    { iDestruct (dval_rel_I8_inv with "H1") as %H; subst.
      iDestruct (dval_rel_I8_inv with "H2") as %H; subst. done. }
    { iDestruct (dval_rel_I32_inv with "H1") as %H; subst.
      iDestruct (dval_rel_I32_inv with "H2") as %H; subst. done. }
    { iDestruct (dval_rel_I64_inv with "H1") as %H; subst.
      iDestruct (dval_rel_I64_inv with "H2") as %H; subst. done. }
    { iDestruct (dval_rel_double_inv with "H1") as %H; subst.
      iDestruct (dval_rel_double_inv with "H2") as %H; subst. done. }
    { iDestruct (dval_rel_float_inv with "H1") as %H; subst.
      iDestruct (dval_rel_float_inv with "H2") as %H; subst. done. }
    { iDestruct (dval_rel_poison_inv with "H1") as %H; subst.
      iDestruct (dval_rel_poison_inv with "H2") as %H; subst. done. }
    { iDestruct (dval_rel_None_inv with "H1") as %H; subst.
      iDestruct (dval_rel_None_inv with "H2") as %H; subst. done. }
    { iDestruct (dval_rel_struct_inv with "H1") as %H; subst.
      destruct H; subst.
      iDestruct (dval_rel_struct_inv with "H2") as %H; subst.
      destruct H; subst.
      rewrite !dval_rel_unfold; cbn.
      rewrite /Forall2.
      iInduction fields as [] "IH" forall (x x0).
      { cbn in *.
        iDestruct (big_sepL2_nil_inv_r with "H1") as %H1; subst.
        iDestruct (big_sepL2_nil_inv_r with "H2") as %H1; subst.
        done. }
      { cbn in *.
        iDestruct (big_sepL2_cons_inv_r with "H1") as (???) "(Hv & H1)"; subst.
        iDestruct (big_sepL2_cons_inv_r with "H2") as (???) "(Hv' & H2)"; subst.
        assert (a = a \/ In a fields) by auto.
        iPoseProof "H" as "H'".
        iSpecialize ("H" $! _ H with "Hv Hv'").
        iDestruct "H" as %H'; subst.
        iAssert (∀ x1 : dvalue,
                ⌜In x1 fields⌝
                → ∀ dv' dv'' : dvalue, dval_rel dv' x1 -∗
                dval_rel dv'' x1 -∗ ⌜dv' = dv''⌝)%I as "Ha".
        { iIntros (????) "Hdv1 Hdv2".
          assert (a = x1 \/ In x1 fields) by auto.
          iSpecialize ("H'" $! _ H1 with "Hdv1 Hdv2"). done. }
        iDestruct ("IH" with "Ha H1 H2") as "%H''".
        by inv H''. } }

    { iDestruct (dval_rel_array_inv with "H1") as %H; subst.
      destruct H; subst.
      iDestruct (dval_rel_array_inv with "H2") as %H; subst.
      destruct H; subst.
      rewrite !dval_rel_unfold; cbn.
      rewrite /Forall2.
      iInduction elts as [] "IH" forall (x x0).
      { cbn in *.
        iDestruct (big_sepL2_nil_inv_r with "H1") as %H1; subst.
        iDestruct (big_sepL2_nil_inv_r with "H2") as %H1; subst.
        done. }
      { cbn in *.
        iDestruct (big_sepL2_cons_inv_r with "H1") as (???) "(Hv & H1)"; subst.
        iDestruct (big_sepL2_cons_inv_r with "H2") as (???) "(Hv' & H2)"; subst.
        assert (a = a \/ In a elts) by auto.
        iPoseProof "H" as "H'".
        iSpecialize ("H" $! _ H with "Hv Hv'").
        iDestruct "H" as %H'; subst.
        iAssert (∀ x1 : dvalue,
                ⌜In x1 elts⌝
                → ∀ dv' dv'' : dvalue, dval_rel dv' x1 -∗
                dval_rel dv'' x1 -∗ ⌜dv' = dv''⌝)%I as "Ha".
        { iIntros (????) "Hdv1 Hdv2".
          assert (a = x1 \/ In x1 elts) by auto.
          iSpecialize ("H'" $! _ H1 with "Hdv1 Hdv2"). done. }
        iDestruct ("IH" with "Ha H1 H2") as "%H''".
        by inv H''. } }
  Qed.

  Lemma dval_rel_inj' dv dv' dv'':
    dval_rel dv dv' -∗ dval_rel dv dv'' -∗ ⌜dv' = dv''⌝.
  Proof.
    iInduction dv as [] "H" forall (dv' dv''); iIntros "H1 H2".
    { iDestruct (dval_rel_addr_inv' with"H1") as %H.
      destruct H; subst.
      iDestruct (dval_rel_addr_inv' with"H2") as %H.
      destruct H; subst.
      rewrite !dval_rel_unfold; cbn.
      iDestruct (heapbij_loc_agree with "H1 H2") as "%H".
      destruct H. specialize (H eq_refl). subst; auto. }
    { iDestruct (dval_rel_I1_inv' with"H1") as %H; subst.
      iDestruct (dval_rel_I1_inv' with"H2") as %H; subst. done. }
    { iDestruct (dval_rel_I8_inv' with"H1") as %H; subst.
      iDestruct (dval_rel_I8_inv' with"H2") as %H; subst. done. }
    { iDestruct (dval_rel_I32_inv' with"H1") as %H; subst.
      iDestruct (dval_rel_I32_inv' with"H2") as %H; subst. done. }
    { iDestruct (dval_rel_I64_inv' with"H1") as %H; subst.
      iDestruct (dval_rel_I64_inv' with"H2") as %H; subst. done. }
    { iDestruct (dval_rel_double_inv' with"H1") as %H; subst.
      iDestruct (dval_rel_double_inv' with"H2") as %H; subst. done. }
    { iDestruct (dval_rel_float_inv' with"H1") as %H; subst.
      iDestruct (dval_rel_float_inv' with"H2") as %H; subst. done. }
    { iDestruct (dval_rel_poison_inv' with"H1") as %H; subst.
      iDestruct (dval_rel_poison_inv' with"H2") as %H; subst. done. }
    { iDestruct (dval_rel_None_inv' with"H1") as %H; subst.
      iDestruct (dval_rel_None_inv' with"H2") as %H; subst. done. }
    { iDestruct (dval_rel_struct_inv' with"H1") as %H; subst.
      destruct H; subst.
      iDestruct (dval_rel_struct_inv' with"H2") as %H; subst.
      destruct H; subst.
      rewrite !dval_rel_unfold; cbn.
      rewrite /Forall2.
      iInduction fields as [] "IH" forall (x x0).
      { cbn in *.
        iDestruct (big_sepL2_nil_inv_l with "H1") as %H1; subst.
        iDestruct (big_sepL2_nil_inv_l with "H2") as %H1; subst.
        done. }
      { cbn in *.
        iDestruct (big_sepL2_cons_inv_l with "H1") as (???) "(Hv & H1)"; subst.
        iDestruct (big_sepL2_cons_inv_l with "H2") as (???) "(Hv' & H2)"; subst.
        assert (a = a \/ In a fields) by auto.
        iPoseProof "H" as "H'".
        iSpecialize ("H" $! _ H with "Hv Hv'").
        iDestruct "H" as %H'; subst.
        iAssert
            (∀ x2 : dvalue,
            ⌜In x2 fields⌝
            → ∀ dv' dv'' : dvalue, dval_rel x2 dv' -∗
            dval_rel x2 dv'' -∗ ⌜dv' = dv''⌝)%I as "Ha".
        { iIntros (????) "Hdv1 Hdv2".
          assert (a = x2 \/ In x2 fields) by auto.
          iSpecialize ("H'" $! _ H1 with "Hdv1 Hdv2"). done. }
        iDestruct ("IH" with "Ha H1 H2") as "%H''".
        by inv H''. } }

    { iDestruct (dval_rel_array_inv' with "H1") as %H; subst.
      destruct H; subst.
      iDestruct (dval_rel_array_inv' with "H2") as %H; subst.
      destruct H; subst.
      rewrite !dval_rel_unfold; cbn.
      rewrite /Forall2.
      iInduction elts as [] "IH" forall (x x0).
      { cbn in *.
        iDestruct (big_sepL2_nil_inv_l with "H1") as %H1; subst.
        iDestruct (big_sepL2_nil_inv_l with "H2") as %H1; subst.
        done. }
      { cbn in *.
        iDestruct (big_sepL2_cons_inv_l with "H1") as (???) "(Hv & H1)"; subst.
        iDestruct (big_sepL2_cons_inv_l with "H2") as (???) "(Hv' & H2)"; subst.
        assert (a = a \/ In a elts) by auto.
        iPoseProof "H" as "H'".
        iSpecialize ("H" $! _ H with "Hv Hv'").
        iDestruct "H" as %H'; subst.
        iAssert
          (∀ x2 : dvalue,
            ⌜In x2 elts⌝ →
            ∀ dv' dv'' : dvalue, dval_rel x2 dv' -∗
            dval_rel x2 dv'' -∗ ⌜dv' = dv''⌝)%I
          as "Ha".
        { iIntros (????) "Hdv1 Hdv2".
          assert (a = x2 \/ In x2 elts) by auto.
          iSpecialize ("H'" $! _ H1 with "Hdv1 Hdv2"). done. }
        iDestruct ("IH" with "Ha H1 H2") as "%H''".
        by inv H''. } }
  Qed.

  Lemma dval_rel_ne_inj dv1 dv2 dv' dv'':
    dval_rel dv' dv1 -∗ dval_rel dv'' dv2 -∗ ⌜dv2 <> dv1⌝ -∗ ⌜dv' <> dv''⌝.
  Proof.
    iIntros "H1 H2 #H". iIntros (?).
    iAssert (⌜dv2 = dv1⌝ -∗ False)%I as "H'".
    { iIntros (?). iDestruct "H" as %H'. eauto. }
    iApply "H'". subst.
    iDestruct (dval_rel_inj' with "H1 H2") as %H''; done.
  Qed.

  Lemma dval_rel_lookup_none {A} fn1 fn2 (r_t r_s : list (_ * A)):
    dval_rel fn1 fn2 -∗
    ([∗ list] v_t;v_s ∈ r_t.*1;r_s.*1, dval_rel v_t v_s) -∗
    ⌜assoc fn2 r_s = None -> assoc fn1 r_t = None⌝.
  Proof.
    iInduction r_t as [] "IH" forall (r_s fn1 fn2).
    { cbn; iIntros "#Hdv Hrel". done. }
    { cbn; iIntros "#Hdv Hrel %Hlu".
      destruct a.
      destruct (RelDec.rel_dec fn1 d) eqn: Hfn; reldec.
      { iDestruct (big_sepL2_cons_inv_l with "Hrel") as (???) "(HΦ & Hrel)".
        cbn.
        iDestruct (dval_rel_inj' with "Hdv HΦ") as %H'. subst.
        destruct r_s; try done. cbn in *.
        destruct p. destruct_if. cbn in *. inv H.
        reldec. done. }
      { iDestruct (big_sepL2_cons_inv_l with "Hrel") as (???) "(HΦ & Hrel)".
        cbn. destruct r_s; try done. cbn in *.
        destruct p. destruct_if. cbn in *. inv H. reldec.
        iDestruct ("IH" with "Hdv Hrel") as %Hlu'. specialize (Hlu' eq_refl).
        eauto. } }
  Qed.

  Lemma dval_rel_lookup_some {A} fn1 fn2 (r_t r_s : list (_ * A)):
    dval_rel fn1 fn2 -∗
    ([∗ list] v_t;v_s ∈ r_t.*1;r_s.*1, dval_rel v_t v_s) -∗
    ⌜∀ v, assoc fn2 r_s = Some v -> ∃ v', assoc fn1 r_t = Some v'⌝.
  Proof.
    iInduction r_t as [] "IH" forall (r_s fn1 fn2).
    { cbn; iIntros "#Hdv Hrel".
      iDestruct (big_sepL2_nil_inv_l with "Hrel") as %Hnil;
        destruct r_s; try done. }
    { cbn; iIntros "#Hdv Hrel %Hlu".
      destruct a.
      destruct (RelDec.rel_dec fn1 d) eqn: Hfn; reldec.
      { iDestruct (big_sepL2_cons_inv_l with "Hrel") as (???) "(HΦ & Hrel)".
        cbn.
        iDestruct (dval_rel_inj' with "Hdv HΦ") as %H'. subst.
        destruct r_s; try done. cbn in *.
        destruct p. destruct_if. cbn in *. inv H.
        destruct (RelDec.rel_dec x2 x2) eqn: Hx; reldec; try done.
        iIntros (?); inv a1; eauto. }
      { iDestruct (big_sepL2_cons_inv_l with "Hrel") as (???) "(HΦ & Hrel)".
        iIntros (?).
        cbn. destruct r_s; try done. cbn in *.
        destruct p. inv H.
        destruct_if; reldec; try done.
        - iDestruct (dval_rel_inj with "Hdv HΦ") as %H'. subst. done.
        - iDestruct ("IH" with "Hdv Hrel") as %Hlu'. specialize (Hlu' _ a0); eauto. } }
  Qed.

End val_rel_properties.


Section mem_rel.

  (* Utility functions on memory lookup and write *)

  (* Inversion lemmas for lookup *)
  Lemma lookup_add_None {A} a (nv : list A) o v :
    lookup a (add_all_index nv o v) = None ->
    lookup a v = None.
  Proof.
    revert a o v.
    induction nv; [ done | ].
    intros. cbn -[lookup] in H.
    destruct (decide (a0 = o)).
    { subst. rewrite lookup_insert in H; inversion H. }
    { rewrite lookup_insert_ne in H; eauto. }
  Qed.

  Lemma lookup_add_None1 {A} a (nv : list A) (o : Z) (v : IntMap A) :
    (a < o \/ o + length nv ≤ a)%Z ->
    lookup a v = None ->
    lookup a (add_all_index nv o v) = None.
  Proof.
    revert a o v.
    induction nv; [ done | ].
    intros. cbn -[lookup] in H.
    destruct (decide (a0 = o)); [lia | ].
    { cbn -[lookup].
      rewrite lookup_insert_ne; [ | lia].
      specialize (IHnv a0 (o + 1)%Z).
      eapply IHnv; eauto. lia. }
  Qed.

  Lemma In_Zseq_bounds a (i : Z) o:
    (a ≤ i)%Z ->
    (i < a + Z.of_nat o)%Z ->
    In i (Zseq a o).
  Proof.
    revert a i.
    induction o; cbn; [ lia | ].
    intros.
    destruct (decide (a = i)) eqn: Hi; [ by left | ].
    right.
    assert (Z.succ a ≤ i)%Z by lia.
    eapply IHo; eauto. lia.
  Qed.

  Lemma nat_interval_choice (a b c : nat) :
    a < b \/ (b ≤ a /\ a < b + c) \/ b + c ≤ a.
  Proof. lia. Qed.

  Lemma Z_interval_choice (a b c : Z) :
    (a < b \/ (b ≤ a /\ a < b + c) \/ b + c ≤ a)%Z.
  Proof. lia. Qed.

  Lemma lookup_add_None2 {A} a (nv : list A) o v :
    nv <> nil ->
    lookup a (add_all_index nv o v) = None ->
    o <> a.
  Proof.
    repeat intro; subst.
    destruct nv; [done | ].
    rewrite lookup_insert in H0. inversion H0.
  Qed.

  Lemma lookup_add_None_range {A} (a : Z) (nv : list A) o v :
    nv <> nil ->
    lookup a (add_all_index nv o v) = None ->
    (a < o \/ o + length nv ≤ a)%Z.
  Proof.
    repeat intro; subst.

    pose proof (Z_interval_choice  a o (length nv)).
    destruct H1; [ | destruct H1]; [ lia | | lia ].
    exfalso.
    destruct nv; [ done | ].
    clear H. cbn -[lookup] in *.

    revert a a0 o v H0 H1.
    induction nv; intros; eauto.
    { cbn -[lookup] in *.
      assert (o = a) by lia.
      rewrite H in H0; rewrite lookup_insert in H0; inversion H0. }
    { cbn -[lookup] in *.
      destruct (decide (a0 = o)) eqn: Ha0.
      { subst; rewrite lookup_insert in H0; inversion H0. }
      { rewrite lookup_insert_ne in H0; eauto.
        eapply IHnv; eauto. lia. } }
  Qed.

  Lemma list_nth_z_nth {A} l (n : Z) (default : A):
    length l > 0 ->
    (n < length l)%Z ->
    (0 <= n)%Z ->
    Coqlib.list_nth_z l n = Some (List.nth (Z.to_nat n) l default).
  Proof.
    intros Hb1 Hb2 Hb3.
    destruct l; cbn in Hb1; [ lia | ]. clear Hb1.
    revert n a default Hb2 Hb3; induction l; eauto.
    { cbn in *; eauto.
      intros.
      destruct (Coqlib.zeq n 0) eqn: H; try rewrite e; [ done | lia ]. }
    { intros. cbn in *.
      destruct (Coqlib.zeq n 0) eqn: Hz.
      { assert (Z.to_nat n = 0) by lia. by rewrite H. }
      assert (Hbound : (Z.pred n < S (length l))%Z) by lia.
      specialize (IHl (Z.pred n) a default Hbound).
      rewrite IHl; [ | lia].
      destruct (Z.to_nat n) eqn: H; [ lia | ].
      assert (Z.to_nat (Z.pred n) = n1) by lia. by rewrite H0. }
  Qed.

  Lemma lookup_add_Some_inv {A} (o a : Z) (nv : list A) v (m : A) (default : A):
    lookup a (add_all_index nv o v) = Some m ->
    (* lookup is within bounds to the newly added index  *)
    ((o ≤ a /\ a < o + length nv)%Z /\
      m = List.nth (Z.to_nat (a - o)) nv default) \/
    (* lookup is not within bounds of the newly added index;
      so it returns the original values in [v] *)
    ((a < o \/ o + length nv ≤ a)%Z /\ lookup a v = Some m).
  Proof.
    destruct (Z_interval_choice a o (length nv)) as [ | [ | ] ]
      eqn: Hrange.
    (* access offset is before write index *)
    { right; split; [ by left | ].
      rewrite lookup_add_all_index_out in H; eauto. }
    (* access offset is within range of write index *)
    { left; split; [ done | ].
      setoid_rewrite lookup_add_all_index_in in H.
      { inversion H; reflexivity. }
      { rewrite Zlength_correct; lia. }
      pose proof @list_nth_z_nth.
      specialize (H0 _ nv (Z.to_nat (a - o)%Z) default).
      eapply list_nth_z_nth; lia. }
    (* access offset is after write index *)
    { right; split; [ by right | ].
      rewrite lookup_add_all_index_out in H; eauto.
      rewrite Zlength_correct. lia. }
  Qed.

  (** *Memory relation
      Definitions for memory relations
      - [mem_byte_rel] is a refinement relation that relates each byte in memory
        between source and target
      - [mem_read_rel] is a relation that relates typed reads of memory
        given the same offset
   *)
  Context {Σ : gFunctors} `{HB: heapbijGS Σ}.

  Definition mem_byte_rel (m_t m_s : mem_block) : iPropI Σ :=
    (∀ k v, ⌜lookup k m_s = Some v⌝ -∗
       ∃ v', ⌜lookup k m_t = Some v'⌝ ∗ val_rel v' v) ∗
    ⌜∀ k, lookup k m_s = None -> lookup k m_t = None⌝.

  Definition mem_read_rel (m_t m_s : mem_block) : iPropI Σ :=
    (∀ τ o,
      ⌜dtyp_WF τ⌝ -∗
      uval_rel (read_in_mem_block m_t o τ) (read_in_mem_block m_s o τ)).

  Lemma mem_byte_rel_empty:
    ⊢ mem_byte_rel empty empty.
  Proof.
    iSplitL "".
    { iIntros (???).
      setoid_rewrite lookup_empty in H; inversion H. }
    { iPureIntro; intros * Hlu; done. }
  Qed.

  Lemma mem_byte_rel_init_block_undef n :
    ⊢ mem_byte_rel (init_block_undef n empty)
      (init_block_undef n empty).
  Proof.
    iInduction n as [|] "IH"; rewrite /mem_byte_rel; cbn.
    { iSplitL "".
      { iIntros (???).
        setoid_rewrite insert_empty in H.
        eapply lookup_singleton_inv in H; try typeclasses eauto.
        destruct H; subst.
        iExists SUndef. rewrite lookup_insert; auto. }
      { iPureIntro; intros * Hlu; done. } }
    { iDestruct "IH" as "(IH1 & %IH2)".
      iSplitL "".
      { iIntros (???).
        destruct (decide ((S n : Z) = k)).
        { subst; rewrite lookup_insert in H; inv H.
          iExists SUndef.
          rewrite lookup_insert; done. }
        { subst; rewrite lookup_insert_ne in H; eauto.
          iSpecialize ("IH1" $! _ _ H).
          rewrite lookup_insert_ne; done. } }
      { iPureIntro.
        intros * H.
        destruct (decide ((S n : Z) = k)).
        { subst; rewrite lookup_insert in H; inv H. }
        { subst; rewrite lookup_insert_ne in H; eauto.
          rewrite lookup_insert_ne; done. } } }
  Qed.

  Lemma mem_byte_rel_make_empty_mem_block d :
    ⊢ mem_byte_rel (make_empty_mem_block d) (make_empty_mem_block d).
  Proof.
    rewrite /make_empty_mem_block /init_block.
    destruct (sizeof_dtyp d).
    { iApply mem_byte_rel_empty. }
    { iApply mem_byte_rel_init_block_undef. }
  Qed.

  Definition mem_byte_rel_sundef o n m_t m_s:
    all_not_sundef (lookup_all_index o n m_s SUndef) = true ->
    mem_byte_rel m_t m_s -∗
    ⌜all_not_sundef (lookup_all_index o n m_t SUndef) = true⌝.
  Proof.
    rewrite /lookup_all_index.
    remember (N.to_nat n). clear n Heqn0. rename n0 into n.
    rewrite /mem_byte_rel.
    iIntros (Hundef) "(#H & Hn)".
    iInduction n as [| n] "IHn" forall (o Hundef); [ done | cbn].
    destruct (lookup o m_s) eqn: H.
    { iSpecialize ("H" $! _ _ H).
      iDestruct "H" as (??) "H".
      cbn in Hundef. rewrite H in Hundef.
      apply andb_prop in Hundef; destruct Hundef.
      rewrite H0.
      iDestruct (val_rel_defined with "H") as "%H'".
      rewrite H1 in H'. rewrite -H'.
      rewrite andb_true_iff.
      iSplitL "".
      { iPureIntro; by apply Is_true_eq_true. }
      by iApply "IHn". }
    { cbn in Hundef. rewrite H in Hundef.
      apply andb_prop in Hundef. destruct Hundef. inversion H0. }
  Qed.

  Definition mem_byte_rel_sundef_false o n m_t m_s:
    all_not_sundef (lookup_all_index o n m_s SUndef) = false ->
    mem_byte_rel m_t m_s -∗
    ⌜all_not_sundef (lookup_all_index o n m_t SUndef) = false⌝.
  Proof.
    rewrite /lookup_all_index.
    remember (N.to_nat n). clear n Heqn0. rename n0 into n.
    rewrite /mem_byte_rel.
    iIntros (Hundef) "(#H & %Hn)".
    iInduction n as [| n] "IHn" forall (o Hundef); [ done | cbn].
    destruct (lookup o m_s) eqn: H.
    { iSpecialize ("H" $! _ _ H).
      iDestruct "H" as (??) "H". rewrite H0.
      cbn in Hundef; rewrite H in Hundef.
      rewrite andb_false_iff in Hundef.
      destruct Hundef.
      { iDestruct (val_rel_defined with "H") as %Hdef.

        rewrite Hdef in H1; rewrite H1. done. }
      { iDestruct ("IHn" $! _ H1) as %IH.
        rewrite /all_not_sundef in IH. rewrite IH.
        by rewrite andb_false_r. } }
    { cbn in Hundef. rewrite H in Hundef.
      rewrite andb_false_iff in Hundef.
      specialize (Hn _ H). rewrite Hn. done. }
  Qed.

  Definition mem_byte_rel_sundef_pos o n m_t m_s:
    (n <> 0)%N ->
    all_not_sundef (lookup_all_index o n m_s SUndef) = true ->
    mem_byte_rel m_t m_s -∗
    ∃ v v', ⌜lookup o m_s = Some v⌝ ∗ ⌜lookup o m_t = Some v'⌝
      ∗ val_rel v' v.
  Proof.
    rewrite /lookup_all_index.
    remember (N.to_nat n). intros ? Hundef.
    assert (n0 > 0)%nat by lia.
    clear n Heqn0 H. rename n0 into n.
    rewrite /mem_byte_rel.
    iIntros "(#H & Hn)".
    iInduction n as [| n] "IHn" forall (o Hundef); [ lia | cbn].
    cbn in *.

    destruct (lookup o m_s) eqn: H.
    { iSpecialize ("H" $! _ _ H).
      iDestruct "H" as (??) "H".
      iExists _, _; by do 2 (iSplitL ""; [ done | ]). }
    { cbn in Hundef. done. }
  Qed.

  Definition mem_byte_rel_sundef_pos_range o n m_t m_s:
    (n <> 0)%N ->
    all_not_sundef (lookup_all_index o n m_s SUndef) = true ->
    mem_byte_rel m_t m_s -∗
    (∀ i, ⌜0 ≤ i⌝ -∗
    ⌜i < N.to_nat n⌝ -∗
    ∃ v v', ⌜lookup (o + i)%Z m_t = Some v'⌝ ∗ ⌜lookup (o + i)%Z m_s = Some v⌝ ∗ val_rel v' v).
  Proof.
    rewrite /lookup_all_index.
    remember (N.to_nat n). intros Hnz Hundef.
    assert (Hpos: n0 > 0) by lia.
    clear n Heqn0 Hnz. rename n0 into n.
    rewrite /mem_byte_rel.
    iIntros "(#H & %Hn)".
    iIntros (? Hbl Hbu).

    destruct n; [ lia | cbn].

    destruct (lookup (o + i)%Z m_s) eqn: H.
    { iSpecialize ("H" $! _ _ H).
      iDestruct "H" as (??) "H".
      iExists _, _; by do 2 (iSplitL ""; [ done | ]). }
    { specialize (Hn _ H).

      rewrite forallb_forall in Hundef.
      setoid_rewrite in_map_iff in Hundef.
      assert (∃ x0 ,
                match lookup x0 m_s with
                | Some val => val
                | None => SUndef
                end = SUndef ∧ In x0 (Zseq o (S n))).
      { exists (o + i)%Z. rewrite H; split; [ done | ].
        apply In_Zseq_bounds; lia. }
      specialize (Hundef _ H0).
      inversion Hundef. }
  Qed.

  Fixpoint int_of_bytes' (bytes: list SByte) : Z :=
    match bytes with
    | nil => 0
    | Byte b :: l' => Integers.Byte.unsigned b + int_of_bytes' l' * 256
    | _ :: l' => int_of_bytes' l'
    end.

  Lemma int_of_bytes_int_of_bytes' bytes :
    int_of_bytes (sbyte_list_to_byte_list bytes) = int_of_bytes' bytes.
  Proof.
    induction bytes; eauto.
    cbn. destruct a; cbn in *.
    { cbn in *. rewrite IHbytes; eauto. }
    all : eauto.
  Qed.

  Ltac to_int_of_bytes' :=
    rewrite /deserialize_sbytes_defined /sbyte_list_to_Z int_of_bytes_int_of_bytes'.

  Lemma mem_byte_rel_read m_t m_s o n:
    mem_byte_rel m_t m_s -∗
    (∀ i : nat,
        ⌜0 ≤ i⌝ -∗
        ⌜i < N.to_nat n⌝ -∗
        ∃ v0 v'0 : SByte, ⌜lookup (o + i)%Z m_t = Some v'0⌝
          ∗ ⌜lookup (o + i)%Z m_s = Some v0⌝ ∗ val_rel v'0 v0) -∗
    ⌜int_of_bytes' (lookup_all_index o n m_t SUndef) =
      int_of_bytes' (lookup_all_index o n m_s SUndef)⌝.
  Proof.
    rewrite /lookup_all_index.
    remember (N.to_nat n). clear n Heqn0. rename n0 into n.
    rewrite /mem_byte_rel.
    iIntros "(#Hr & %Hn) #Hbounds".

    iInduction n as [| n] "IHn" forall (o); [ done | cbn].

    iPoseProof ("Hbounds" $! 0 (Nat.le_refl _) (Nat.lt_0_succ _)) as (????) "H".

    rewrite Z.add_0_r in H H0; rewrite H H0.

    iAssert
      (∀ i0 : nat,
        ⌜0 ≤ i0⌝ -∗
        ⌜i0 < n⌝ -∗
        ∃ v0 v'0 : SByte,
          ⌜lookup (Z.succ o + i0)%Z m_t = Some v'0⌝ ∗
          ⌜lookup (Z.succ o + i0)%Z m_s = Some v0⌝ ∗ val_rel v'0 v0)%I as "HP".
    { iIntros (???).
      assert (Hb1 : 0 ≤ S i0) by lia.
      assert (Hb2 : S i0 < S n) by lia.
      iSpecialize ("Hbounds" $! (S i0) Hb1 Hb2).

      assert (He : (Z.succ o + i0)%Z = (o + S i0)%Z) by lia.
      by rewrite He. }
    iSpecialize ("IHn" with "HP").
    iDestruct "IHn" as "%Heq". rewrite Heq.

    destruct v0.
    - iDestruct (val_rel_byte_inv_r with "H") as "%Hb"; by subst.
    - iDestruct (val_rel_ptr_inv_r with "H") as (??) "Hp"; by subst.
    - iDestruct (val_rel_ptrfrag_inv_r with "H") as "%Hb"; by subst.
    - iDestruct (val_rel_sundef_inv_r with "H") as "%Hb"; by subst.
  Qed.

  Lemma drop_zseq_lookup_all_index {A} n sz m o def:
    drop (A := A) n
      (map (λ x , match lookup x m with
                          | Some val => val
                          | None => def
                          end) (Zseq o (n + N.to_nat sz))) =
    lookup_all_index (o + n) sz m def.
  Proof.
    rewrite /lookup_all_index.
    revert sz m o def.
    induction n.
    { intros; cbn; by rewrite Z.add_0_r. }
    intros.
    assert (S n + N.to_nat sz = S (n + N.to_nat sz)) by lia.
    cbn. rewrite IHn.
    assert (Z.succ o + n = o + S n)%Z by lia.
    by rewrite H0.
  Qed.

  Lemma drop_lookup_all_index {A} n sz m o def:
    drop (A := A) (N.to_nat n)
      (lookup_all_index o (N.of_nat (S sz) * n) m def) =
    lookup_all_index (o + N.to_nat n) (N.of_nat sz * n) m def.
  Proof.
    rewrite -drop_zseq_lookup_all_index. rewrite /lookup_all_index.
    do 3 f_equiv; lia.
  Qed.

  Lemma array_parse_length τ sz m o:
    length
      ((fix array_parse (count byte_sz : nat) (bytes : list SByte)
       {struct count} : list uvalue :=
        match count with
        | 0 => []
        | S n => deserialize_sbytes_defined (take byte_sz bytes) τ
                  :: array_parse n byte_sz (drop byte_sz bytes)
        end)
        sz
        (N.to_nat (sizeof_dtyp τ))
        (lookup_all_index o (N.of_nat sz * sizeof_dtyp τ) m SUndef)) = sz.
  Proof.
    revert τ m o.
    induction sz; eauto.
    intros; cbn; f_equiv.
    destruct (N.to_nat (sizeof_dtyp τ)) eqn : Hτ.
    { cbn in *.
      assert (sizeof_dtyp τ = 0%N) by lia. rewrite H.
      rewrite drop_0.
      specialize (IHsz τ). rewrite Hτ in IHsz.
      rewrite H in IHsz; cbn in IHsz.
      by rewrite N.mul_0_r in IHsz. }
    { cbn in *.
      specialize (IHsz τ).
      destruct (sizeof_dtyp τ); inversion Hτ; cbn in *.
      assert (N.of_nat (S sz) * N.pos p =
                N.pos p + (N.of_nat sz * N.pos p))%N by lia.
      rewrite H; clear H.
      pose proof
        (@drop_zseq_lookup_all_index SByte (N.to_nat (N.pos p))%nat
          (N.of_nat sz * N.pos p)).
      rewrite /lookup_all_index.
      assert (N.to_nat (N.pos p) + N.to_nat (N.of_nat sz * N.pos p) =
          (N.to_nat (N.pos p + N.of_nat sz * N.pos p))) by lia.
      rewrite -H1.
      rewrite H. apply IHsz. }
  Qed.

  Lemma zseq_app_ge n o a:
    n ≤ a ->
    (Zseq o a = (Zseq o n) ++ (Zseq (o + n) (a - n)))%list.
  Proof.
    intros. revert a o H.
    induction n; intros; cbn.
    { by rewrite Z.add_0_r Nat.sub_0_r. }
    destruct a; [ lia | ]; cbn.
    f_equiv. rewrite IHn; [ | lia].
    f_equiv.
    assert (Z.succ o + n = o + S n)%Z by lia.
    by rewrite H0.
  Qed.

  Lemma map_zseq_app B f o a n:
    n ≤ a ->
    map (B := B) f (Zseq o a) =
      (map f (Zseq o n) ++ map f (Zseq (o + n) (a - n)))%list.
  Proof.
    intros.
    rewrite -map_app.
    rewrite <-zseq_app_ge; [ | done]. done.
  Qed.

  Lemma drop_lookup_all_index_fold o m fields n a:
    n ≤ a ->
    drop n
      (lookup_all_index o
        (fold_left (λ (acc : N) (x : dtyp), (acc + sizeof_dtyp x)%N) fields (N.of_nat a)) m SUndef) =
    lookup_all_index (o + n)
        (fold_left (λ (acc : N) (x : dtyp), (acc + sizeof_dtyp x)%N) fields (N.of_nat (a - n))) m SUndef.
  Proof.
    intros.
    revert o n a H.

    induction fields; intros.
    { intros; cbn. rewrite /lookup_all_index.
      rewrite Nat2N.id.
      assert (n = length (map (λ x, match lookup x m with
                             | Some val => val
                             | None => SUndef
                             end) (Zseq o n))).
      { rewrite map_length Zseq_length. lia. }

      rewrite {1}H0.
      setoid_rewrite map_zseq_app at 2; [ | apply H].
      setoid_rewrite drop_app; cbn.
      f_equiv.
      rewrite Nat2N.id; cbn; done.
    }
    { cbn.
      assert
        (Heq1:
          (N.of_nat a0 + sizeof_dtyp a =
            N.of_nat (a0 + N.to_nat (sizeof_dtyp a)))%N).
      { by rewrite Nat2N.inj_add N2Nat.id. }
      assert
        (Heq2 :
          (N.of_nat (a0 - n) + sizeof_dtyp a =
            (N.of_nat ((a0 + N.to_nat (sizeof_dtyp a)) - n)))%N).
      { rewrite !Nat2N.inj_sub Nat2N.inj_add N2Nat.id; lia. }
      rewrite Heq1 Heq2.
      rewrite IHfields; try done. lia. }
  Qed.

  Lemma drop_lookup_all_index_fold_0 o m fields n:
    drop (N.to_nat n)
      (lookup_all_index o
        (fold_left (λ (acc : N) (x : dtyp), (acc + sizeof_dtyp x)%N) fields n) m SUndef) =
    lookup_all_index (o + (N.to_nat n))
        (fold_left (λ (acc : N) (x : dtyp), (acc + sizeof_dtyp x)%N) fields 0%N) m SUndef.
  Proof.
    rewrite -{2}(N2Nat.id n).
    remember (N.to_nat n).
    rewrite drop_lookup_all_index_fold; [ | lia].
    rewrite Nat.sub_diag. by cbn.
  Qed.

  Lemma struct_parse_length m fields o:
    length
      ((fix struct_parse (typ_list : list dtyp) (bytes : list SByte) {struct typ_list} : list uvalue :=
          match typ_list with
          | [] => []
          | t :: tl =>
              deserialize_sbytes_defined (take (N.to_nat (sizeof_dtyp t)) bytes) t
              :: struct_parse tl (drop (N.to_nat (sizeof_dtyp t)) bytes)
          end) fields
        (lookup_all_index o (fold_left (λ (acc : N) (x : dtyp), (acc + sizeof_dtyp x)%N) fields 0%N) m SUndef)) =
      length fields.
  Proof.
    revert m o.
    induction fields; [ done | ].
    intros; cbn; f_equiv.
    rewrite N.add_0_l.
    rewrite drop_lookup_all_index_fold_0.
    by rewrite IHfields.
  Qed.

  Lemma take_lookup_all_index {A} m n n' o def:
    take (A := A) (N.to_nat n)
      (lookup_all_index o (n + n') m def) =
    lookup_all_index o n m def.
  Proof.
    rewrite /lookup_all_index.
    remember (N.to_nat n).
    rewrite -(N2Nat.id n). rewrite -Heqn0.
    clear n Heqn0.
    revert m o def.
    rename n0 into n.
    induction n; [ done | ].
    cbn in *. intros.
    rewrite N2Nat.inj_add positive_N_nat SuccNat2Pos.id_succ.
    rewrite plus_Sn_m; cbn.
    f_equiv.
    erewrite <- IHn. do 3 f_equiv.
    rewrite N2Nat.inj_add.
    rewrite !Nat2N.id. f_equiv.
  Qed.

  Lemma array_lookup_inv k τ sz m o v:
    (fix array_parse (count byte_sz : nat) (bytes : list SByte)
       {struct count} : list uvalue :=
      match count with
      | 0 => []
      | S n => deserialize_sbytes_defined (take byte_sz bytes) τ
                :: array_parse n byte_sz (drop byte_sz bytes)
      end)
      sz
      (N.to_nat (sizeof_dtyp τ))
      (lookup_all_index o (N.of_nat sz * sizeof_dtyp τ) m SUndef) !! k =
       Some v ->
    let τ_size := sizeof_dtyp τ in
    let off := (o + Z.of_nat (k * N.to_nat τ_size))%Z in
    (* [k] is within bounds of the array *)
    0 ≤ k /\ k < sz /\
    (* v is the serialized bytes at the right index *)
    v = deserialize_sbytes_defined (lookup_all_index off (sizeof_dtyp τ) m SUndef) τ.
  Proof.
    revert k τ m o v.
    induction sz; [ done | ].
    intros.
    split; [ lia | ].
    rewrite drop_lookup_all_index in H.
    destruct k eqn: Hk.
    { split; [ lia | ]. unfold off.
      assert (0 * N.to_nat τ_size = 0)%nat by lia; rewrite H0; clear H0.
      assert (N.of_nat (S sz) = N.succ (N.of_nat sz)) by lia.
      rewrite H0 in H; clear H0.
      inversion H.
      assert (N.succ (N.of_nat sz) * sizeof_dtyp τ =
                sizeof_dtyp τ + N.of_nat sz * sizeof_dtyp τ)%N by lia.
      rewrite H0; clear H0.
      f_equiv. rewrite take_lookup_all_index.
      by rewrite Z.add_0_r. }
    { cbn in *.
      specialize (IHsz _ _ _ _ _ H).
      destruct IHsz as (?&?&?).
      split; [ lia | ].
      unfold off. rewrite H2. do 2 f_equiv.
      lia. }
  Qed.

  Lemma array_lookup_inv1 k τ (sz : N) m o v:
    (fix array_parse (count byte_sz : nat) (bytes : list SByte)
       {struct count} : list uvalue :=
      match count with
      | 0 => []
      | S n => deserialize_sbytes_defined (take byte_sz bytes) τ
                :: array_parse n byte_sz (drop byte_sz bytes)
      end)
      (N.to_nat sz)
      (N.to_nat (sizeof_dtyp τ))
      (lookup_all_index o (sz * sizeof_dtyp τ) m SUndef) !! k =
       Some v ->
    let τ_size := sizeof_dtyp τ in
    let off := (o + Z.of_nat (k * N.to_nat τ_size))%Z in
    (* [k] is within bounds of the array *)
    0 ≤ k /\ k < N.to_nat sz /\
    (* v is the serialized bytes at the right index *)
    v = deserialize_sbytes_defined (lookup_all_index off (sizeof_dtyp τ) m SUndef) τ.
  Proof.
    intros. rewrite -(N2Nat.id sz) in H.
    remember (N.to_nat sz).
    clear sz Heqn. rename n into sz.
    eapply array_lookup_inv; rewrite -H.
    repeat f_equiv.
    by rewrite Nat2N.id.
  Qed.

  Lemma drop_In_cons:
    forall A k (l : list A) default,
      k < length l ->
      drop k l = nth k l default :: drop (S k) l.
  Proof.
    intros.
    apply lookup_lt_is_Some in H.
    destruct H.
    erewrite drop_S; eauto.
    rewrite H.
    apply nth_lookup_Some with (d := default) in H.
    rewrite H; done.
  Qed.

  Lemma struct_lookup_inv k (fields : list dtyp) m o v:
    (fix struct_parse
      (typ_list : list dtyp) (bytes : list SByte) {struct typ_list} : list uvalue :=
        match typ_list with
        | [] => []
        | t :: tl =>
            deserialize_sbytes_defined
              (take (N.to_nat (sizeof_dtyp t)) bytes) t
            :: struct_parse tl (drop (N.to_nat (sizeof_dtyp t)) bytes)
        end)
      fields
      (lookup_all_index o
          (fold_left (λ (acc : N) (x : dtyp), (acc + sizeof_dtyp x)%N)
            fields 0%N) m SUndef) !! k = Some v ->
    let τ := List.nth k fields DTYPE_Void in
    let off := (o +
                  Z.of_N
                  (fold_left (λ (acc : N) (x : dtyp), (acc + sizeof_dtyp x)%N) (take k fields) 0%N))%Z in
    (* [k] is within bounds of the fields lookup *)
    0 <= k /\ k < length fields /\
    (* v is the serialized bytes at the right index *)
    v = deserialize_sbytes_defined (lookup_all_index off (sizeof_dtyp τ) m SUndef) τ.
  Proof.
    revert k m o v.
    induction fields; [ done | ].
    cbn; intros.
    split; [ lia | ].
    destruct k eqn: Hk.
    { split; [ lia | ].
      inversion H; cbn in H.
      rewrite take_0; cbn.
      rewrite Z.add_0_r N.add_0_l.
      rewrite fold_sizeof.
      by rewrite take_lookup_all_index. }
    { cbn in *.
      rewrite N.add_0_l in H.
      rewrite drop_lookup_all_index_fold_0 in H.
      specialize (IHfields _ _ _ _ H).
      destruct IHfields as (?&?&?).
      split; [ lia |].
      rewrite H2. do 2 f_equiv.
      rewrite N.add_0_l.
      setoid_rewrite fold_sizeof at 2. lia. }
  Qed.

  Lemma fold_left_size_take_drop k fields:
    ((fold_left (λ (acc : N) (x : dtyp), (acc + sizeof_dtyp x)%N) (take k fields) 0%N) +
      fold_left (λ (acc : N) (x : dtyp), (acc + sizeof_dtyp x)%N) (drop k fields) 0%N
      = (fold_left (λ (acc : N) (x : dtyp), (acc + sizeof_dtyp x)%N) fields 0%N))%N.
  Proof.
    intros.
    rewrite -{3}(take_drop k fields).
    rewrite fold_left_app.
    by setoid_rewrite fold_sizeof at 3.
  Qed.

  Lemma uval_rel_lift dv dv' uv uv':
    concretize_uvalue uv = Monad.ret dv ->
    concretize_uvalue uv' = Monad.ret dv' ->
    dval_rel dv dv' -∗
    uval_rel uv uv'.
  Proof.
    rewrite /uval_rel.
    iIntros (??) "#H".
    iIntros (??).
    iExists dv; iSplitL ""; [done | ].
    rewrite H1 in H0; inversion H0; by subst.
  Qed.

  Lemma dval_rel_lift v_t v_s:
    dval_rel v_t v_s -∗
    uval_rel (dvalue_to_uvalue v_t) (dvalue_to_uvalue v_s).
  Proof.
    iIntros "Hd" (??).
    rewrite concretize_uvalue_dvalue_to_uvalue in H; inversion H; subst.
    rewrite concretize_uvalue_dvalue_to_uvalue; iExists _; iSplitL ""; done.
  Qed.

  Lemma val_rel_implies_val_rel_prop v v' :
    val_rel v v' -∗ ⌜val_rel_prop v v'⌝.
  Proof.
    iIntros "H". rewrite /val_rel.
    destruct v, v'; try done.
  Qed.

  Lemma forall_val_rel_implies_val_rel_prop v v':
    Forall2 val_rel v v' -∗
    ⌜List.Forall2 val_rel_prop v v'⌝.
  Proof.
    rewrite /Forall2.
    rewrite big_sepL2_forall.
    iIntros "(%Hl & #H)".
    iInduction v as [|] "IH" forall (v' Hl).
    { destruct v'; try done. }

    destruct v'; try done.
    rewrite Forall2_cons.
    iPoseProof "H" as "H'".
    iSpecialize ("H" $! 0 _ _ eq_refl eq_refl).
    iDestruct (val_rel_implies_val_rel_prop with "H") as "%H".
    iSplit; auto.

    iApply "IH"; auto.
    iModIntro.
    iIntros (?????).
    iApply ("H'" $! (S k)); eauto.
  Qed.

  Lemma dval_rel_implies_val_rel_prop v v':
    dval_rel v v' -∗
    ⌜List.Forall2 val_rel_prop (serialize_dvalue v) (serialize_dvalue v')⌝.
  Proof.
    iIntros "Hdv".
    iPoseProof (dval_rel_implies_val_rel with "Hdv") as "Hv".
    iApply (forall_val_rel_implies_val_rel_prop with "Hv").
  Qed.

  Lemma uval_rel_implies_obs_val v_t v_s:
    ⊢ uval_rel v_t v_s -∗ ⌜obs_val v_t v_s⌝.
  Proof.
    iIntros "H". rewrite /uval_rel /obs_val.
    iIntros (????).
    iSpecialize ("H" $! _ a0).
    iDestruct "H" as (??) "H".
    rewrite H in a2; inv a2.
    iApply (dval_rel_implies_val_rel_prop with "H").
  Qed.

  Lemma mem_byte_rel_implies_read_rel m_t m_s :
    Addr.null ↔h Addr.null -∗
    mem_byte_rel m_t m_s -∗
    mem_read_rel m_t m_s.
  Proof.
    iIntros "#Hnull #H" (???).

    rewrite /read_in_mem_block /deserialize_sbytes.

    destruct (all_not_sundef (lookup_all_index o (sizeof_dtyp τ) m_s SUndef))
      eqn: Hundef; cycle 1.
    { (* Everything is undef in source, i.e. uninitialized *)
      iDestruct (mem_byte_rel_sundef_false _ _ _ _ Hundef with "H") as "%Hundef_t".
      rewrite Hundef_t.
      by iApply uval_rel_undef. }

    iDestruct (mem_byte_rel_sundef _ _ _ _ Hundef with "H") as "%Hundef_t".
    rewrite Hundef_t.
    pose proof (dtyp_WF_size_nonzero _ H) as Hsz.
    iDestruct (mem_byte_rel_sundef_pos_range _ _ _ _ Hsz Hundef with "H") as "Hvr".
    clear Hundef Hundef_t; subst.

    iRevert "Hvr H".

    iInduction τ as [] "IH" using dtyp_ind forall (H m_s m_t o);
      try solve [inversion H]; iIntros "#Hvr #H".

    (* Arithmetic cases *)
    { inversion H; subst.
      all: do 2 to_int_of_bytes'; subst;
        iApply uval_rel_lift; eauto;
        rewrite dval_rel_unfold /dval_relF;
        rewrite /sizeof_dtyp;
        iPoseProof (mem_byte_rel_read with "H Hvr") as "%H'";
        iPureIntro; by rewrite H'. }

    2,3:
      do 2 to_int_of_bytes';
      subst; iApply uval_rel_lift; eauto;
      rewrite dval_rel_unfold /dval_relF;
      rewrite /sizeof_dtyp;
      iPoseProof (mem_byte_rel_read with "H Hvr") as "%H'";
      iPureIntro; by rewrite H'.


    { (* Pointer *)
      cbn.

      assert (HP: (8 = N.succ 7)%N) by lia. rewrite !HP.
      assert (0 ≤ 0) by lia.
      assert (0 < S (Pos.to_nat 7)) by lia.
      iSpecialize ("Hvr" $! 0 H0 H1); clear H0 H1.
      iDestruct "Hvr" as (????) "Hv".
      rewrite /lookup_all_index; cbn.
      rewrite !N2Nat.inj_succ; cbn.
      rewrite Z.add_0_r in H0 H1; rewrite H0 H1; clear H0 H1.

      iDestruct "H" as "(H & Hb)".
      destruct v eqn : Hes; subst.
      - iDestruct (val_rel_byte_inv_r with "Hv") as "%Hb"; subst.
        iApply uval_rel_lift; eauto;
        iApply dval_rel_none.
      - iDestruct (val_rel_ptr_inv_r with "Hv") as (??) "Hp"; subst.
        iApply uval_rel_lift; eauto;
        by iApply dval_rel_addr.
      - iDestruct (val_rel_ptrfrag_inv_r with "Hv") as "%Hb"; subst.
        iApply uval_rel_lift; eauto;
        iApply dval_rel_none.
      - iDestruct (val_rel_sundef_inv_r with "Hv") as "%Hb"; subst.
        iApply uval_rel_lift; eauto;
        iApply dval_rel_none. }

    (* Inductive cases *)

    { (* Array *)
      inversion H; subst.
      pose proof (dtyp_WF_size_nonzero _ H2) as Hsz'.
      iSpecialize ("IH" $! Hsz' H2).
      cbn.
      iApply uval_rel_array.
      rewrite /Forall2 big_sepL2_forall.
      iSplitL "".
      { iPureIntro.
        pose proof (array_parse_length τ (N.to_nat sz) m_t o).
        rewrite N2Nat.id in H0. rewrite H0.
        pose proof (array_parse_length τ (N.to_nat sz) m_s o).
        rewrite N2Nat.id in H1. by rewrite H1. }
      { iIntros (?????); subst.
        pose proof (array_lookup_inv1 _ _ _ _ _ _ H1).
        pose proof (array_lookup_inv1 _ _ _ _ _ _ H0).
        destruct H4 as (Hbound1&Hbound2&Hx2).
        destruct H5 as (Hbound1'&Hbound2'&Hx1).
        rewrite Hx1 Hx2.
        iApply "IH"; [ | done].
        iModIntro. iIntros (???).
        assert (Hb' : 0 ≤ k * N.to_nat (sizeof_dtyp τ) + i) by lia.
        assert (Hb'' : k * N.to_nat (sizeof_dtyp τ) + i <
                         N.to_nat (sz * sizeof_dtyp τ)).
        { clear Hb' Hx2 Hx1 H0 H1.

          rewrite N2Nat.inj_mul.
          remember (N.to_nat (sizeof_dtyp τ)); remember (N.to_nat sz).
          clear τ Heqn H Hsz H2 H3 Hsz' Hbound1 Hbound2 sz Heqn0.
          rename n into τ; rename n0 into sz.

          assert (Hb1: 0 <= k < sz) by lia.
          assert (Hb2: 0 <= i < τ) by lia. clear -Hb1 Hb2.

          assert (S k * τ ≤ sz * τ).
          { rewrite -Nat.mul_le_mono_pos_r; lia. }

          eapply Nat.lt_le_trans; [ | apply H].
          lia. }

        iSpecialize ("Hvr" $! ((k * N.to_nat (sizeof_dtyp τ))%nat + i) Hb' Hb'').
        iDestruct "Hvr" as (????) "Hv".
        iExists v, v'. iSplitL "".
        { iPureIntro; rewrite -H6; f_equiv; lia. }
        iSplitL "".
        { iPureIntro; rewrite -H7; f_equiv; lia. }
        done. } }

    { (* Structs *)
      inversion H; subst. cbn.
      iApply uval_rel_struct.
      rewrite /Forall2 big_sepL2_forall.
      iSplitL "".
      { iPureIntro.
        pose proof (struct_parse_length m_s fields o).
        rewrite H0.
        pose proof (struct_parse_length m_t fields o).
        by rewrite H3. }

      { iIntros (?????); subst.
        pose proof (struct_lookup_inv _ _ _ _ _ H3).
        pose proof (struct_lookup_inv _ _ _ _ _ H0).
        destruct H4 as (Hbound1&Hbound2&Hx2).
        destruct H5 as (Hbound1'&Hbound2'&Hx1).
        rewrite Hx1 Hx2.
        iApply "IH"; try done.
        { iPureIntro; by eapply nth_In. }
        { iPureIntro.
          rewrite Forall_nth in H2.
          Unshelve. 2 : exact DTYPE_Void.
          by apply dtyp_WF_size_nonzero, H2. }
        { iPureIntro; rewrite Forall_nth in H2; by eapply H2. }

        iModIntro. iIntros (???).
        assert
          (Hb' :
            (0 ≤
              N.to_nat (fold_left (λ (acc : N) (x : dtyp), (acc + sizeof_dtyp x)%N) (take k fields) 0%N) + i)%nat)
                 by lia.
        assert (Hb'' :
            (N.to_nat (fold_left (λ (acc : N) (x : dtyp), (acc + sizeof_dtyp x)%N) (take k fields) 0%N) + i) <
            N.to_nat (fold_left (λ (acc : N) (x : dtyp), (acc + sizeof_dtyp x)%N) fields 0%N)).
        { assert (N.to_nat (fold_left (λ (acc : N) (x : dtyp), (acc + sizeof_dtyp x)%N) (take k fields) 0%N) + i <
            N.to_nat (fold_left (λ (acc : N) (x : dtyp), (acc + sizeof_dtyp x)%N) (take k fields) 0%N) +
            N.to_nat (sizeof_dtyp (nth k fields DTYPE_Void))) by lia.
          eapply Nat.lt_le_trans; [ apply H6 | ].
          clear -H1 H2 Hbound2'.
          rewrite -(fold_left_size_take_drop k fields).
          rewrite N2Nat.inj_add.
          rewrite -PeanoNat.Nat.add_le_mono_l.
          rewrite (drop_In_cons _ _ _ DTYPE_Void); eauto.
          cbn. rewrite N.add_0_l.
          rewrite fold_sizeof. lia. }

        iClear "IH".
        iSpecialize ("Hvr" $! _ Hb' Hb'').
        iDestruct "Hvr" as (????) "Hv".
        iExists v, v'. iSplitL "".
        { iPureIntro; rewrite -H6; f_equiv; lia. }
        iSplitL "".
        { iPureIntro; rewrite -H7; f_equiv; lia. }
        done. } }
  Qed.

  Lemma mem_byte_rel_write_stable v_t v_s dv_t dv_s o:
    mem_byte_rel v_t v_s -∗
    dval_rel dv_t dv_s -∗
    mem_byte_rel
      (add_all_index (serialize_dvalue dv_t) o v_t)
      (add_all_index (serialize_dvalue dv_s) o v_s).
  Proof.
    rewrite /mem_byte_rel.
    iIntros "(#Hs& %Hn) #Hd".

    iPoseProof
      (dval_rel_length_serialize_dvalue with "Hd") as "%Hlen".
    iSplitL ""; cycle 1.
    { iIntros (??).
      pose proof (lookup_add_None _ _ _ _ a0) as Hnv.
      specialize (Hn _ Hnv).

      (* Case analysis on dvalue length for [dv_s]
          if it is 0, use [dval_rel_length_0] and conclude *)
      (* Otherwise use [lookup_add_None_range] to see that
            the lookup is always out of range anyways using
            [lookup_add_all_index_out] *)
      destruct (serialize_dvalue dv_s) eqn: Hdv_s.
      { assert
          (Hdv_s_length:
            length (serialize_dvalue dv_s) = 0)
          by (rewrite Hdv_s; by cbn). cbn in *.
        apply nil_length_inv in Hlen. rewrite Hlen; by cbn. }
      { assert (H_nnil : (s :: l) <> nil) by (intros Hnil; inversion Hnil).
        pose proof (lookup_add_None_range _ _ _ _ H_nnil a0) as Hrange.
        rewrite lookup_add_all_index_out; [ done | ].
        rewrite Zlength_correct. lia. } }

    { iIntros (??) "%H".
      pose proof (lookup_add_Some_inv _ _ _ _ _ SUndef H) as Hc.
      destruct Hc as [Hinbounds | Houtbounds].
      { destruct Hinbounds as (Hbounds & Hv).
        subst. setoid_rewrite lookup_add_all_index_in; cycle 1.
        { rewrite Zlength_correct; lia. }
        { apply list_nth_z_nth; lia. }
        Unshelve. 2 : exact SUndef.
        iExists _; iSplitL "".
        { iPureIntro; reflexivity. }
        iApply (dval_rel_val_rel_index with "Hd"); eauto. }
      { destruct Houtbounds.
        setoid_rewrite lookup_add_all_index_out; cycle 1.
        { rewrite Zlength_correct. lia. }
        by iApply "Hs". } }
  Qed.

End mem_rel.
