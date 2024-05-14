From Coq Require Import List.
Import ListNotations.
From stdpp Require Import decidable.
From iris Require Import bi.bi.
From iris.base_logic.lib Require Import ghost_map.
From iris.proofmode Require Import proofmode.
From iris Require Import algebra.local_updates algebra.gmap.
From iris.prelude Require Import options.
Import bi.

From ITree Require Import ITree Eq.Eqit Events.State Events.StateFacts
     Eq.Rutt.
From ExtLib Require Import Monads.
From Vellvm.Syntax Require Import LLVMAst.
From Vellvm.Semantics Require Import
     InterpretationStack LLVMEvents.
From Vellvm.Handlers Require Import Handlers.
From Vellvm.Analysis Require Import Dom.

Require Import List Equalities Orders RelationClasses Lia.
Require Import FSets FMaps.
Import ListNotations.
From Vellvm Require Import Utils.Util.

From Vellvm.Analysis Require Import DomId.

Import CFG.
Import DynamicTypes.

(* Example sketched in the introduction *)
Definition pre_term : terminator dtyp:=
  TERM_Br_1 (Name "loop").

Definition pre : block dtyp:= {|
  blk_id := Name "pre";
  blk_phis := [];
  blk_code := [];
  blk_term := pre_term;
  blk_comments := None |}.

Definition loop_code : code dtyp:=
[(IId (Raw 2), INSTR_Load true (DTYPE_I 32)
                 (DTYPE_I 32, EXP_Ident (ID_Local (Raw 0))) None);
 (IId (Raw 3), INSTR_Call
                 (DTYPE_I 32, EXP_Ident (ID_Local (Name "foo")))
                 [(DTYPE_I 32, EXP_Ident (ID_Local (Raw 0)))]
                 [FNATTR_Readonly]);
 (IId (Raw 4), INSTR_Op
                (OP_ICmp Sle (DTYPE_I 32)
                   (EXP_Ident (ID_Local (Raw 2)))
                   (EXP_Ident (ID_Local (Raw 3)))))].

Definition loop_term : terminator dtyp:=
  TERM_Br (DTYPE_I 1, EXP_Ident (ID_Local (Raw 4)))
    (Name "loop") (Name "end").

Definition loop : block dtyp:= {|
  blk_id := Name "loop";
  blk_phis := [];
  blk_code := loop_code;
  blk_term := loop_term;
  blk_comments := None |}.

Definition end_block : block dtyp:= {|
  blk_id := Name "end";
  blk_phis := [];
  blk_code := [];
  blk_term := TERM_Ret (DTYPE_I 32, EXP_Ident (ID_Local (Raw 3)));
  blk_comments := None |}.

Definition bar_ocfg : ocfg dtyp := [pre; loop; end_block].

Definition bar : cfg dtyp := {|
    init := Name "pre";
    blks := bar_ocfg;
    args := [(Raw 0)] |}.

Definition pre_term' : terminator dtyp :=
  TERM_Br_1 (Name "loop").

Definition pre' : block dtyp := {|
  blk_id := Name "pre";
  blk_phis := [];
  blk_code :=
    [(IId (Raw 2), INSTR_Load true (DTYPE_I 32)
                 (DTYPE_I 32, EXP_Ident (ID_Local (Raw 0))) None)];
  blk_term := pre_term;
  blk_comments := None |}.

Definition loop_code' : code dtyp :=
[(IId (Raw 3), INSTR_Call
                 (DTYPE_I 32, EXP_Ident (ID_Local (Name "foo")))
                 [(DTYPE_I 32, EXP_Ident (ID_Local (Raw 0)))] []);
 (IId (Raw 4), INSTR_Op
                (OP_ICmp Sle (DTYPE_I 32)
                   (EXP_Ident (ID_Local (Raw 2)))
                   (EXP_Ident (ID_Local (Raw 3)))))].

Definition loop_term' : terminator dtyp :=
  TERM_Br (DTYPE_I 1, EXP_Ident (ID_Local (Raw 4)))
    (Name "loop") (Name "end").

Definition loop' : block dtyp := {|
  blk_id := Name "loop";
  blk_phis := [];
  blk_code := loop_code';
  blk_term := loop_term';
  blk_comments := None |}.

Definition end_block' : block dtyp := {|
  blk_id := Name "end";
  blk_phis := [];
  blk_code := [];
  blk_term := TERM_Ret (DTYPE_I 32, EXP_Ident (ID_Local (Raw 3)));
  blk_comments := None |}.

Definition bar_ocfg' : ocfg dtyp := [pre'; loop'; end_block'].

Definition bar' : cfg dtyp := {|
    init := Name "pre";
    blks := bar_ocfg';
    args := [(Raw 0)] |}.

#[global] Instance attr_eq_dec: EqDecision fn_attr.
Proof. solve_decision. Defined.

Definition HasAttr : fn_attr -> list fn_attr -> bool :=
  fun attr l =>
    match l with
    | nil => false
    | l =>
      foldl (fun p b =>
        p && (Coqlib.proj_sumbool (decide (b = attr)))) true l
    end.

Definition readonly_instr {T} (x : instr T) :=
  match x with
  | INSTR_Store _ _ _ _ => false
  | INSTR_Call _ _ attrs =>
      HasAttr FNATTR_Readonly attrs
  | _ => true
  end.

Definition readonly (fn : code dtyp) :=
  foldr (fun '(_, x) acc => acc && readonly_instr x) true fn.

Definition raw_id_eqb : raw_id -> raw_id -> bool :=
  fun id1 id2 =>
    match id1, id2 with
    | Name str1, Name str2 => str1 =? str2
    | Anon z1, Anon z2
    | Raw z1, Raw z2 => Z.eqb z1 z2
    | _, _ => false
   end.

Definition ident_eqb : ident -> ident -> bool :=
  fun id1 id2 =>
    match id1, id2 with
    | ID_Global id1, ID_Global id2
    | ID_Local id1, ID_Local id2 => raw_id_eqb id1 id2
    | _, _ => false
    end.

Definition contains_ident {T} : ident -> list (texp T) -> bool :=
  fun id l =>
    foldr (fun x acc =>
             match x with
              | (_, EXP_Ident id') => orb (ident_eqb id' id) acc
              | _ => acc
              end
          ) false l.

Definition dummy_instr : (instr_id * instr dtyp):= (IVoid 0, INSTR_Comment "dummy").

Fixpoint load_remove (id : ident * dtyp) (fn : code dtyp) :
  code dtyp * option (instr_id * instr dtyp) :=
  match fn with
    | [] => (nil, None)
    | (iid, i) :: tl =>
        (match iid, i with
           | IId iid, INSTR_Load _ τ (_, EXP_Ident id') _ =>
              if ident_eqb id' id.1 && dtyp_eqb id.2 τ then
                (tl, Some (IId iid, i))
              else
                let '(x, y) := load_remove id tl in
                ((IId iid, i) :: x, y)
          | _,_ =>
              let '(x, y) := load_remove id tl in
              ((iid, i) :: x, y)
         end)
  end.

Definition writes_to {A : Type}
  (l : list ident) (fn : A * instr dtyp) :=
  match fn with
  | (_, INSTR_Store _ _ (_, EXP_Ident id) _) =>
      existsb (fun x => ident_eqb x id) l
  | (_, INSTR_Store _ _ _ _) => false
  | (_, INSTR_Call _ el attrs) =>
      HasAttr FNATTR_Readonly attrs ||
      (HasAttr FNATTR_Argmemonly attrs &&
      forallb (fun id => contains_ident id el) l)
  | (_, _) => true
  end.

(* any loads that load [id] is hoisted *)
Definition hoist_load (id: ident * dtyp) (l : list ident) (fn : code dtyp) :=
  let '(fn', i) := load_remove id fn in
  match i with
  | Some x =>
      if forallb (writes_to l) fn then
        (fn', i) else (fn, None)
  | None => (fn, None)
  end.

(* Knowing that id and l stores separate pointers, see if any
  loads that load from id can be hoisted out of the loop *)
Definition licm (id : ident * dtyp) (l : list ident) (fn : code dtyp) :=
  hoist_load id l fn.

(* Eval cbv in (licm loop_code). *)

(* Simple loop creation *)
Definition make_pre pre : block dtyp := {|
  blk_id := Name "pre";
  blk_phis := [];
  blk_code := pre;
  blk_term := TERM_Br_1 (Name "body");
  blk_comments := None |}.

Definition make_body body : block dtyp := {|
  blk_id := Name "body";
  blk_phis := [];
  blk_code := body;
  blk_term := TERM_Br (DTYPE_I 1, EXP_Ident (ID_Local (Name "loop_cond")))
               (Name "body") (Name "end");
  blk_comments := None |}.

Definition make_end : block dtyp := {|
  blk_id := Name "end";
  blk_phis := [];
  blk_code := [];
  blk_term := TERM_Ret (DTYPE_I 32, EXP_Ident (ID_Local (Name "exit")));
  blk_comments := None |}.

Definition make_loop pre fn :=
  denote_ocfg [make_pre pre ; make_body fn ; make_end]
    (Name "pre", Name "pre").

(* TODO: (l : gset Z) take in a set of addresses that are not aliased. *)

(* Finding blocks within loop construct *)
Lemma find_block_pre pre fn:
  find_block [make_pre pre; make_body fn; make_end ] (Name "pre") =
    Some (make_pre pre).
Proof.
  rewrite /find_block /find.
  destruct (Eqv.eqv_dec_p (blk_id (make_pre pre)) (Name "pre")); eauto.
  exfalso. apply n.
  unfold Eqv.eqv, AstLib.eqv_raw_id; by cbn.
Qed.

Lemma find_block_body pre fn :
  find_block [make_pre pre; make_body fn; make_end ] (Name "body") =
    Some (make_body fn).
Proof.
  rewrite /find_block /find.
  destruct (Eqv.eqv_dec_p (blk_id (make_pre pre)) (Name "body")); eauto.
  { unfold Eqv.eqv, AstLib.eqv_raw_id in e; inversion e. }
  destruct (Eqv.eqv_dec_p (blk_id (make_body fn)) (Name "body")); eauto.
  exfalso. apply n0.
  unfold Eqv.eqv, AstLib.eqv_raw_id. by cbn.
Qed.

Lemma find_block_end pre fn :
  find_block [make_pre pre; make_body fn; make_end ] (Name "end") =
    Some (make_end ).
Proof.
  rewrite /find_block /find.
  destruct (Eqv.eqv_dec_p (blk_id (make_pre pre)) (Name "end")); eauto.
  { unfold Eqv.eqv, AstLib.eqv_raw_id in e; inversion e. }
  destruct (Eqv.eqv_dec_p (blk_id (make_body fn)) (Name "end")); eauto.
  { unfold Eqv.eqv, AstLib.eqv_raw_id in e; inversion e. }
  destruct (Eqv.eqv_dec_p (blk_id (make_end )) (Name "end")); eauto.
  exfalso. apply n1.
  unfold Eqv.eqv, AstLib.eqv_raw_id. by cbn.
Qed.

Lemma unfold_denote_ocfg_pre pre fn :
  let loop := [make_pre pre; make_body fn; make_end ] in
  denote_ocfg loop (Name "pre", Name "pre") ≅
    ITree.bind (denote_block (make_pre pre) (Name "pre"))
      (λ r : block_id + uvalue,
        match r with
        | inl bid_target => Tau (denote_ocfg loop (Name "pre", bid_target))
        | inr dv => Ret (inr dv)
        end).
Proof.
  intros. setoid_rewrite unfold_iter at 1.
  rewrite find_block_pre.
  rewrite bind_bind.
  eapply eq_itree_clo_bind; first done.
  intros; subst. destruct u2;
    rewrite bind_ret_l; reflexivity.
Qed.

Lemma unfold_denote_ocfg_body pre fn  n:
  let loop := [make_pre pre; make_body fn; make_end ] in
  denote_ocfg loop (n, Name "body") ≅
    ITree.bind (denote_block (make_body fn) (Name "body"))
      (λ r : block_id + uvalue,
        match r with
        | inl bid_target => Tau (denote_ocfg loop (Name "body", bid_target))
        | inr dv => Ret (inr dv)
        end).
Proof.
  intros. setoid_rewrite unfold_iter at 1.
  rewrite find_block_body.
  rewrite bind_bind.
  eapply eq_itree_clo_bind; first done.
  intros; subst. destruct u2;
    rewrite bind_ret_l; reflexivity.
Qed.

Lemma unfold_denote_ocfg_end pre fn n:
  let loop := [make_pre pre; make_body fn; make_end ] in
  denote_ocfg loop (n, Name "end") ≅
    Vis (exp_to_instr (subevent _ (LocalRead (Name "exit"))))
    (fun u => Ret (inr u)).
Proof.
  intros. setoid_rewrite unfold_iter at 1.
  rewrite find_block_end.
  cbn.
  tau_steps. eapply eqit_Vis; intros.
  setoid_rewrite TranslateFacts.translate_ret.
  setoid_rewrite bind_ret_l.
  setoid_rewrite TranslateFacts.translate_ret.
  repeat setoid_rewrite bind_ret_l.
  reflexivity.
Qed.

Lemma partition_inv_nil {A} (f : A -> bool) (l l' : list A):
  partition f l = (nil, l') -> l = l'.
Proof.
  revert l l'.
  induction l; cbn; intros; eauto.
  - by inversion H.
  - destruct (partition f l) eqn: Hpl''.
    destruct (f a) eqn : fa; try inversion H; subst.
    f_equiv. by apply IHl.
Qed.

From simuliris.vir Require Import vir fundamental.
From ITree.Props Require Import Leaf.
From ITree.Interp Require Import InterpFacts TranslateFacts.
From Equations Require Import Equations.

Definition option_to_list {A} (l : option A) : list A :=
  match l with
  | Some x => [x]
  | None => []
  end.

Opaque denote_instr.

From simuliris.simulation Require Import sim_properties reduction.
From simuliris.vir Require Import spec logical_relations instr_laws.

Lemma hoist_load_none fn id l c:
  licm id l fn = (c, None) ->
  fn = c.
Proof.
  rewrite /licm /hoist_load.
  intros; destruct_match; try done.
Qed.

Lemma ident_eqb_eq id1 id2:
  ident_eqb id1 id2 <-> id1 = id2.
Proof.
  split; intros; subst; cycle 1.
  { destruct id2; cbn; eauto;
    by rewrite raw_id_eqb_eq. }
  { destruct id1, id2; try done; cbn in H;
    rewrite raw_id_eqb_eq in H; by subst. }
Qed.

Lemma dtyp_eqb_dtyp_eq t1 t2:
  dtyp_eqb t1 t2 <-> t1 = t2.
Proof.
  rewrite /dtyp_eqb.
  split; intros; subst; eauto.
  { destruct (DynamicTypes.dtyp_eq_dec t1 t2) eqn: H'; auto.
    inv H. }
  { destruct (DynamicTypes.dtyp_eq_dec t2 t2) eqn: H'; auto. }
Qed.

Lemma hoist_load_some fn id l c i:
  licm id l fn = (c, Some i) ->
  exists idx,
    fn !! idx = Some i
    /\ c = firstn idx fn ++ skipn (S idx) fn
    /\ (forallb (writes_to l) c)
    /\ (exists iid b t2 o,
        i = (IId iid, INSTR_Load b id.2 (t2, EXP_Ident id.1) o)).
Proof.
  rewrite /licm /hoist_load.
  intros; destruct_match; try done.
  clear -H0 H1. revert id c i H0.
  induction fn; eauto; intros; try solve [inv H0].
  cbn in *; apply andb_prop in H1; destruct H1.

  destruct a; cbn in *.
  specialize (IHfn H1).
  destruct_match.

  all: try (specialize (IHfn _ _ _ H2);
    destruct IHfn as (?&?&?&?&?&?&?&?&?);
    exists (S x); cbn; split; eauto; subst;
    split; auto; repeat eexists; eauto;
    intros; eauto;
    match goal with
      | [ H' : _ ∈ _ :: _ |- _] =>
          apply elem_of_cons in H'; destruct H';
          eauto; subst;
          solve [ constructor |
                  cbn; rewrite H; auto]
    end).

  - exists 0; split; eauto. split; eauto.
    assert (id1 = id.1).
    { apply andb_true_iff in H2; destruct H2.
      apply ident_eqb_eq; by rewrite H2. }
    subst; eauto.
    apply andb_prop in H2. destruct H2.
    apply Is_true_eq_left in H3.
    rewrite dtyp_eqb_dtyp_eq in H3; subst.
    repeat eexists; eauto.

  - specialize (IHfn _ _ _ H3);
      destruct IHfn as (?&?&?&?&?&?&?&?&?);
      exists (S x); cbn; split; eauto; subst;
      split; auto; repeat eexists; eauto.
  - specialize (IHfn _ _ _ H2);
      destruct IHfn as (?&?&?&?&?&?&?&?&?);
      exists (S x0); cbn; split; eauto; subst;
      split; auto; repeat eexists; eauto.
Qed.

Notation "⎩ e ⎭" := (instr_conv e).

Tactic Notation "unfold_cat" "in" hyp(H) :=
    rewrite /resum in H;
    rewrite /ReSum_inr in H;
    rewrite /ReSum_inl in H;
    rewrite /ReSum_id in H;
    rewrite /cat in H;
    rewrite /Cat_IFun in H;
    rewrite /id_ in H;
    rewrite /inr_ in H;
    rewrite /Inr_sum1 in H;
    rewrite /inl_ /Inl_sum1 /resum /Id_IFun in H.

Ltac unfold_cat :=
    rewrite /resum ;
    rewrite /ReSum_inr ;
    rewrite /ReSum_inl ;
    rewrite /ReSum_id ;
    rewrite /cat ;
    rewrite /Cat_IFun ;
    rewrite /id_ ;
    rewrite /inr_ ;
    rewrite /Inr_sum1;
    rewrite /inl_ /Inl_sum1 /resum /Id_IFun.

Lemma denote_block_pre_prefix pre:
  denote_block (make_pre pre) (Name "pre") ≅
  _ <- (_ <- denote_phis (Name "pre") (blk_phis (make_pre pre));;
       denote_code (blk_code (make_pre pre)));;
      translate exp_to_instr (denote_terminator (blk_term (make_pre pre))).
Proof.
  rewrite /denote_block.
  by setoid_rewrite <-bind_bind at 1.
Qed.

Lemma map_monad_app_eq_itree {E}
      {A B} (f:A -> itree E B) (l0 l1:list A):
  map_monad f (l0++l1) ≅
  bs1 <- map_monad f l0;;
  bs2 <- map_monad f l1;;
  ret (bs1 ++ bs2).
Proof.
  induction l0 as [| a l0 IH]; simpl; intros.
  - cbn; rewrite bind_ret_l bind_ret_r.
    reflexivity.
  - cbn.
    setoid_rewrite IH.
    repeat setoid_rewrite bind_bind.
    setoid_rewrite bind_ret_l.
    reflexivity.
Qed.

Lemma denote_block_pre_app_prefix pre a:
  denote_block (make_pre (pre ++ a)) (Name "pre") ≅
  _ <- (_ <- denote_phis (Name "pre") (blk_phis (make_pre pre));;
       denote_code (blk_code (make_pre pre)));;
  (_ <- map_monad denote_instr a ;;
      translate exp_to_instr (denote_terminator (blk_term (make_pre pre)))).
Proof.
  rewrite /denote_block; cbn.
  repeat setoid_rewrite bind_bind.
  repeat setoid_rewrite bind_ret_l.
  rewrite map_monad_app_eq_itree.
  repeat rewrite bind_bind.
  eapply eq_itree_clo_bind; first done.
  intros; subst. rewrite bind_bind.
  eapply eq_itree_clo_bind; first done.
  intros; subst. by rewrite bind_ret_l.
Qed.

Lemma block_WF_cons_inv a fn:
  block_WF (make_body (a :: fn)) ->
  instr_WF a.2 /\ block_WF (make_body fn).
Proof.
  rewrite /make_body /block_WF; cbn.
  intros; destructb.
  rewrite andb_true_r.
  split; last by apply forallb_True in H1.
  destruct a; eauto.
Qed.

Section licm.

  Context {Σ} `{!sheapGS Σ, !checkedoutGS Σ, !heapbijGS Σ}.

  Definition local_id_rel id i_t i_s P :=
   (∃ p_t p_s v_t v_s,
     [ id := UVALUE_Addr (p_t,0)%Z ]t i_t ∗
      [ id := UVALUE_Addr (p_s,0)%Z ]s i_s ∗
      p_t ↦t v_t ∗
      p_s ↦s v_s ∗
      P v_s ∗
      dval_rel v_t v_s)%I.

  Definition local_in_scope hid i_t i_s :=
    (∃ uv1 uv2,
      [ hid := uv1 ]t i_t ∗ [ hid := uv2 ]s i_s)%I.

  Theorem licm_correct pre fn i_t i_s A_t A_s id id' τ:
    ∀ fn' hid hoisted,
      licm (ID_Local id, τ) [(ID_Local id')] fn = (fn', Some (IId hid, hoisted)) ->
      ocfg_WF [make_pre pre; make_body fn; make_end] ->
      local_id_rel id i_t i_s (fun x => ⌜dvalue_has_dtyp x τ⌝) -∗
      local_id_rel id' i_t i_s (fun _ => True) -∗
      local_in_scope hid i_t i_s -∗
      code_inv ∅ i_t i_s A_t A_s -∗
      ⎩ make_loop (pre ++ (IId hid, hoisted) :: nil ) fn' ⎭ ⪯
      ⎩ make_loop pre fn ⎭
      [[ fun e_t e_s =>
            code_inv_post ∅ i_t i_s A_t A_s∗
            ∃ v_t v_s, ⌜e_t = Ret v_t⌝ ∗ ⌜e_s = Ret v_s⌝ ∗
                        match v_t, v_s with
                          | inl (id_s, id_s'), inl (id_t, id_t') =>
                              ⌜id_s = id_t⌝ ∗ ⌜id_s' = id_t'⌝
                          | inr v_t, inr v_s => uval_rel v_t v_s
                          | _,_ => False
                        end]].
  Proof.
    iIntros (??? LICM Hsucc).
    (* An instruction was hoisted *)
    cbn in *.
    iIntros "Hid Hid' His".
    iDestruct "Hid" as (????) "(Hid_t& Hid_s& Hpt &Hps & %Hτ & #Hdv)".
    iDestruct "Hid'" as (p_t' p_s' v_t' v_s') "(Hid'_t& Hid'_s& Hpt'&Hps'& _ & #Hdv')".
    iDestruct "His" as (dv dv') "(Hhid_t & Hhid_s)".

    apply hoist_load_some in LICM.
    destruct LICM as (?&?&?&?&?&?&?&?&?); inv H2.
    assert (IWF: instr_WF (INSTR_Load x1 τ (x2, ' id ') x3)).
    { destructb. clear H3.
      rewrite /block_WF in H2.
      apply andb_prop in H2. destruct H2. cbn in H2.
      apply Is_true_eq_left in H2.
      rewrite forallb_True in H2.
      rewrite List.Forall_forall in H2.
      specialize (H2 (IId x0, (INSTR_Load x1 τ (x2, ' id ') x3))).
      apply elem_of_list_lookup_2, elem_of_list_In in H.
      specialize (H2 H). by cbn in *. }

    iIntros "CI". rewrite /make_loop.
    setoid_rewrite unfold_denote_ocfg_pre.

    rewrite !(instr_conv_bind (denote_block _ _)).
    iApply sim_expr'_bind.
    rewrite denote_block_pre_app_prefix.
    rewrite denote_block_pre_prefix.
    Opaque denote_phis.
    Opaque denote_code.
    Opaque find_block. cbn.
    repeat setoid_rewrite bind_bind.
    do 2 setoid_rewrite interp_bind.
    repeat setoid_rewrite bind_ret_l.
    setoid_rewrite translate_ret.
    setoid_rewrite interp_bind.
    setoid_rewrite interp_ret.

    iApply sim_expr'_bind.
    iApply (sim_expr'_bupd_mono with
      "[Hid_t Hid'_t Hid_s Hid'_s Hhid_t Hhid_s Hpt Hps Hpt' Hps']"); cycle 1.
    { iApply sim_expr_lift; iApply (phis_logrel_refl with "CI"). }

    cont.
    iApply sim_expr'_bind.
    iApply (sim_expr'_bupd_mono with
      "[Hid_t Hid'_t Hid_s Hid'_s Hhid_t Hhid_s Hpt Hps Hpt' Hps']"); cycle 1.
    { iApply sim_expr_lift. iApply code_logrel_refl; eauto.
      rewrite /block_WF in Hsucc;
      destructb; by rewrite H0. }

    cont.

    iDestruct "H" as (????) "CI".
    iDestruct "CI" as "(Hd_t&Hd_s&Hs_t&Hs_s&CI)".
    iDestruct (dval_rel_dvalue_has_dtyp with "Hdv") as %Hdv.
    specialize (Hdv Hτ).

    iPoseProof
      (target_instr_load_in with "Hpt Hid_t Hhid_t Hd_t Hs_t") as "Htgt"; eauto.
    { cbn in *. destructb. rewrite dtyp_WF_b_dtyp_WF in H0.
      by apply dtyp_WF_implies_is_supported. }

    iApply sim_expr'_bupd_mono; cycle 1.
    { iApply sim_expr_lift.
      rewrite /instr_conv.
      iApply reduction.target_red_sim_expr.
      { iApply reduction.target_red_bind.
        iApply (reduction.target_red_mono with
          "[Hid'_t Hid_s Hid'_s Hhid_s Hps Hpt' Hps' Hd_s Hs_s CI]"); cycle 1.
        { iApply "Htgt". iModIntro.
          iIntros "Hid_t Hx0_t Hpt Hd_t Hs_t".
          iApply reduction.target_red_base.
          Unshelve.
          3 : refine (fun x => ⌜x = Ret tt⌝ ∗ _)%I.
          2, 3 : shelve. cbn. iSplitL ""; first done.
          iCombine "Hid_t Hx0_t Hpt Hd_t Hs_t" as "H". iExact "H". }
        iIntros (?) "(%Hrt&Hid_t&Hx0_t&Hpt&Hd_t&Hs_t)".
        subst. iApply reduction.target_red_base.
        rewrite !bind_ret_l.
        iApply sim_expr_base.
        Unshelve.
        2 : refine (fun x y =>
          ⌜x = Ret (inl (Name "body"))⌝ ∗ ⌜y = Ret (inl (Name "body"))⌝
          ∗ _)%I; shelve.
        cbn; do 2 (iSplitL ""; first done).
        iCombine "Hid'_t Hid_s Hid'_s Hhid_s Hps Hpt' Hps' Hid_t Hx0_t Hpt
            CI Hd_s Hd_t Hs_s Hs_t" as "H".
        iExact "H". } }

    iIntros (??) "H".
    iDestruct "H" as (??) "H".
    subst; rewrite !bind_ret_l.
    setoid_rewrite interp_tau.
    setoid_rewrite interp_iter'.
    2 : {
      Unshelve.
      2 :
        exact (fun i => interp (λ (T : Type) (x5 : instr_E T), Vis (instrE_conv T x5) ret)
          (let
          '(bid_from, bid_src) := i in
            match
              find_block
                [make_pre
                  (pre ++ (IId x0, INSTR_Load x1 τ (x2, ' id ') x3) :: nil);
                make_body (take x fn ++ drop (S x) fn); make_end] bid_src
            with
            | Some block_src =>
                bind (denote_block block_src bid_from)
                  (λ bd : block_id + uvalue,
                    match bd with
                    | inl bid_target => ret (inl (bid_src, bid_target))
                    | inr dv => ret (inr (inr dv))
                    end)
            | None => ret (inr (inl (bid_from, bid_src)))
            end)). 2 : shelve. intros. reflexivity. }
    2 : {
      Unshelve.
      2 :
        exact (fun i =>
        interp (λ (T : Type) (x5 : instr_E T), Vis (instrE_conv T x5) ret)
          (let
          '(bid_from, bid_src) := i in
            match
              find_block [make_pre pre; make_body fn; make_end] bid_src
            with
            | Some block_src =>
                bind (denote_block block_src bid_from)
                  (λ bd : block_id + uvalue,
                    match bd with
                    | inl bid_target => ret (inl (bid_src, bid_target))
                    | inr dv => ret (inr (inr dv))
                    end)
            | None => ret (inr (inl (bid_from, bid_src)))
            end)).
      reflexivity. }

    match goal with
    | |- context[sim_expr' _
          (Tau (ITree.iter ?body1 ?index1)) (Tau (ITree.iter ?body2 ?index2))] =>
        replace (Tau (ITree.iter body1 index1)) with (guarded_iter' _ _ _ body1 index1);
        replace (Tau (ITree.iter body2 index2)) with (guarded_iter' _ _ _ body2 index2)
    end; cycle 1.
    { rewrite /guarded_iter'. reflexivity. }
    { rewrite /guarded_iter'. reflexivity. }
    { rewrite /guarded_iter'. reflexivity. }

    iApply (sim_expr_guarded_iter' _ _
        (fun x y =>
          [ id' := UVALUE_Addr (p_t', 0%Z) ]t i_t ∗ [ id := UVALUE_Addr (p_s, 0%Z) ]s i_s ∗
          [ id' := UVALUE_Addr (p_s', 0%Z) ]s i_s ∗
          (∃ uv, [ x0 := uv ]s i_s) ∗
          p_s ↦s v_s ∗ p_t' ↦t v_t' ∗ p_s' ↦s v_s' ∗
          [ id := UVALUE_Addr (p_t, 0%Z) ]t i_t ∗ [ x0 := v_t ̂ ]t i_t ∗ p_t ↦t v_t ∗
            ⌜(x.2 = Name "body" ∨ x.2 = Name "end") /\ x = y⌝ ∗ code_inv_post ∅ i_t i_s A_t A_s)%I
            with "[] [H]"); cycle 1.
    { iDestruct "H" as "(?&?&?&H'&?&?&?&?&?&?&H)"; iFrame. cbn.
      iSplitL "H'"; first (iExists _; iFrame).
      iSplitL ""; first (iPureIntro; split; first left; try done).
      iDestruct "H" as "(?&?&?&?&?&?)".
      repeat iExists _; iFrame. }

    iModIntro.
    iIntros (??)
      "(Hp_t' & Hp_s & Hp_s' & Hhid_s & Hps & Hpt' & Hps' & Hp_t & Hx0 & Hpt& %Hp & CI)".
    destruct Hp; subst. destruct i_s0.
    iDestruct "CI" as (??) "CI".

    destruct H0; cbn in H0; subst; cycle 1.
    (* exit loop *)
    { rewrite !find_block_end.
      rewrite interp_bind.
      iApply sim_expr'_bind.
      rewrite /make_end; cbn.
      Transparent denote_phis. Transparent denote_code. cbn.
      repeat setoid_rewrite bind_ret_l.
      setoid_rewrite translate_bind.
      setoid_rewrite translate_ret.
      setoid_rewrite interp_bind.
      iApply sim_expr'_bind.
      iApply sim_expr_lift.
      iApply exp_conv_to_instr.
      setoid_rewrite interp_translate.
      setoid_rewrite interp_vis.
      iApply sim_expr_bind.

      iApply (sim_expr_bupd_mono with
          "[Hp_t' Hp_s Hp_s' Hhid_s Hps Hpt' Hps' Hp_t Hx0 Hpt]");
          last iApply (local_read_refl with "CI").
      cont. rewrite !interp_ret.
      iApply sim_expr_tau; iApply sim_expr_base.
      rewrite !bind_ret_l !interp_ret.
      iApply sim_expr'_base.
      rewrite !bind_ret_l !interp_ret.
      iApply sim_expr'_base.
      iRight; repeat iExists _; iFrame; eauto.
      repeat (iSplitL ""; first done).
      iDestruct "H" as "(#Hv & H)".
      iSplitL "H"; first iExists _, _; first by iFrame.
      iExists _, _; do 2 (iSplitL " "; first by iFrame).
      cbn. done. }

    (* still in body *)
    Opaque denote_phis. Opaque denote_code. Opaque denote_terminator.
    cbn.
    rewrite !find_block_body;
      repeat setoid_rewrite interp_bind;
      repeat setoid_rewrite bind_bind.
    (* Phi denotation is the same *)
    iApply sim_expr'_bind.
    cbn -[denote_code denote_terminator].
    iApply (sim_expr'_bupd_mono with
        "[Hp_t' Hp_s Hp_s' Hhid_s Hps Hpt' Hps' Hp_t Hx0 Hpt]");
        last (
            iApply sim_expr_lift;
            iApply (phis_logrel_refl with "CI")).
    cont.

    iApply sim_expr'_bind.

    match goal with
      [ |- context[sim_expr' ?P _ _] ] => remember P
    end.
    clear r_t r_s r_t0 r_s0 r_t1 r_s1.
    clear e_t0 e_s0 e_t1 e_t2 args_t args_s nA_t nA_s.

    (* Denote code: induct on fn *)
    iInduction fn as [ | ] "IH" forall (x H H1 nA_t0 nA_s0); first (cbn in *; inv H).

    destructb. rewrite H0.
    apply Is_true_eq_left in H2; apply block_WF_cons_inv in H2.
    destructb.
    destruct x; cycle 1.
    { cbn in *. rewrite !denote_code_cons.
      setoid_rewrite interp_bind; iApply sim_expr'_bind.
      destruct a.
      iApply (sim_expr'_bupd_mono with
          "[Hp_t' Hp_s Hp_s' Hhid_s Hps Hpt' Hps' Hp_t Hx0 Hpt]");
          last (
              iApply sim_expr_lift;
              iApply (instr_logrel_refl with "H")); last by rewrite H2.
      cont; iDestruct "H" as (??) "H".

      rewrite H4 !app_assoc.
      assert (Htrue : true && true) by auto.
      rewrite -forallb_True in H1.
      cbn in H1.  apply andb_prop_elim in H1; destruct H1.
      by iSpecialize ("IH" $! Htrue _ H H5 (nA_t ++ nA_t0) (nA_s ++ nA_s0) with
                    "Hp_t' Hp_s Hp_s' Hhid_s Hps Hpt' Hps' Hp_t Hx0 Hpt H"). }

    { cbn in *; inversion H. iClear "IH"; rewrite drop_0. clear H.
      rewrite H6 in H2. clear H6.
      rewrite drop_0 in H1.
      rewrite denote_code_cons.
      iApply sim_expr_lift; rewrite interp_bind.
      iApply reduction.source_red_sim_expr.
      iApply source_red_bind.

      iDestruct "H" as (??) "(Hd_t&Hd_s&Hs_t&Hs_s&CI)".
      iDestruct "Hhid_s" as (?) "Hhid_s".
      iApply (source_instr_load_in with "Hps Hp_s Hhid_s Hd_s Hs_s"); eauto.
      { cbn in *.
        apply andb_true_iff in H2. destruct H2.
        rewrite dtyp_WF_b_dtyp_WF in H.
        by apply dtyp_WF_implies_is_supported. }

      iModIntro.
      iIntros "Hp_s Hx0_s Hps Hd_s Hs_s".
      do 2 iApply source_red_base; rewrite bind_ret_l.
      iAssert (code_inv ∅ i_t i_s (nA_t0 ++ A_t) (nA_s0 ++ A_s))%I with "[Hd_t Hs_t Hd_s Hs_s CI]"as "H".
      { iExists args_t, args_s; iFrame. }
      iApply (sim_expr_bupd_mono with
                "[Hp_t' Hp_s' Hpt' Hps' Hp_t Hx0 Hpt Hp_s Hx0_s Hps]");
        last iApply (code_logrel_refl with "H"); cycle 1.
      { rewrite /block_WF in H4.
        apply Is_true_eq_left in H4; destructb; cbn in *.
        rewrite /code_WF; by rewrite H. }

      subst. cont.
      iApply sim_expr'_bind.
      iApply sim_expr_lift. iApply exp_conv_to_instr.

      iDestruct "H" as (??) "H".
      iApply (sim_expr_bupd_mono with
                "[Hp_t' Hp_s' Hpt' Hps' Hp_t Hx0 Hpt Hp_s Hx0_s Hps]"); cycle 1.
      { Transparent denote_terminator. cbn.
        setoid_rewrite interp_bind.
        rewrite translate_vis interp_vis bind_bind.
        iApply sim_expr_bind; iApply sim_expr_bupd_mono;
          last iApply (local_read_refl with "H"); cont.
        rewrite !translate_ret !interp_ret !bind_tau !bind_ret_l.
        iApply sim_expr_tau; rewrite !interp_bind.
        iDestruct "H" as "(#Hv & CI)".
        iApply sim_expr_bind;
          iApply (sim_expr_bupd_mono with "[CI]");
          last iApply (exp_conv_concretize_or_pick with "Hv").
        cont. destruct dv_s;
          try solve [rewrite interp_bind interp_vis bind_bind bind_vis;
            iApply sim_expr_exception_vis].
        { iDestruct (dval_rel_I1_inv with "H") as %H. subst.
          destruct (DynamicValues.Int1.eq x DynamicValues.Int1.one);
          rewrite interp_ret; iApply sim_expr_base.
          Unshelve.
          3 : refine (fun x y =>
              (code_inv ∅ i_t i_s (nA_t ++ nA_t0 ++ A_t) (nA_s ++ nA_s0 ++ A_s) ∗
              (⌜(x = Ret (inl (Name "body")) /\ y = Ret (inl (Name "body"))) ∨
                (x = Ret (inl (Name "end")) /\ y = Ret (inl (Name "end")))⌝ ∨
              (∃ v_t v_s, ⌜(x = Ret (inr v_t) /\ y = Ret (inr v_s))⌝ ∗ uval_rel v_t v_s))))%I.
          { iFrame; iLeft; by iLeft. }
          { iFrame; iLeft; by iRight. } }

         { rewrite interp_bind interp_vis bind_bind bind_vis.

          iApply sim_expr_UB. } }
      cbn. iIntros (??) "H".
      iDestruct "H" as "(CI & H)".
      iDestruct "H" as "[%H | H]".
      { destruct H; destruct H; subst;
          rewrite bind_ret_l interp_ret; iApply sim_expr'_base;
        iLeft; repeat iExists _; iFrame; eauto;
        do 2 (iSplitL " "; first by iFrame);
        iSplitL "Hx0_s"; first (iExists _; by iFrame);
        cbn.
        - rewrite !app_assoc; iSplitL "".
          { iPureIntro; split; auto. }
          iExists _, _; by iFrame.
        - iExists _; by iFrame.
        - rewrite !app_assoc; iSplitL "".
          { iPureIntro; split; auto. }
          iExists _, _; by iFrame. }
      { iDestruct "H" as (???) "#Hb"; subst.
        destruct H; subst.

        rewrite !bind_ret_l !interp_ret; iApply sim_expr'_base;
        iRight; repeat iExists _; iFrame; eauto.
        do 2 (iSplitL " "; first by iFrame).
        rewrite !app_assoc.
        iSplitL "CI".
        { iExists (nA_t ++ nA_t0), (nA_s ++ nA_s0); by iFrame. }
        iExists _, _; iFrame.
        do 2 (iSplitL " "; first by iFrame); by cbn. } }
  Qed.

End licm.
