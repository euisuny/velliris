From iris.prelude Require Import options.

From velliris.vir.util Require Import util vir_util.

(* Syntactic well-formedness conditions and other auxiliary lemmas used for
  logical relation. *)
Section WF.

  (* Syntactic well-formedness of LLVM IR program that we wish to verify *)
  Definition term_WF (ϒ : terminator dtyp) : bool :=
    match ϒ with
      | TERM_Ret _
      | TERM_Ret_void => true
      | TERM_Br (τ, e) bid1 bid2 => true
      | TERM_Br_1 bid => true
      | TERM_Switch (τ, e) bid l => true
      (* Unsupported terminators *)
      | _ => false
    end.

  Definition instr_WF (i : instr dtyp) :=
    match i with
    | INSTR_Op exp => true
    | INSTR_Load _ t (t', _) _ =>
        dtyp_WF_b t && dtyp_WF_b t'
    | INSTR_Store _ (t, _) (DTYPE_Pointer, _) _ =>
        dtyp_WF_b t && non_void_b t
    | INSTR_Call (d, e) args _ => true
    | INSTR_Alloca t _ _ => non_void_b t && dtyp_WF_b t
    | _ => false
    end.

  Definition code_WF (e : code dtyp) : bool :=
      forallb (fun '(id, c) => instr_WF c) e.

  Definition block_WF (b : LLVMAst.block dtyp) : bool :=
    code_WF (LLVMAst.blk_code b) && term_WF (blk_term b).

  Definition ocfg_WF (c : CFG.ocfg dtyp) : bool :=
    forallb (fun b => block_WF b) c.

  Definition cfg_WF (c : CFG.cfg dtyp) : bool :=
    ocfg_WF (CFG.blks c).

  Definition fun_WF (f : definition dtyp (CFG.cfg dtyp)): bool :=
    NoDup_b (df_args f) && cfg_WF (df_instrs f).

  Definition fundefs_WF (F : list (dvalue * _))
    (Attr : list (list fn_attr)) : bool :=
    (length F =? length Attr) &&
    forallb (fun '(_, f) => fun_WF f) F &&
    NoDup_b F.*1.

  Definition CFG_attributes (defs : CFG.mcfg dtyp) :=
    dc_attrs <$> (CFG.m_declarations defs).

  Definition defs_names {T FnBody} (defs : list (definition T FnBody)) :=
    (fun f => dc_name (df_prototype f)) <$> defs.

  Definition CFG_names (defs : CFG.mcfg dtyp) :=
    defs_names (CFG.m_definitions defs).

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

End WF.

Arguments defs_names : simpl never.
Arguments CFG_names /.

Ltac destructb :=
  repeat match goal with
  | [H : is_true (_ && _) |- _] =>
      apply Bool.andb_true_iff in H; destruct H
  | [H : _ && _ = true |- _] =>
      apply Bool.andb_true_iff in H; destruct H
  end.


Section WF_def_properties.

  Lemma fundefs_WF_cons_inv f F a Attr:
    fundefs_WF (f :: F) (a :: Attr) ->
    fun_WF f.2 /\ fundefs_WF F Attr.
  Proof.
    rewrite /fundefs_WF; cbn.
    intros. destructb. destruct f; split; auto.
    do 2 (apply Bool.andb_true_iff; split; auto).
  Qed.

  Lemma ocfg_WF_cons_inv a c :
    ocfg_WF (a :: c) ->
    block_WF a /\ ocfg_WF c.
  Proof. cbn; intros; destructb; eauto. Qed.

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
    intros. unfold contains_keys in H.
    rewrite /defs_names in H. cbn in H.
    apply union_subseteq in H.
    destruct H; split; eauto.
    set_solver.
  Qed.

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

End WF_def_properties.

From velliris.vir Require Import spec vir_state.

(* ------------------------------------------------------------------------ *)
(* Auxiliary definitions for stating invariants for logical relation. *)

(* Collect the local ids that occur in an expression [e]. *)
Fixpoint exp_local_ids_ {T} (e : exp T) (acc : list raw_id) : list raw_id :=
  match e with
  | EXP_Ident (ID_Local i) => i :: acc
  | EXP_Cstring l | EXP_Struct l | EXP_Array l =>
      List.concat (List.map (fun x => exp_local_ids_ x.2 nil) l) ++ acc
  | OP_IBinop _ _ v1 v2 | OP_ICmp _ _ v1 v2 =>
      exp_local_ids_ v1 (exp_local_ids_ v2 acc)
  | OP_Conversion _ _ v _ =>
      exp_local_ids_ v acc
  | OP_GetElementPtr _ (_, e) l =>
      exp_local_ids_ e nil ++
      List.concat (List.map (fun x => exp_local_ids_ x.2 nil) l) ++ acc
  | _ => acc
  end.

Definition exp_local_ids {T} (e : exp T) := exp_local_ids_ e nil.

Definition empty_WF :
  gmap (loc * loc) Qp → gmap raw_id uvalue → gmap raw_id uvalue → Prop :=
  fun _ _ _ => True.

(* Given expressions, get the intersection of their local ids. *)
Definition intersection_local_ids {T} (e_t e_s : exp T) :=
  list_intersection (exp_local_ids e_t) (exp_local_ids e_s).

(* Helper functions for [mcfg]. *)
Definition address_one_function (df : definition dtyp (CFG.cfg dtyp)) :
  itree LLVMEvents.L0 (dvalue * definition dtyp (CFG.cfg dtyp)) :=
  let fid := (dc_name (df_prototype df)) in
  fv <- trigger (GlobalRead fid) ;;
  Ret (fv, df).

Definition mcfg_definitions (mcfg : CFG.mcfg dtyp) :
  itree LLVMEvents.L0 (list (dvalue * _)) :=
    (Util.map_monad address_one_function (CFG.m_definitions mcfg)).

Definition local_env_spec {Σ} `{!vellirisGS Σ} :=
  (list frame_names -> list frame_names -> local_env -> local_env -> iProp Σ).

Definition alloca_spec {Σ} `{!vellirisGS Σ} :=
  (gmap (loc * loc) Qp -> list Z -> list Z -> iProp Σ).

(* ------------------------------------------------------------------------ *)
(* Helper lemmas on auxiliary definitions for logical relation. *)
Lemma intersection_local_ids_eq {T} (e : exp T):
  intersection_local_ids e e = exp_local_ids e.
Proof.
  apply list_intersection_eq.
Qed.

(* Properties about [expr_local_env_inv] *)
Lemma exp_local_ids_acc_commute {T} (e : exp T) acc :
  exp_local_ids_ e acc = exp_local_ids e ++ acc.
Proof.
  revert acc.
  induction e; cbn; try rewrite app_nil_r; eauto.
  (* Ident *)
  { destruct id; eauto. }
  (* Binop *)
  { intros.
    do 2 rewrite IHe2. rewrite app_nil_r.
    do 2 rewrite IHe1. by rewrite app_assoc. }
  (* ICmp *)
  { intros.
    do 2 rewrite IHe2. rewrite app_nil_r.
    do 2 rewrite IHe1. by rewrite app_assoc. }
  (* GEP *)
  { intros. destruct ptrval; cbn.
    by rewrite app_assoc. }
Qed.
