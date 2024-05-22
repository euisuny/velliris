From iris.prelude Require Import options.

From velliris.logic Require Import satisfiable.
From velliris.vir Require Import lang logrel.

From velliris.vir.soundness Require Import adequacy.

Set Default Proof Using "Type*".

(** *Initial state *)

Definition empty_vir_state : vir_state :=
  {| vglobal := ∅;
     vlocal := (nil, nil);
     vmem := (∅, ∅, Mem.Singleton nil) |}.

(* Returns `true` only if both function are named and have
     the same name. *)
Definition function_name_eq (a b:function_id) : bool :=
  match a, b with
  | Name aname, Name bname => String.eqb aname bname
  | _, _ => false
  end.

(* Initial state: all function declaration names are allocated in global
   environment, and otherwise the state is empty *)
Definition allocate_declaration_prog (d:declaration dtyp) (σ : vir_state) : vir_state :=
  match List.find (fun x => function_name_eq (dc_name d) (dc_name x))
          IntrinsicsDefinitions.defined_intrinsics_decls with
  | Some _ => σ
  | None =>
      let '(mem, v) := vir_util.allocate_non_void DTYPE_Pointer (vmem σ) in
      let σ := update_mem mem σ in
      apply_global (fun g => <[ dc_name d := DVALUE_Addr v]> g) σ
  end.

Definition allocate_declarations_prog
  (ds:list (declaration dtyp)) (σ : vir_state) : vir_state :=
  List.fold_left (fun acc x => allocate_declaration_prog x acc) ds σ.

Definition init_state ds := allocate_declarations_prog ds empty_vir_state.

(** *Whole-program refinement *)
Section prog_ref.

  Context (ds : list (declaration dtyp)) (main : Addr.addr).

  Definition init_mem : vir.logical_memory :=
    ({[main.1 := dvalue_to_block DVALUE_None;
      Addr.null.1 := dvalue_to_block DVALUE_None]},
    {[main.1; Addr.null.1]}, Mem.Singleton [main.1; Addr.null.1]).

  (* If the initial states are related by some relation, and the expressions
     are well formed (i.e. the source program does not "go wrong" and the
     expressions are closed after denotation), then the resulting programs
     are observationally equivalent to each other using [eutt]. *)
  Definition prog_ref (e_t e_s : expr vir_lang uvalue) :=
    let σ :=
      {| vglobal := vglobal (init_state ds);
         vlocal := (∅, ∅); vmem := init_mem |} in
    well_formed (⟦ e_t ⟧ σ) (⟦ e_s ⟧ σ) ->
    eutt obs_val_res (⟦ e_t ⟧ σ) (⟦ e_s ⟧ σ).

End prog_ref.

Import CFG.

(* A context is a mutually recursive control flow graph [mcfg]. *)
Notation context := (CFG.mcfg dtyp).

(* Well-formedness over contexts *)
Definition ctx_wf (C : context) :=
  let funs := CFG.m_definitions C in
  (* The context has the same definitions *)
  (length (CFG.m_declarations C) = length (CFG.m_definitions C)) /\
  (* There are no duplicate names in the context *)
  NoDup (CFG_names C) /\
  (* All the functions declared are well-formed *)
  Forall fun_WF funs /\
  (* The attributes list is empty for each function declaration *)
  (* TODO : Do we want something a little more generic here?
     This is the strongest statement that would follow automatically as a
     consequence of the fundamental theorem. *)
  Forall (fun x => dc_attrs x = nil) (CFG.m_declarations C)
.

(** *Top-level Contextual Refinement *)

Section CR_definition.

  Context (Σ : gFunctors).
  Context (ret_typ : dtyp) (main : Addr.addr) (args : list uvalue)
          (I : vir_state -> vir_state -> Prop).

  (* The context takes a function (with its declaration and definition) as its
     hole; we can extend the list of declarations and definitions with the hole. *)
  Definition fill_mcfg_defs (C : context)
    (e : declaration dtyp * definition dtyp (CFG.cfg dtyp)) :=
    {| m_name := m_name C;
      m_target := m_target C;
      m_datalayout := m_datalayout C;
      m_type_defs := m_type_defs C;
      m_globals := m_globals C;
      m_declarations := e.1 :: m_declarations C;
      m_definitions := e.2 :: m_definitions C
    |}.

  (* Filling the context involves (1) extending the function declaration map and
    (2) restating the denotation of mutually-recursive control flow graps using
        [denote_mcfg]. *)
  Definition fill_ctx (C : context) e :=
    Monad.bind (mcfg_definitions (fill_mcfg_defs C e))
        (fun defs => denote_mcfg defs ret_typ (DVALUE_Addr main) args).

  (* Contextual refinement. *)
  Definition ctx_ref e_t e_s: Prop :=
    forall (C : CFG.mcfg dtyp),
      (* The context and function needs to be well-formed *)
      ctx_wf C ->
      Addr.null.1 <> main.1 ->
      (* All the attributes are nil *)
      (Forall (fun x => dc_attrs x = nil) (map df_prototype (m_definitions C))) ->
      (* Implies whole-program refinement *)
      prog_ref (m_declarations C) main (fill_ctx C e_t) (fill_ctx C e_s).

End CR_definition.

From Equations Require Import Equations.

Section contextual_refinement.

  Context `{!vellirisGS Σ}.

  Definition mcfg_logrel
    (Ft Fs : list (dvalue * definition dtyp (cfg dtyp)))
    τ ft fs (args_t args_s : list uvalue) : iPropI Σ :=
    (∀ i_t i_s args_t args_s,
      frameR i_t i_s nil nil ∅ -∗
      allocaR i_t i_s ∅ ∅ -∗
      val_rel.Forall2 uval_rel args_t args_s -∗
      denote_mcfg Ft τ ft args_t ⪯
      denote_mcfg Fs τ fs args_s
    ⦉ fun v_t v_s =>
        ∃ r_t r_s, ⌜v_t = Ret r_t⌝ ∗ ⌜v_s = Ret r_s⌝ ∗
        frameR i_t i_s nil nil ∅∗
        allocaR i_t i_s ∅ ∅ ∗
        uval_rel r_t r_s ⦊)%I.

  Definition interp_mrec_body {D E : Type -> Type}
    (ctx : D ~> itree (D +' E)) : forall T, itree (D +' E) T -> itree E _ :=
    fun R x =>
      match observe x with
      | RetF r => Ret (inr r)
      | TauF t => Ret (inl t)
      | @VisF _ _ _ X (inl1 d) k => Ret (inl (x <- ctx _ d;; k x))
      | @VisF _ _ _ X (inr1 e) k => Vis e (λ x0 : X, Ret (inl (k x0)))
      end.

  Opaque denote_function.
  Lemma denote_mcfg_unfold l τ (f : dvalue) args x:
    lookup_defn f l = Some x ->
    RelDec.rel_dec (dc_attrs (df_prototype x)) (remove_tag []) ->
    denote_mcfg l τ f args ≅
      lr <- interp_mrec_body (denote_mfun l) _ (denote_function x args) ;;
      match lr with
      | inl l0 => Tau (interp_mrec (denote_mfun l) l0)
      | inr r => Ret r
      end.
  Proof.
    intros H Hattr; rewrite /denote_mcfg.
    rewrite {1}/mrec /interp_mrec.
    setoid_rewrite unfold_iter at 1.
    change (ITree.iter _) with (interp_mrec (T := uvalue) (denote_mfun l)).
    rewrite {1}/denote_mfun. rewrite H.
    fold (interp_mrec (D := CallE) (E := L0)); rewrite Hattr.
    eapply eq_itree_clo_bind; first done. intros; subst; done.
  Qed.

  From Paco Require Import paco.

  Lemma interp_mrec_body_proper {D E} x y ctx ctx':
    x ≅ y ->
    (∀ u d, ctx u d ≅ ctx' u d) ->
    eq_itree (fun x y => match x, y with
      | inl x, inl y => x ≅ y | inr x, inr y => x = y | _, _ => False end)
      (interp_mrec_body ctx uvalue x)
      (interp_mrec_body (D := D) (E := E) ctx' uvalue y).
  Proof.
    intros Heq Hctx. punfold Heq. red in Heq.
    unfold interp_mrec_body.
    remember (observe x) as Hox; remember (observe y) as Hoy.
    clear HeqHox HeqHoy.
    induction Heq; subst; try done; pclearbot; try apply eqit_Ret; try done.
    destruct e; try apply eqit_Ret.
    - eapply eq_itree_clo_bind; first done; intros; subst; eauto.
      eapply REL.
    - apply eqit_Vis; intros. apply eqit_Ret; apply REL.
  Qed.

  Lemma interp_mrec_body_proper' {R} (x : itree L0' R) (y : itree L0' R)
    (ctx ctx' : ∀ T : Type, CallE T → L0'expr T) Φ :
    (L0'expr_conv x ⪯ L0'expr_conv y
       ⦉ fun x y => ∃ vx vy, ⌜x = Ret vx⌝ ∗ ⌜y = Ret vy⌝ ∗  Φ vx vy ⦊) -∗
    (∀ d, L0'expr_conv (ctx R d) ⪯ L0'expr_conv (ctx' R d)
         ⦉ fun x y => ∃ vx vy, ⌜x = Ret vx⌝ ∗ ⌜y = Ret vy⌝ ∗  Φ vx vy ⦊) -∗
    interp_mrec_body (D := CallE) (E := L0) ctx R x
    ⪯
    interp_mrec_body (D := CallE) ctx' R y
    ⦉ fun x y =>
         ∃ vx vy, ⌜x = Ret vx⌝ ∗ ⌜y = Ret vy⌝ ∗
          match vx, vy with
          | inl x, inl y => L0'expr_conv x ⪯ L0'expr_conv y [{ (x, y), Φ x y }]
          | inr x, inr y => Φ x y | _, _ => ⌜False⌝
          end ⦊.
  Proof. Admitted.

  (** *contextual refinement *)
  Theorem contextual_refinement
    e_t e_s e_t' e_s' C attr attr' ft ft' fs fs' args_t args_s τ:
    RelDec.rel_dec (dc_attrs (df_prototype e_t)) [] ->
    RelDec.rel_dec (dc_attrs (df_prototype e_s)) [] ->
    fun_logrel attr_inv attr e_t e_s C -∗
    fun_logrel attr_inv attr' e_t' e_s' C -∗
    mcfg_logrel
      [(ft, e_t); (ft', e_t')]
      [(fs, e_s); (fs', e_s')] τ ft fs args_t args_s.
  Proof.
    intros Hat Has.
    iIntros "Hf Hf'" (????) "Hfr Ha Hargs".
    rewrite /mrec /interp_mrec.
    rewrite denote_mcfg_unfold; cycle 1; cbn.
    { destruct (RelDec.rel_dec ft ft) eqn: Ht; eauto.
      apply RelDec.neg_rel_dec_correct in Ht; done. }
    { done. }

    rewrite denote_mcfg_unfold; cycle 1; cbn.
    { destruct (RelDec.rel_dec fs fs) eqn: Ht; eauto.
      apply RelDec.neg_rel_dec_correct in Ht; done. }
    { done. }

    Cut...

    iPoseProof
      (interp_mrec_body_proper'
          (denote_function e_t args_t0)
          (denote_function e_s args_s0)
          (denote_mfun [(ft, e_t); (ft', e_t')])
      ) as "H".
    iApply sim_expr'_bupd_mono; cycle 1.
    { iApply ("H" with "[Hf Hfr Ha Hargs]").
      { iApply "Hf"; admit. }
      iIntros (?). Require Import Coq.Program.Equality.
      dependent destruction d; cbn.

  Admitted.

End contextual_refinement.
