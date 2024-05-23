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
  Definition fill_ctx (C : context) e attr :=
    Monad.bind (mcfg_definitions (fill_mcfg_defs C e))
        (fun defs => denote_mcfg defs ret_typ (DVALUE_Addr main) args attr).

  (* Contextual refinement. *)
  Definition ctx_ref e_t e_s attr: Prop :=
    forall (C : CFG.mcfg dtyp),
      (* The context and function needs to be well-formed *)
      ctx_wf C ->
      Addr.null.1 <> main.1 ->
      (* All the attributes are nil *)
      (Forall (fun x => dc_attrs x = nil) (map df_prototype (m_definitions C))) ->
      (* Implies whole-program refinement *)
      prog_ref (m_declarations C) main (fill_ctx C e_t attr) (fill_ctx C e_s attr).

End CR_definition.

From Equations Require Import Equations.

Section contextual_refinement.

  Context `{!vellirisGS Σ}.

  Definition mcfg_logrel
    (Ft Fs : list (dvalue * definition dtyp (cfg dtyp)))
    τ ft fs (args_t args_s : list uvalue) attr : iPropI Σ :=
    (val_rel.Forall2 uval_rel args_t args_s -∗
      denote_mcfg Ft τ ft args_t attr ⪯
      denote_mcfg Fs τ fs args_s attr
    ⦉ fun v_t v_s =>
        ∃ r_t r_s, ⌜v_t = Ret r_t⌝ ∗ ⌜v_s = Ret r_s⌝ ∗
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

  Definition lift_val_rel {R1 R2} (Φ : R1 -> R2 -> iPropI Σ) :=
    (λ (x : exprO (Λ := vir_lang) R1) (y : exprO (Λ := vir_lang) R2),
        ∃ vx vy, ⌜x = Ret vx⌝ ∗ ⌜y = Ret vy⌝ ∗ Φ vx vy)%I.

  Definition interp_mrec_post (Φ : uvalue -> uvalue -> iPropI Σ) :=
    (fun vx vy =>
      match vx, vy with
      | inl x, inl y => L0'expr_conv x ⪯ L0'expr_conv y [{ (x, y), Φ x y }]
      | inr x, inr y => Φ x y | _, _ => ⌜False⌝
      end)%I.

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
    destruct Heq; subst; try done; pclearbot; try apply eqit_Ret; try done.
    destruct e; try apply eqit_Ret.
    - eapply eq_itree_clo_bind; first done; intros; subst; eauto.
      eapply REL.
    - apply eqit_Vis; intros. apply eqit_Ret; apply REL.
  Qed.

  Notation "x ~d~ y" := (dval_rel x y) (at level 20).
  Notation "x ~u~ y" := (uval_rel x y) (at level 20).
  Notation "x ~U~ y" := (val_rel.Forall2 uval_rel x y) (at level 20).

  (* Lemma sim_expr'_ret_inv {R1 R2} r_t r_s (Φ : R1 -> R2 -> iPropI Σ) : *)
  (*   Ret r_t ⪯ Ret r_s ⦉ lift_val_rel Φ ⦊ -∗ *)
  (*   Φ r_t r_s. *)
  (* Proof. *)
  (*   rewrite sim_expr' _unfold. *)
  (*   iIntros "[SI H]". rewrite sim_expr_unfold. cbn. *)
  (*   iSpecialize ("H" with "SI"). iMod "H". iDestruct "H" as (?) "H". *)
  (*   destruct c. *)
  (*   - rewrite /lift_expr_rel. *)
  (*     iDestruct "H" as (??????) "(?&H)". *)
  (*     iDestruct "H" as (????) "H". *)
  (*     apply eqit_inv in H; apply eqit_inv in H0. *)
  (*     cbn in H, H0. inv H; inv H0. *)
  (*     subst. *)
  (*     apply eqit_inv in H1; apply eqit_inv in H2. *)
  (*     cbn in H1, H2. subst. *)
  (*     iModIntro; iFrame. *)
  (*   - rewrite /stutter_l. *)
  (*     iDestruct "H" as (??) "H". inv H. *)
  (*   - rewrite /stutter_r. *)
  (*     iDestruct "H" as (??) "H". inv H. *)
  (*   - rewrite /tau_step. *)
  (*     iDestruct "H" as (???) "H". inv H. *)
  (*   - rewrite /vis_step. *)
  (*     iDestruct "H" as (???????) "H". inv H. *)
  (*   - rewrite /source_ub. *)
  (*     iDestruct "H" as (???) "%H". inv H. *)
  (*   - rewrite /source_exc. *)
  (*     iDestruct "H" as (???) "%H". inv H. *)
  (* Qed. *)

  Lemma sim_coindF_ret_inv {R1 R2} r1 r2 (Φ: R1 -d> R2 -d> iPropI Σ) :
    ⊢ sim_coindF (lift_rel (lift_val_rel Φ)) (RetF r1) (RetF r2) ==∗
      state_interp r1.1 r2.1 ∗ Φ r1.2 r2.2.
  Proof.
    iIntros "H".
    rewrite sim_coindF_unfold sim_indF_unfold /sim_expr_inner. iMod "H".
    iDestruct "H" as (?) "H".
    destruct c.
    - rewrite /lift_rel /lift_val_rel.
      iDestruct "H" as (????)"(SI & H)".
      iDestruct "H" as (??????) "H"; subst.
      cbn -[state_interp] in *. inv H; inv H0. by iFrame.
    - rewrite /stutter_l.
      iDestruct "H" as (??) "H". inv H.
    - rewrite /stutter_r.
      iDestruct "H" as (??) "H". inv H.
    - rewrite /tau_step.
      iDestruct "H" as (???) "H". inv H.
    - rewrite /vis_step.
      iDestruct "H" as (????????) "H". inv H0.
    - rewrite /source_ub.
      iDestruct "H" as (???) "%H". inv H.
    - rewrite /source_exc.
      iDestruct "H" as (???) "%H". inv H.
  Qed.

  Lemma interp_mrec_body_proper' (x : itree L0' uvalue) (y : itree L0' uvalue)
    (ctx ctx' : ∀ T : Type, CallE T → L0'expr T) Φ :
    ⟅ x ⟆ ⪯ ⟅ y ⟆ ⦉ lift_val_rel Φ ⦊ -∗
    (∀ τ f_t f_s attrs args_t args_s,
        f_t ~d~ f_s -∗
        args_t ~U~ args_s -∗
        ⟅ ctx _ (Call τ f_t args_t attrs) ⟆ ⪯
        ⟅ ctx' _ (Call τ f_s args_s attrs) ⟆
        ⦉ lift_val_rel uval_rel ⦊) -∗
    interp_mrec_body (D := CallE) ctx uvalue x
    ⪯
    interp_mrec_body (D := CallE) ctx' uvalue y
    ⦉ lift_val_rel (interp_mrec_post Φ) ⦊.
  Proof.
    iIntros "H Hctx".
    rewrite /interp_mrec_body.
    rewrite {1 2}/L0'expr_conv; do 2 rewrite unfold_interp.

    destruct (observe x) eqn: Hx; destruct (observe y) eqn: Hy; rewrite Hx Hy; cbn.
    { (* Ret Ret *)
      iIntros (??) "SI".
      iSpecialize ("H" with "SI"). iMod "H".
      rewrite /interp_L2. setoid_rewrite StateFacts.interp_state_ret.
      rewrite /sim_coind'. cbn.
      iMod (sim_coindF_ret_inv with "H") as "(SI & H)".
      iApply sim_coindF_base; cbn.
      iExists σ_t, σ_s, (Ret (inr r)), (Ret (inr r0)).
      sfinal. cbn; do 2 sfinal. }
    8 : {
      destruct e, e0; eauto.
      { iApply sim_expr'_base. sfinal. rewrite /interp_mrec_post.
        destruct c, c0. rewrite !bind_vis.
        iPoseProof (sim_expr'_call_inv with "H") as "H".
  Admitted.

  Lemma denote_mfun_related args_t args_s attr ft fs τ F_t F_s :
    val_rel.Forall2 uval_rel args_t args_s -∗
    ⟅ denote_mfun F_t (Call τ ft args_t attr) ⟆
    ⪯
    ⟅ denote_mfun F_s (Call τ fs args_s attr) ⟆
    ⦉ lift_val_rel uval_rel ⦊.
  Proof. Admitted.

  Lemma base_rel_eq:
    ⊢ □
      (∀ x y,
        sim_properties.base (Λ := vir_lang) x y ∗ lift_val_rel uval_rel x y ∗-∗
        lift_val_rel uval_rel x y).
  Proof. Admitted.

  (** *contextual refinement *)
  Theorem contextual_refinement attr C f args τ F:
    <pers> ([∗ list]
       '(ft, e_t);'(fs, e_s) ∈ F; F,
        (* Function names are the same and *)
        ⌜ft = fs⌝ ∗
        ⌜dc_attrs (df_prototype e_t) = dc_attrs (df_prototype e_s)⌝ ∗
        (* The functions are logically related and satisfy the attributes *)
        fun_logrel attr_inv (dc_attrs (df_prototype e_t)) e_t e_s C) -∗
    mcfg_logrel F F τ f f args args attr.
  Proof with vsimp.
    iIntros "#Hf Hargs"; rewrite /mrec /interp_mrec.

    (* Can change the current subgoal to a guarded iteration*)
    iApply sim_expr'_tau_inv; first iApply base_rel_eq.

    iApply (sim_expr_guarded_iter'%I).
    Unshelve.
    3 : exact
      (fun x y => sim_expr' (lift_val_rel uval_rel)%I
                 (L0'expr_conv x) (L0'expr_conv y)).
    { iModIntro; iIntros (??) "H".
      iApply sim_expr'_bupd_mono; cycle 1.
      { iApply (interp_mrec_body_proper' _ _ (denote_mfun F_t) with "[H]");
          try done;
        iIntros (??????) "Hdv Hrel".
        by iApply denote_mfun_related. }

      iIntros (??) "H"; iDestruct "H" as (????) "H"; subst...
      destruct vx, vy; eauto.
      { iLeft. sfinal. iApply sim_expr_lift.
        mono: iApply "H"... cbn. iIntros (??) "H".
        iDestruct "H" as (????) "H".
        sfinal. iPureIntro; split; by apply EqAxiom.bisimulation_is_eq. }
      { iRight. do 2 sfinal. } }

    cbn -[denote_mfun]. by iApply denote_mfun_related.
  Qed.

End contextual_refinement.


  (* Opaque denote_function. *)
  (* Lemma denote_mcfg_unfold l τ (f : dvalue) args x attr: *)
  (*   lookup_defn f l = Some x -> *)
  (*   RelDec.rel_dec (dc_attrs (df_prototype x)) (remove_tag []) -> *)
  (*   denote_mcfg l τ f args attr ≅ *)
  (*     lr <- interp_mrec_body (denote_mfun l) _ (denote_function x args) ;; *)
  (*     match lr with *)
  (*     | inl l0 => Tau (interp_mrec (denote_mfun l) l0) *)
  (*     | inr r => Ret r *)
  (*     end. *)
  (* Proof. *)
  (*   intros H Hattr; rewrite /denote_mcfg. *)
  (*   rewrite {1}/mrec /interp_mrec. *)
  (*   setoid_rewrite unfold_iter at 1. *)
  (*   change (ITree.iter _) with (interp_mrec (T := uvalue) (denote_mfun l)). *)
  (*   rewrite {1}/denote_mfun. rewrite H. *)

  (* (*   fold (interp_mrec (D := CallE) (E := L0)); rewrite Hattr. *) *)
  (* (*   eapply eq_itree_clo_bind; first done. intros; subst; done. *) *)
  (* (* Qed. *) *)
  (* Admitted. *)


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
