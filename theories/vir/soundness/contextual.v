From iris.prelude Require Import options.

From velliris.logic Require Import satisfiable.
From velliris.program_logic Require Import program_logic.
From velliris.vir Require Import vir val_rel
  heapbij adequacy spec globalbij logical_relations fundamental
  contextual_mcfg.

From Vellvm Require Import Syntax.DynamicTypes Handlers Syntax.LLVMAst
  Semantics.InterpretationStack.

From ITree Require Import Eq Recursion.

Import LLVMEvents.

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
    {[main.1; Addr.null.1]}, Singleton [main.1; Addr.null.1]).

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
      (* TODO Remove this and impose this on the adequacy *)
      fun_WF e_t.2 -> fun_WF e_s.2 ->
      (* All the attributes are nil *)
      (Forall (fun x => dc_attrs x = nil) (map df_prototype (m_definitions C))) ->
      (dc_attrs (df_prototype e_t.2)) = nil ->
      (dc_attrs (df_prototype e_s.2)) = nil ->
      (* The names of the declarations are the same *)
      dc_name (df_prototype e_t.2) = dc_name (df_prototype e_s.2) ->
      (* Implies whole-program refinement *)
      prog_ref (m_declarations C) main (fill_ctx C e_t) (fill_ctx C e_s).

End CR_definition.

(* (* Initial relation on states; there is a [main] and [null] address in the *)
(*     state. *)
(*   The memory and frame is empty except for the main and null address. *) *)
(* Definition init_state (main : Addr.addr) (fun_names : list function_id) : vir_state -> Prop := *)
(*   fun '(g, (l, ls), (m, f)) => *)
(*     (* The global environment contains the names of function declarations in *)
(*         the context [C]. *) *)
(*       g = init_global (fun_names) *)
(*     (* The local environment and local stack is empty *) *)
(*     /\ l = nil /\ ls = nil *)
(*     (* The memory has [main] and [null] allocated *) *)
(*     /\ m = ({[ main.1 := dvalue_to_block DVALUE_None; *)
(*               Addr.null.1 := dvalue_to_block DVALUE_None ]}, *)
(*             {[ main.1; Addr.null.1 ]}) *)
(*     (* The frame has the main and null address *) *)
(*     /\ f = Mem.Singleton [ main.1; Addr.null.1 ]. *)

(* (* The relational variant, with the added condition that the [main] and [null] *)
(*   addresses are not equivalent to each other. *) *)
(* Definition init_state_rel (main : Addr.addr) C : vir_state -> vir_state -> Prop := *)
(*   fun σ_t σ_s => *)
(*     main.1 <> Addr.null.1 /\ (* Do we say something about the rest of the state? *) *)
(*     init_state main C σ_t /\ init_state main C σ_s. *)

Section CR_properties.

  Context {Σ} `{!vellirisGS Σ}.
(*   Context (ret_typ : dtyp) (main : Addr.addr) (args : list uvalue). *)

  (* TODO *)
  Lemma contains_keys_init_global C :
    contains_keys (vglobal (init_state (m_declarations C))) (CFG_names C).
  Proof.
    (* induction names; cbn; eauto; first set_solver. *)
    (* rewrite /contains_keys. cbn. rewrite /init_global; cbn. *)
  Admitted.

  (* TODO *)
  Lemma nodup_codomain_init_global C :
    NoDup_codomain
      (filter_keys (vglobal (init_state (m_declarations C))) (CFG_names C)).
  Proof. Admitted.

  Lemma ctx_wf_implies_CFG_WF C :
   ctx_wf C ->
   CFG_WF C
    (vglobal (init_state (m_declarations C)))
    (vglobal (init_state (m_declarations C))).
  Proof.
    intros (?&?&?&?).
    repeat (split; eauto);
      eauto using contains_keys_init_global, nodup_codomain_init_global.
  Qed.

(*   Lemma ctx_wf_fill_mcfg_defs C decl e_t: *)
(*     ctx_wf (fill_mcfg_defs C (decl, e_t)) -> *)
(*     ctx_wf C. *)
(*   Proof. *)
(*     rewrite /ctx_wf. *)
(*     intros. destructb. *)
(*     cbn in *. split; eauto. nodup. *)
(*     apply Forall_cons in H1, H2. *)
(*     destructb. *)
(*     repeat split; eauto. *)
(*   Qed. *)

(*   Lemma ctx_wf_hole_attr C decl e_t: *)
(*     ctx_wf (fill_mcfg_defs C (decl, e_t)) -> *)
(*     (dc_attrs decl = nil). *)
(*   Proof. *)
(*     rewrite /ctx_wf. *)
(*     intros. destructb. *)
(*     clear -H2. cbn in *. *)
(*     apply Forall_cons in H2; by destructb. *)
(*   Qed. *)

End CR_properties.

(* Well-formedness on globals: all global values are self-related *)
Definition globals_WF `{heapbijGS Σ} (g : global_env) : iPropI Σ :=
  ([∗ map] g0↦v ∈ g, ∃ v' : dvalue, ⌜g !! g0 = Some v'⌝ ∗ dval_rel v' v)%I.

Definition init_keys (main : Addr.addr) : list global_id :=
  Raw main.1 :: Raw Addr.null.1 :: nil.

(* We can instantiate a state interpretation with corresponding ghost resources
  on states that satisfy the initializaition relation [I] *)
(* IY : Is there a cleaner way to state this lemma? *)
Lemma initialize_state_interp ds (main : Addr.addr) Σ `{vellirisGpreS Σ} :
  forall e_t e_s,
    (* let init_keys := init_keys main in *)
    (∀ `(vellirisGS Σ), <pers> fun_logrel e_t e_s ∅) ==∗
    ∃ (H_sh : vellirisGS Σ),
      state_interp (init_state ds) (init_state ds) ∗
      target_globals (vglobal (init_state ds)) ∗
      source_globals (vglobal (init_state ds)) ∗
    ∃ γ_t γ_s,
        checkout ∅ ∗ stack_tgt [γ_t] ∗ stack_src [γ_s].
Proof.
  (* rename H into H_vs. *)
  intros *.

  iMod (velliris_init ∅ (vglobal (init_state ds)) (vglobal (init_state ds)) ∅)
    as (Hvg) "(Hc1 & Hc2 & (Hh_t & Hh_s & H) & Hbij)".

  rewrite /state_interp.

  iDestruct "H" as "(Hh_tf & Hb_t & Hg_t & Hh_sf & Hb_s & Hg_s & H)".

  iDestruct "H" as "(Ht & Hs)".
  iDestruct "Ht" as (?) "(Hst_t & Hl_t & Hld_t & Ha_t)".
  iDestruct "Hs" as (?) "(Hst_s & Hl_s & Hld_s & Ha_s)".

  (* Allocate null bij *)
  (* destruct σ_t as ((?&?&?)&(?&?)&?). *)
  (* destruct σ_s as ((?&?&?)&(?&?)&?). *)

  (* destruct HI as (Hun & ?&?&?&?&?&?); subst; inv H3. *)
  (* destruct H as (?&?&?&?&?); subst; inv H2. *)

  (** *Allocate null address *)
  (* Allocate at [Addr.null] on target side *)
  iCombine ("Ha_t Hst_t Hh_t") as "H".
  iPoseProof
    (heap_ctx_alloc _ Addr.null.1
       DVALUE_None ((∅, ∅), Singleton ∅) [γf] _ _ _ _ _ DTYPE_Void) as "Halloc_t";
    [ set_solver | cbn; set_solver | constructor | ].
  rewrite allocaS_eq /allocaS_def. rewrite /stack.
  iSpecialize ("Halloc_t" with "H"). iMod "Halloc_t".

  (* Allocate at [Addr.null] on source side *)
  iCombine ("Ha_s Hst_s Hh_s") as "H".
  iPoseProof
    (heap_ctx_alloc _ Addr.null.1
       DVALUE_None ((∅, ∅), Singleton ∅) [γf0] _ _ _ _ _ DTYPE_Void) as "Halloc_s";
    [ set_solver | cbn; set_solver | constructor | ].
  rewrite allocaS_eq /allocaS_def. rewrite /stack.
  iSpecialize ("Halloc_s" with "H"). iMod "Halloc_s".

  iDestruct "Halloc_t" as "(Hh_t & %Hin_t & Ha_t & Hst_t & Hv_t & hb_t)".
  iDestruct "Halloc_s" as "(Hh_s & %Hin_s & Ha_s & Hst_s & Hv_s & hb_s)".

  (* Extend global bij *)
  rewrite !mapsto_dval_eq /mapsto_dval_def.
  iAssert (lb_rel (dvalue_to_block DVALUE_None) (dvalue_to_block DVALUE_None))%I as "Hb".
  { rewrite /lb_rel. cbn.
    rewrite /mem_byte_rel. rewrite /init_block; cbn.
    simpl. iSplit.
    { iIntros (???). inversion H0. }
    { done. } }

  iIntros "Hf".
  iDestruct (heapbij_insert with "Hbij Hv_t Hv_s Hb hb_t hb_s") as ">(Hbij & #Haddr_null)".

  (** *Allocate main address *)
  (* Allocate at [Addr.main] on target side *)
  iCombine ("Ha_t Hst_t Hh_t") as "H".
  iPoseProof
    (heap_ctx_alloc _ main.1
       DVALUE_None (({[Addr.null.1:=dvalue_to_block DVALUE_None]}, {[Addr.null.1]})
         , Mem.Singleton [Addr.null.1]) [γf] _ _ _ _ _ DTYPE_Void) as "Halloc_t".
  { cbn; rewrite lookup_singleton_ne; auto. admit. }
  (* { cbn; set_solver. } *)
  (* { constructor. } *)

  (* rewrite allocaS_eq /allocaS_def. rewrite /stack. *)
  (* cbn. rewrite !insert_empty !union_empty_r_L. *)
  (* iSpecialize ("Halloc_t" with "H"). iMod "Halloc_t". *)

  (* (* Allocate at [Addr.main] on source side *) *)
  (* iCombine ("Ha_s Hst_s Hh_s") as "H". *)
  (* iPoseProof *)
  (*   (heap_ctx_alloc _ main.1 *)
  (*      DVALUE_None (({[Addr.null.1:=dvalue_to_block DVALUE_None]}, {[Addr.null.1]}) *)
  (*        , Mem.Singleton [Addr.null.1]) [γf0] _ _ _ _ _ DTYPE_Void) as "Halloc_s". *)
  (* { cbn; rewrite lookup_singleton_ne; auto. } *)
  (* { cbn; set_solver. } *)
  (* { constructor. } *)

  (* rewrite allocaS_eq /allocaS_def. rewrite /stack. *)
  (* iSpecialize ("Halloc_s" with "H"). iMod "Halloc_s". *)

  (* iDestruct "Halloc_t" as "(Hh_t & %Hin_t' & Ha_t & Hs_t & Hv_t & hb_t)". *)
  (* iDestruct "Halloc_s" as "(Hh_s & %Hin_s' & Ha_s & Hs_s & Hv_s & hb_s)". *)

  (* (* Extend global bij *) *)
  (* rewrite !mapsto_dval_eq /mapsto_dval_def. *)
  (* iDestruct (heapbij_insert with "Hbij Hv_t Hv_s Hb hb_t hb_s") as ">(H & #Haddr_main)". *)
  (* iDestruct "Hg_t" as "#Hg_t"; iDestruct "Hg_s" as "#Hg_s". *)

  (* iSpecialize ("Hf" $! Hvg). *)
  (* iDestruct  "Hf" as "#Hf". *)
  (* iModIntro. *)
  (* iExists Hvg. *)

  (* iSplitR "Hc2 Hs_t Hs_s". *)
  (* { iExists ∅, {[(main.1, main.1); (Addr.null.1, Addr.null.1)]}, (vglobal (init_state ds)); iFrame. *)

  (*   (* Global init *) *)
  (*   rewrite /spec.globalbij_interp; cbn. *)
  (*   rewrite !globals_eq /globals_def; cbn. iFrame. *)
  (*   iDestruct "Haddr_null" as "(Haddr' & %H')". *)
  (*   iSplitL "H". { iPureIntro; set_solver. } *)
  (*   iSplitL "". { iSplitL ""; done. } *)
  (*   iSplitL "". { iPureIntro; set_solver. } *)
  (*   iFrame "Hg_t Hg_s". done. } *)
  (* rewrite !globals_eq /globals_def. iFrame "Hg_t Hg_s". *)
  (* iExists γf, γf0; iFrame. *)
Abort.
(* Admitted. *)

(* The contextual refinement statement, with ghost state instantiated *)
Lemma contextual_ref `(vellirisGS Σ):
  ∀ e_t e_s γ_t γ_s C decl main,
  (* Well-formedness conditions *)
  ctx_wf C ->
  fun_WF e_t ->
  fun_WF e_s ->
  (* The names of the declarations are the same *)
  dc_name (df_prototype e_t) = dc_name (df_prototype e_s) ->
  (* The ghost resources for globals is set up *)
  target_globals (vglobal (init_state (m_declarations C))) -∗
  source_globals (vglobal (init_state (m_declarations C))) -∗
  (* Hole is logically related *)
  □ (fun_logrel e_t e_s ∅) -∗
  (* Frame resources are set up *)
  checkout ∅ ∗ stack_tgt [γ_t] ∗ stack_src [γ_s] ==∗
  fill_ctx DTYPE_Void main [] C (decl, e_t)
  ⪯
  fill_ctx DTYPE_Void main [] C (decl, e_s)
  [[ (λ x y : uvalue, ⌜obs_val x y⌝) ⤉ ]].
Proof.
  rename H into H_vgs.
  iIntros (??????? H_wf H_wf_t Hwf_s WF_name) "#Hg_t #Hg_s #Hfun Hstack".

  (* Access stack resources *)
  iDestruct "Hstack" as "(Hc & Hs_t & Hs_s)".

  (* Unfold [context] definition *)
  with_strategy transparent [context] cbn.

  rewrite !bind_bind; setoid_rewrite bind_ret_l.
  iApply sim_expr'_bind.

  rewrite WF_name.

  (* Read the names of the functions ; they are the same *)
  iApply (sim_expr'_bupd_mono with "[Hc Hs_t Hs_s]");
    [ | iApply sim_expr_lift; iApply sim_global_read ]; cycle 1.
  { iModIntro. iIntros (??) "H'". iApply "H'". }

  iIntros (??) "(%dv & %dv' & %Hr1 & %Hr2 & #Hdv)".
  rewrite Hr1 Hr2 !bind_ret_l; clear Hr1 Hr2.
  rewrite !bind_bind; setoid_rewrite bind_ret_l.
  iApply sim_expr'_bind.

  (* The mcfg is the same, so the resulting definitions are the same *)
  iApply (sim_expr'_bupd_mono with "[Hc Hfun Hs_t Hs_s]");
    [ | iApply mcfg_definitions_refl' ]; eauto.
  2 : eauto using ctx_wf_implies_CFG_WF.

  iIntros (??) "H".
  iDestruct "H" as (????????)
    "(#Hv &  %Hl1 & %Hl2 & #(Hrel & %WF_t & %WF_s & #Hlr))"; subst.

  setoid_rewrite bind_ret_l. iModIntro.

  pose proof (mcfg_definitions_leaf _ _ _ _ _ _ Hl1 Hl2) as Hsame. subst.
  rewrite /mcfg_definitions in Hl1; iClear "Hrel Hlr".

  destruct H_wf.
(*    iApply (contextual_denote_mcfg with "Hfun Hc Hs_t Hs_s"); eauto. *)
(* Qed. *)
Abort.

(* (* The contextual refinement statement, with ghost state instantiated *) *)
(* Lemma contextual_ref `(vellirisGS Σ): *)
(*   ∀ e_t e_s γ_t γ_s C decl main, *)
(*   (* Well-formedness conditions *) *)
(*   ctx_wf C -> *)
(*   fun_WF e_t -> *)
(*   fun_WF e_s -> *)
(*   (* The names of the declarations are the same *) *)
(*   dc_name (df_prototype e_t) = dc_name (df_prototype e_s) -> *)
(*   (* The ghost resources for globals is set up *) *)
(*   target_globals (vglobal (init_state (m_declarations C))) -∗ *)
(*   source_globals (vglobal (init_state (m_declarations C))) -∗ *)
(*   (* Hole is logically related *) *)
(*   □ (fun_logrel e_t e_s ∅) -∗ *)
(*   (* Frame resources are set up *) *)
(*   checkout ∅ ∗ stack_tgt [γ_t] ∗ stack_src [γ_s] ==∗ *)
(*   fill_ctx DTYPE_Void main [] C (decl, e_t) *)
(*   ⪯ *)
(*   fill_ctx DTYPE_Void main [] C (decl, e_s) *)
(*   [[ (λ x y : uvalue, ⌜obs_val x y⌝) ⤉ ]]. *)
(* Proof. *)
(*   iIntros (??????? H_wf H_wf_t Hwf_s WF_name) "#Hg_t #Hg_s #Hfun Hstack". *)

Lemma init_global_WF `{vellirisGS Σ} C :
  ⊢ globals_WF (vglobal (init_state C)).
Admitted.

Lemma init_cfg_WF `{vellirisGS Σ} C:
 CFG_WF C
   (vglobal (init_state (m_declarations C)))
   (vglobal (init_state (m_declarations C))).
Admitted.

From Equations Require Import Equations.

(** *Top-level soundness theorem *)
Theorem soundness `{vellirisGpreS Σ}
  e_t e_s main decl:
  isat (∀ `(vellirisGS Σ), <pers> fun_logrel e_t e_s ∅) ->
  ctx_ref DTYPE_Void main [] (decl, e_t) (decl, e_s).
Proof.
  intros Hf C WF WF_main WF_t WF_s WF_attr_nil
    WF_attr_t WF_attr_s WF_name WF_pr.

  (* Apply adequacy; moving to the Iris logic *)
  eapply (@adequacy Σ isat); eauto; try typeclasses eauto.

  eapply sat_mono, Hf. clear Hf.
  iStartProof. iIntros "#Hf".

  set (init_σ := init_state (m_declarations C)).

  (* Initialize the ghost state *)
  iMod (@velliris_init Σ _ ∅
           (vglobal init_σ) (vglobal init_σ) ∅)
    as (Hsh) "(Hc1 & Hc2 & (Hh_t & Hh_s & H) & Hbij)".

  rewrite /state_interp.

  iDestruct "H" as "(Hh_tf & Hb_t & Hg_t & Hh_sf & Hb_s & Hg_s & H)".

  iDestruct "H" as "(Ht & Hs)".
  iDestruct "Ht" as (?) "(Hst_t & Hl_t & Hld_t & Ha_t)".
  iDestruct "Hs" as (?) "(Hst_s & Hl_s & Hld_s & Ha_s)".

  (** *Allocate null address *)
  (* Allocate at [Addr.null] on target side *)
  iCombine ("Ha_t Hst_t Hh_t") as "H".
  iPoseProof
    (heap_ctx_alloc _ Addr.null.1
       DVALUE_None ((∅, ∅), ∅) [γf] _ _ _ _ _ DTYPE_Void) as "Halloc_t";
    [ set_solver | cbn; set_solver | constructor | ].
  rewrite allocaS_eq /allocaS_def. rewrite /stack.
  iSpecialize ("Halloc_t" with "H"). iMod "Halloc_t".

  (* Allocate at [Addr.null] on source side *)
  iCombine ("Ha_s Hst_s Hh_s") as "H".
  iPoseProof
    (heap_ctx_alloc _ Addr.null.1
       DVALUE_None ((∅, ∅), ∅) [γf0] _ _ _ _ _ DTYPE_Void) as "Halloc_s";
    [ set_solver | cbn; set_solver | constructor | ].
  rewrite allocaS_eq /allocaS_def. rewrite /stack.
  iSpecialize ("Halloc_s" with "H"). iMod "Halloc_s".

  iDestruct "Halloc_t" as "(Hh_t & %Hin_t & Ha_t & Hst_t & Hv_t & hb_t)".
  iDestruct "Halloc_s" as "(Hh_s & %Hin_s & Ha_s & Hst_s & Hv_s & hb_s)".

  (* Extend global bij *)
  rewrite !mapsto_dval_eq /mapsto_dval_def.
  iAssert (lb_rel (dvalue_to_block DVALUE_None) (dvalue_to_block DVALUE_None))%I as "Hb".
  { rewrite /lb_rel. cbn.
    rewrite /mem_byte_rel. rewrite /init_block; cbn.
    simpl. iSplit.
    { iIntros (???). inversion H0. }
    { done. } }
  iPoseProof (heapbij_insert with "Hbij Hv_t Hv_s Hb hb_t hb_s") as ">(Hbij & #Haddr_null)".

  (** *Allocate main address *)
  (* Allocate at [Addr.main] on target side *)
  iCombine ("Ha_t Hst_t Hh_t") as "H".
  iPoseProof
    (heap_ctx_alloc _ main.1
       DVALUE_None (({[Addr.null.1:=dvalue_to_block DVALUE_None]}, {[Addr.null.1]})
         , Mem.Singleton [Addr.null.1]) [γf] _ _ _ _ _ DTYPE_Void) as "Halloc_t".
  { cbn; rewrite lookup_singleton_ne; auto. }
  { cbn; set_solver. }
  { constructor. }

  rewrite allocaS_eq /allocaS_def. rewrite /stack.
  cbn. rewrite !insert_empty !union_empty_r_L.
  iSpecialize ("Halloc_t" with "H"). iMod "Halloc_t".

  (* Allocate at [Addr.main] on source side *)
  iCombine ("Ha_s Hst_s Hh_s") as "H".
  iPoseProof
    (heap_ctx_alloc _ main.1
       DVALUE_None
       (({[Addr.null.1:=dvalue_to_block DVALUE_None]}, {[Addr.null.1]}),
         Mem.Singleton [Addr.null.1]) [γf0] _ _ _ _ _ DTYPE_Void) as "Halloc_s".
  { cbn; rewrite lookup_singleton_ne; auto. }
  { cbn; set_solver. }
  { constructor. }

  rewrite allocaS_eq /allocaS_def. rewrite /stack.
  iSpecialize ("Halloc_s" with "H"). iMod "Halloc_s".

  iDestruct "Halloc_t" as "(Hh_t & %Hin_t' & Ha_t & Hs_t & Hv_t & hb_t)".
  iDestruct "Halloc_s" as "(Hh_s & %Hin_s' & Ha_s & Hs_s & Hv_s & hb_s)".

  (* Extend global bij *)
  rewrite !mapsto_dval_eq /mapsto_dval_def.
  iDestruct (heapbij_insert with "Hbij Hv_t Hv_s Hb hb_t hb_s") as ">(H & #Haddr_main)".
  iDestruct "Hg_t" as "#Hg_t"; iDestruct "Hg_s" as "#Hg_s".

  iModIntro.
  iExists Hsh. cbn.

  iSplitR "Hc1 Hf Hs_t Hs_s".
  { iExists ∅, {[(main.1, main.1); (Addr.null.1, Addr.null.1)]},
    (vglobal (init_σ)); iFrame.

    (* Global init *)
    rewrite /globalbij_interp; cbn.
    rewrite !globals_eq /globals_def; cbn. iFrame.
    iDestruct "Haddr_null" as "(Haddr' & %H')".
    iSplitL ""; first set_solver.
    iSplitL ""; first (iSplitL ""; done).
    iSplitL ""; first set_solver.
    iFrame "Hg_t Hg_s".
    cbn.
    unfold init_σ.
    iSpecialize ("Hf" $! _ _ _).
    iApply init_global_WF. }

  (* Initialize state interpretation and resources *)
  rewrite !bind_bind. setoid_rewrite bind_ret_l.
  iApply sim_expr'_bind.
  cbn in WF_name; subst. rewrite WF_name.
  iApply (sim_expr'_bupd_mono with "[Hc1 Hs_t Hs_s]");
    [ | iApply sim_expr_lift; iApply sim_global_read ]; cycle 1.
  { iIntros (??) "H'". iApply "H'". }
  iIntros (??) "(%dv & %dv' & %Hr1 & %Hr2 & #Hdv)".
  rewrite Hr1 Hr2 !bind_ret_l; clear Hr1 Hr2.
  rewrite !bind_bind; setoid_rewrite bind_ret_l.
  iApply sim_expr'_bind.

  iApply (sim_expr'_bupd_mono with "[Hc1 Hf Hs_t Hs_s]");
    [ | iApply mcfg_definitions_refl ]; eauto.
  3, 4: by rewrite globals_eq /globals_def.
  2 : apply init_cfg_WF.

  iIntros (??) "H".
  rename WF_t into WF_fun_t, WF_s into WF_fun_s.
  iDestruct "H" as (??????)
    "(#Hv &  %Hl1 & %Hl2 & #(Hrel & %WF_t & %WF_s & #Hlr))"; subst.

  setoid_rewrite bind_ret_l. iModIntro.

  (* pose proof (mcfg_definitions_leaf _ _ _ _ _ _ Hl1 Hl2) as Hsame. *)
  (* rewrite /mcfg_definitions in Hl1. *)

  iAssert (inv [γf] [γf0])%I with "[Hc1 Hs_t Hs_s]" as "Hinv".
  { iFrame. auto. }

  (* Lemma. Proof of compatibility. *)
  iPoseProof
    (Proper_interp_mrec' _ _ _ _ (λ x y : uvalue, ⌜obs_val x y⌝)%I [γf] [γf0]
      with "Hinv") as "Hrec"; eauto.
  iApply (sim_expr'_bupd_mono with "[] [Hrec]"); last iApply "Hrec".
  { iIntros (??) "HΨ"; iDestruct "HΨ" as (????) "(%HΨ & HI)".
    iExists _, _; iFrame. done. }
  { rewrite /context_rel.

    (* Related contexts *)
    iSplitL ""; [ | iSplitL "" ].
    (* context_call *)
    { iPureIntro. red. split.
      - cbn. intros; eauto.
      - cbn. intros; eauto. }
    { iPureIntro. red. split.
      - cbn. intros; eauto.
      - cbn. intros; eauto. }

    iSplitL ""; cycle 1.
    {  (* REFL *)
      iIntros (??).
      iModIntro.
      iIntros (?????).
      destruct C0 as ((?&?)&?).
      rewrite /arg_val_rel. cbn -[denote_function].
      iIntros "Hev".
      iDestruct "Hev" as "(#HWF & HC & Hst & Hss & #Hfn & #Hargs)".
      subst.

      destruct (lookup_defn fn2 ((dv', e_s) :: r_s))
        eqn: Hs; cycle 1.

      (* External call case *)
      { cbn in Hs. destruct_if; reldec.
        iDestruct (dval_rel_ne_inj with "Hfn Hdv") as %Hne.
        assert (dv' <> fn2) by eauto.
        specialize (Hne H1). cbn -[denote_function].
        destruct (RelDec.rel_dec fn1 dv) eqn: Hfn1; reldec; try done.
        iPoseProof (dval_rel_lookup_none with "Hfn Hv") as "%Hlu".
        rewrite H4.
        rewrite /lookup_defn.
        specialize (Hlu Hs); rewrite Hlu.

        iApply (sim_expr'_bupd_mono);
          last iApply (sim_external_call with "HWF Hst Hss HC Hfn Hargs").

        rewrite /call_ev; cbn. simp vir_call_ev.
        iIntros (??) "H'".
        rewrite /lift_post.
        iDestruct "H'" as (????) "(#Hv' & HC & Hs_t & Hs_s)".
        iExists _, _; iFrame.
        repeat (iSplitL ""; first done).
        simp vir_call_ans; by iFrame. }

      (* Internal call case *)
      { rewrite /fundefs_rel_WF.

        apply lookup_defn_cons_Some in Hs.
        destruct Hs.
        (* It is the [e_s] function (the hole) *)
        { destruct H0; subst; cbn -[denote_function].
          iDestruct (dval_rel_inj with "Hdv Hfn") as %Hdef; subst.
          destruct (RelDec.rel_dec fn1 fn1) eqn: Hf; reldec; subst; last done.
          destruct (RelDec.rel_dec dv' dv') eqn: Hf'; reldec; subst; last done.
          subst.

          iDestruct "HWF" as %HWF; subst.

          iSpecialize ("Hf" $! _ _ _ _ _ HWF with "Hst Hss Hargs").
          rewrite WF_attr_t WF_attr_s.

          (* FIXME This is where we need to assume that the function satisfies
              the specification on the attributes. *)

          (* In our logical relation, we should state instead that the protocols
           hold for the functions. *)

          (* TODO: Not enough of an assumption for the internal call *)
          (* iApply sim_expr'_bupd_mono; last (iApply "Hf'"). *)
          (* iIntros (??) "H'". *)
          (* rewrite /lift_post. *)
          (* iDestruct "H'" as (????) "(Hs_t & Hs_s & HC & Hval)". *)
          (* iExists _, _; iFrame. subst; iModIntro. *)
          (* repeat (iSplitL ""; first done). *)
          (* simp vir_call_ans; by iFrame. } *)
          admit. }

        (* It is a function in the context *)
        { destruct H0. cbn -[denote_function].

          iDestruct (dval_rel_ne_inj with "Hdv Hfn") as "%Hne"; subst.
          specialize (Hne H0); subst.
          destruct (RelDec.rel_dec fn1 dv) eqn: Hf; reldec; subst; first done.
          destruct (RelDec.rel_dec fn2 dv') eqn: Hf'; reldec; subst; first done.
          clear H2 Hne Hf.
          iPoseProof (dval_rel_lookup_some with "Hfn Hv") as "%Hlu".
          specialize (Hlu _ H1). destruct Hlu as (?&?).
          rewrite /lookup_defn in H1.
          rewrite /lookup_defn; rewrite H1 H2.

          (* Juicing out information from the WF of fundefs *)
          unfold fundefs_WF in WF_s.
          apply andb_prop_elim in WF_s.
          destruct WF_s as (Hlen & Wdup_s).
          apply andb_prop_elim in Hlen. destruct Hlen as (Hlen & Hfun_wf).
          apply forallb_True in Hfun_wf.
          rewrite List.Forall_forall in Hfun_wf.
          assert (Hr_s := H1).
          apply lookup_defn_Some_In in H1.
          (* Function [d] is well-formed. *)
          specialize (Hfun_wf _ H1); cbn in Hfun_wf.

          (* Using [fundefs_logrel] *)
          assert (Hlen': (length [γf0] > 0)%Z → (length [γf] > 0)%Z) by auto.
          rewrite /fundefs_logrel. rewrite /lookup_defn in Hr_s.
          apply lookup_defn_Some_lookup in Hr_s.
          destruct Hr_s.
          (* Juice information out of fundef rel WF *)
          iDestruct "Hrel" as "(Hrel & Hn)".
          iSpecialize ("Hrel" $! _ _ _ H4).
          iDestruct "Hrel" as (???) "(#Hdv' & %Hattr & %Hattr' & %Hft & %Hfs)".

          iDestruct (dval_rel_inj with "Hfn Hdv'") as %Hf; subst.

          iSpecialize ("Hlr" $! _ _ _ _ _ _ H5 H4 Hattr Hattr'
                        with "Hdv'").
          iDestruct "HWF" as %HWF.
          (* TODO: Again, some constraint that says that [g] is ∅ *)
          (* iSpecialize ("Hlr" $! _ _ _ _ HWF with "Hst Hss Hargs HC"). *)

          eapply lookup_defn_Some in H2; eauto;cycle 1.
          { clear -WF_t.

            unfold fundefs_WF in WF_t.
            apply andb_prop_elim in WF_t.
            destruct WF_t as (Hlen & Wdup_t).
            apply andb_prop_elim in Hlen. destruct Hlen as (Hlen & Hfun_wf).
            apply forallb_True in Hfun_wf.
            rewrite List.Forall_forall in Hfun_wf.
            apply Is_true_true_1 in Wdup_t.
            by apply NoDup_b_NoDup. }
          subst.

          (* TODO
              Assume that everything in context has the empty attribute *)
          admit. } } }
          (* iApply sim_expr'_bupd_mono; last iApply "Hlr". *)
          (* iIntros (??) "Hin". *)
          (* iDestruct "Hin" as (????) "(Hst & Hss & HC & Hval)". *)
          (* iExists _, _. *)
          (* repeat (iSplitL ""; first done). *)
          (* simp vir_call_ans; subst; by iFrame. } } } *)

    { (* CALL INV *)
      iIntros (??).
      iModIntro.
      iIntros (???????).
      destruct C0 as ((?&?)&?).
      rewrite /call_ev. cbn -[denote_function].
      iIntros "Hev".


      (* --------------------------------------------- *)

      simp vir_call_ev.
      iDestruct "Hev" as
        "(#Hfn &%Hdt & %Hattr& #Hargs & HC & #HWF & Hst & Hss & %Hinterp)".
      subst.

      destruct (lookup_defn fn2 ((dv', e_s) :: r_s))
        eqn: Hs; cycle 1.

      (* External call case *)
      { cbn in Hs. destruct_if; reldec.
        iDestruct (dval_rel_ne_inj with "Hfn Hdv") as %Hne.
        assert (dv' <> fn2) by eauto.
        specialize (Hne H1). cbn -[denote_function].
        destruct (RelDec.rel_dec fn1 dv) eqn: Hfn1; reldec; try done.
        iPoseProof (dval_rel_lookup_none with "Hfn Hv") as "%Hlu".
        rewrite /lookup_defn.
        specialize (Hlu Hs); rewrite Hlu.

        rewrite /call_ev; cbn; simp vir_call_ev.
        rewrite /lookup_defn in Hs. rewrite Hs.

        (* specialize (WF_attr _ _ _ _ _ _ _ _ Hinterp); subst. *)
        (* TODO: Again *)

        iApply (sim_expr'_bupd_mono);
          last iApply (sim_external_call with "HWF Hst Hss HC Hfn Hargs").
        iIntros (??) "H'".
        rewrite /lift_post.
        iDestruct "H'" as (????) "(#Hv' & HC & Hs_t & Hs_s)".
        iExists _, _; iFrame.
        repeat (iSplitL ""; first done).
        simp vir_call_ans; by iFrame. }

      (* Internal call case *)
      { rewrite /fundefs_rel_WF.

        apply lookup_defn_cons_Some in Hs.
        destruct Hs.
        (* It is the [e_s] function (the hole) *)
        { destruct H2; subst; cbn -[denote_function].
          iDestruct (dval_rel_inj with "Hdv Hfn") as %Hdef; subst.
          destruct (RelDec.rel_dec fn1 fn1) eqn: Hf; reldec; subst; last done.
          destruct (RelDec.rel_dec dv' dv') eqn: Hf'; reldec; subst; last done.
          subst.

          iDestruct "HWF" as %HWF; subst.
          iDestruct ("Hf" $! _ _ _) as "(_ & Hf')".
          specialize (WF_attr _ _ _ _ _ _ _ _ Hinterp); subst.

          iSpecialize ("Hf'" $! _ _ _ _ HWF with "Hst Hss Hargs HC").
          iApply sim_expr'_bupd_mono; last (iApply "Hf'").
          iIntros (??) "H'".
          rewrite /lift_post.
          iDestruct "H'" as (????) "(Hs_t & Hs_s & HC & Hval)".
          iExists _, _; iFrame. subst; iModIntro.
          repeat (iSplitL ""; first done).
          simp vir_call_ans; by iFrame. }

        (* It is a function in the context *)
        { destruct H2. cbn -[denote_function].

          iDestruct (dval_rel_ne_inj with "Hdv Hfn") as "%Hne"; subst.
          specialize (Hne H2); subst.
          destruct (RelDec.rel_dec fn1 dv) eqn: Hf; reldec; subst; first done.
          destruct (RelDec.rel_dec fn2 dv') eqn: Hf'; reldec; subst; first done.
          clear H2 Hne Hf.
          iPoseProof (dval_rel_lookup_some with "Hfn Hv") as "%Hlu".
          specialize (Hlu _ H3). destruct Hlu as (?&?).
          rewrite /lookup_defn in H3.
          rewrite /lookup_defn; rewrite H2 H3.

          (* Juicing out information from the WF of fundefs *)
          unfold fundefs_WF in WF_s.
          apply andb_prop_elim in WF_s.
          destruct WF_s as (Hlen & Wdup_s).
          apply andb_prop_elim in Hlen. destruct Hlen as (Hlen & Hfun_wf).
          apply forallb_True in Hfun_wf.
          rewrite List.Forall_forall in Hfun_wf.
          assert (Hr_s := H3).
          apply lookup_defn_Some_In in H3.
          (* Function [d] is well-formed. *)
          specialize (Hfun_wf _ H3); cbn in Hfun_wf.

          (* Using [fundefs_logrel] *)
          assert (Hlen': (length [γf0] > 0)%Z → (length [γf] > 0)%Z) by auto.
          rewrite /fundefs_logrel. rewrite /lookup_defn in Hr_s.
          apply lookup_defn_Some_lookup in Hr_s.
          destruct Hr_s.
          (* Juice information out of fundef rel WF *)
          iDestruct "Hrel" as "(Hrel & Hn)".
          iSpecialize ("Hrel" $! _ _ _ H6).
          iDestruct "Hrel" as (???) "(#Hdv' & %Hattr & %Hattr' & %Hft & %Hfs)".

          iDestruct (dval_rel_inj with "Hfn Hdv'") as %Hf; subst.

          specialize (WF_attr _ _ _ _ _ _ _ _ Hinterp); subst.
          iSpecialize ("Hlr" $! _ _ _ _ _ _ H7 H6 Hattr Hattr'
                        with "Hdv'").
          iDestruct "HWF" as %HWF.
          iSpecialize ("Hlr" $! _ _ _ _ HWF with "Hst Hss Hargs HC").

          eapply lookup_defn_Some in H2; eauto;cycle 1.
          { clear -WF_t.

            unfold fundefs_WF in WF_t.
            apply andb_prop_elim in WF_t.
            destruct WF_t as (Hlen & Wdup_t).
            apply andb_prop_elim in Hlen. destruct Hlen as (Hlen & Hfun_wf).
            apply forallb_True in Hfun_wf.
            rewrite List.Forall_forall in Hfun_wf.
            apply Is_true_true_1 in Wdup_t.
            by apply NoDup_b_NoDup. }
          subst.

          iApply sim_expr'_bupd_mono; last iApply "Hlr".
          iIntros (??) "Hin".
          iDestruct "Hin" as (????) "(Hst & Hss & HC & Hval)".
          iExists _, _.
          repeat (iSplitL ""; first done).
          simp vir_call_ans; subst; by iFrame. } } } }

  (* Other obligation that "feels like a duplicate obligation",
   but is a separate one coming from the body of the [mrec] *)
  { iModIntro. iIntros "(#HWF & HC & Hst & Hss)".

    iAssert (dval_rel (DVALUE_Addr main) (DVALUE_Addr main))%I as "#Hmain".
    { rewrite (dval_rel_unfold (DVALUE_Addr _)).
      cbn. iSplitL ""; try done.
      iDestruct "Haddr_main" as "(Haddr_main & _)"; done. }

    destruct (lookup_defn (DVALUE_Addr main) ((dv', e_s) :: r_s))
      eqn: Hs; cycle 1.

    (* External call case *)
    { cbn in Hs. destruct_if; reldec.
      iDestruct (dval_rel_ne_inj with "Hmain Hdv") as %Hne.
      assert (dv' <> DVALUE_Addr main) by eauto.
      specialize (Hne H3). cbn -[denote_function map_monad].
      destruct (RelDec.rel_dec (DVALUE_Addr main) dv) eqn: Hfn1;
        reldec; try done.
      iPoseProof (dval_rel_lookup_none with "Hmain Hv") as "%Hlu".
      rewrite /lookup_defn.
      specialize (Hlu Hs); rewrite Hlu.

      iApply (sim_expr'_bupd_mono);
        last iApply (sim_external_call with "HWF Hst Hss HC Hmain"); try done.
      iIntros (??) "H'".
      rewrite /lift_post.
      iDestruct "H'" as (????) "(#Hv' & HC & Hs_t & Hs_s)".
      iExists _, _; iFrame.
      repeat (iSplitL ""; first done).
      (iSplitR ""; last done).

      iApply (uval_rel_implies_obs_val with "Hv'"). }

    (* Internal call case *)
    { apply lookup_defn_cons_Some in Hs.
      destruct Hs.
      (* It is the [e_s] function (the hole) *)
      { destruct H2; inv H2; subst. cbn -[denote_function].
        iDestruct (dval_rel_inj with "Hdv Hmain") as %Hdef; subst.
        destruct (RelDec.rel_dec (DVALUE_Addr main) (DVALUE_Addr main))
          eqn: Hf; reldec; subst; last done.
        rewrite /fun_logrel.
        iDestruct "HWF" as %HWF.
        iDestruct ("Hf" $! _ _ _) as "(_ & Hf')".

        iSpecialize ("Hf'" $! _ _ nil nil HWF with "Hst Hss").
        cbn -[denote_function].
        iSpecialize ("Hf'" $! Logic.I with "HC").

        iApply sim_expr'_bupd_mono; last (iApply "Hf'").
        iIntros (??) "H'".
        rewrite /lift_post.
        iDestruct "H'" as (????) "(Hs_t & Hs_s & HC & Hval)".
        iExists _, _; iFrame. subst; iModIntro.
        repeat (iSplitL ""; first done).
        (iSplitR ""; last done).
        iApply (uval_rel_implies_obs_val with "Hval"). }

      (* It is a function in the context *)
      { destruct H2; cbn -[denote_function].

        iDestruct (dval_rel_ne_inj with "Hdv Hmain") as "%Hne"; subst.
        specialize (Hne H2); subst.
        destruct (RelDec.rel_dec (DVALUE_Addr main) dv) eqn: Hf;
          reldec; subst; first done.
        clear H2 Hne Hf.
        iPoseProof (dval_rel_lookup_some with "Hmain Hv") as "%Hlu".
        specialize (Hlu _ H3). destruct Hlu as (?&?).
        rewrite /lookup_defn H2.

        (* Juicing out information from the WF of fundefs *)
        unfold fundefs_WF in WF_s.
        apply andb_prop_elim in WF_s.
        destruct WF_s as (Hlen & Wdup_s).
        apply andb_prop_elim in Hlen. destruct Hlen as (Hlen & Hfun_wf).
        apply forallb_True in Hfun_wf.
        rewrite List.Forall_forall in Hfun_wf.
        assert (Hr_s := H3).
        apply lookup_defn_Some_In in H3.
        (* Function [d] is well-formed. *)
        specialize (Hfun_wf _ H3); cbn in Hfun_wf.

        (* Using [fundefs_logrel] *)
        assert (Hlen': (length [γf0] > 0)%Z → (length [γf] > 0)%Z) by auto.
        rewrite /fundefs_logrel.
        apply lookup_defn_Some_lookup in Hr_s.
        destruct Hr_s.
        (* Juice information out of fundef rel WF *)
        iDestruct "Hrel" as "(Hrel & Hn)".
        iSpecialize ("Hrel" $! _ _ _ H6).
        iDestruct "Hrel" as (???)
                              "(#Hdv' & %Hattr & %Hattr' & %Hft & %Hfs)".

        iSpecialize ("Hlr" $! _ _ _ _ _ _ H7 H6 Hattr Hattr'
                      with "Hdv'").
        iSpecialize ("Hlr" $! _ _ nil nil Hlen' with "Hst Hss").
        cbn -[denote_function].
        iSpecialize ("Hlr" $! Logic.I with "HC").

        iDestruct (dval_rel_inj with "Hmain Hdv'") as %Hf; subst.

        eapply lookup_defn_Some in H2; eauto;cycle 1.
        { clear -WF_t.

          unfold fundefs_WF in WF_t.
          apply andb_prop_elim in WF_t.
          destruct WF_t as (Hlen & Wdup_t).
          apply andb_prop_elim in Hlen. destruct Hlen as (Hlen & Hfun_wf).
          apply forallb_True in Hfun_wf.
          rewrite List.Forall_forall in Hfun_wf.
          apply Is_true_true_1 in Wdup_t.
          by apply NoDup_b_NoDup. }
        eauto.
        subst.

        iApply sim_expr'_bupd_mono; last iApply "Hlr".
        iIntros (??) "Hin".
        iDestruct "Hin" as (????) "(Hst & Hss & HC & Hval)".
        iExists _, _; subst.
        repeat (iSplitL ""; first done); iFrame.
        (iSplitR ""; last done).

        iApply (uval_rel_implies_obs_val with "Hval"). } } }
    Unshelve.
    all : eauto. all: do 2 constructor.

Qed.
