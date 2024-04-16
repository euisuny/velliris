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

  Context (ds : list (declaration dtyp)).

  (* If the initial states are related by some relation, and the expressions
     are well formed (i.e. the source program does not "go wrong" and the
     expressions are closed after denotation), then the resulting programs
     are observationally equivalent to each other using [eutt]. *)
  Definition prog_ref (e_t e_s : expr vir_lang uvalue) :=
    let σ := init_state ds in
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
      (* The context needs to be well-formed *)
      ctx_wf C ->
      (* The names of the declarations are the same *)
      dc_name (df_prototype e_t.2) = dc_name (df_prototype e_s.2) ->
      (* Implies whole-program refinement *)
      prog_ref (m_declarations C) (fill_ctx C e_t) (fill_ctx C e_s).

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

(* Section CR_properties. *)

(*   Context {Σ} `{!sheapGS Σ, !checkedoutGS Σ, !heapbijGS Σ}. *)
(*   Context (ret_typ : dtyp) (main : Addr.addr) (args : list uvalue). *)

(*   (* (* TODO *) *) *)
(*   (* Lemma contains_keys_init_global names : *) *)
(*   (*   contains_keys (init_global names) names. *) *)
(*   (* Proof. *) *)
(*   (*   induction names; cbn; eauto; first set_solver. *) *)
(*   (*   rewrite /contains_keys. cbn. rewrite /init_global; cbn. *) *)
(*   (* Admitted. *) *)

(*   (* (* TODO *) *) *)
(*   (* Lemma nodup_codomain_init_global names : *) *)
(*   (*   NoDup_codomain (filter_keys (init_global names) names). *) *)
(*   (* Proof. Admitted. *) *)

(*   Lemma ctx_wf_implies_CFG_WF C : *)
(*    ctx_wf C -> *)
(*    CFG_WF C (init_global (CFG_names C)) (init_global (CFG_names C)). *)
(*   Proof. *)
(*     intros (?&?&?&?). *)
(*     repeat (split; eauto); *)
(*       eauto using contains_keys_init_global, nodup_codomain_init_global. *)
(*   Qed. *)

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

(* End CR_properties. *)

(* Well-formedness on globals: all global values are self-related *)
Definition globals_WF `{heapbijGS Σ} (g : global_env) : iPropI Σ :=
  ([∗ map] g0↦v ∈ g, ∃ v' : dvalue, ⌜g !! g0 = Some v'⌝ ∗ dval_rel v' v)%I.

Definition init_keys (main : Addr.addr) : list global_id :=
  Raw main.1 :: Raw Addr.null.1 :: nil.

(* We can instantiate a state interpretation with corresponding ghost resources
  on states that satisfy the initializaition relation [I] *)
(* IY : Is there a cleaner way to state this lemma? *)
Lemma initialize_state_interp ds `{sheapGpreS Σ} `{heapbijGpreS Σ} `{checkedoutGpreS Σ} :
  forall e_t e_s,
    (* let init_keys := init_keys main in *)
    (∀ `(sheapGS Σ, checkedoutGS Σ, heapbijGS Σ),
        <pers> fun_logrel e_t e_s ∅) ==∗
    ∃ (H_sh : sheapGS Σ) (H_bij : heapbijGS Σ) (H_c : checkedoutGS Σ),
      state_interp (init_state ds) (init_state ds) ∗
      target_globals (vglobal (init_state ds)) ∗
      source_globals (vglobal (init_state ds)) ∗
    ∃ γ_t γ_s,
        checkout ∅ ∗ stack_tgt [γ_t] ∗ stack_src [γ_s].
Proof.
  rename H into H_shp, H0 into H_bijp, H1 into H_cp.
(*   intros * HI. *)

(*   iMod (@sheap_init Σ _ g g) as (Hsh) "(Hh_t & Hh_s & H)". *)
(*   iMod (@heapbij_init Σ _ _ ∅) as (Hhb) "Hbij". *)
(*   iMod (@checkedout_init Σ _ ∅) as (Hc) "[Hc1 Hc2]". *)

(*   rewrite /state_interp. *)

(*   iDestruct "H" as "(Hh_tf & Hb_t & Hg_t & Hh_sf & Hb_s & Hg_s & H)". *)

(*   iDestruct "H" as "(Ht & Hs)". *)
(*   iDestruct "Ht" as (?) "(Hst_t & Hl_t & Hld_t & Ha_t)". *)
(*   iDestruct "Hs" as (?) "(Hst_s & Hl_s & Hld_s & Ha_s)". *)

(*   (* Allocate null bij *) *)
(*   destruct σ_t as ((?&?&?)&(?&?)&?). *)
(*   destruct σ_s as ((?&?&?)&(?&?)&?). *)

(*   destruct HI as (Hun & ?&?&?&?&?&?); subst; inv H3. *)
(*   destruct H as (?&?&?&?&?); subst; inv H2. *)

(*   (** *Allocate null address *) *)
(*   (* Allocate at [Addr.null] on target side *) *)
(*   iCombine ("Ha_t Hst_t Hh_t") as "H". *)
(*   iPoseProof *)
(*     (heap_ctx_alloc _ Addr.null.1 *)
(*        DVALUE_None ((∅, ∅), Singleton ∅) [γf] _ _ _ _ _ DTYPE_Void) as "Halloc_t"; *)
(*     [ set_solver | cbn; set_solver | constructor | ]. *)
(*   rewrite allocaS_eq /allocaS_def. rewrite /stack. *)
(*   iSpecialize ("Halloc_t" with "H"). iMod "Halloc_t". *)

(*   (* Allocate at [Addr.null] on source side *) *)
(*   iCombine ("Ha_s Hst_s Hh_s") as "H". *)
(*   iPoseProof *)
(*     (heap_ctx_alloc _ Addr.null.1 *)
(*        DVALUE_None ((∅, ∅), Singleton ∅) [γf0] _ _ _ _ _ DTYPE_Void) as "Halloc_s"; *)
(*     [ set_solver | cbn; set_solver | constructor | ]. *)
(*   rewrite allocaS_eq /allocaS_def. rewrite /stack. *)
(*   iSpecialize ("Halloc_s" with "H"). iMod "Halloc_s". *)

(*   iDestruct "Halloc_t" as "(Hh_t & %Hin_t & Ha_t & Hst_t & Hv_t & hb_t)". *)
(*   iDestruct "Halloc_s" as "(Hh_s & %Hin_s & Ha_s & Hst_s & Hv_s & hb_s)". *)

(*   (* Extend global bij *) *)
(*   rewrite !mapsto_dval_eq /mapsto_dval_def. *)
(*   iAssert (lb_rel (dvalue_to_block DVALUE_None) (dvalue_to_block DVALUE_None))%I as "Hb". *)
(*   { rewrite /lb_rel. cbn. *)
(*     rewrite /mem_byte_rel. rewrite /init_block; cbn. *)
(*     simpl. iSplit. *)
(*     { iIntros (???). inversion H. } *)
(*     { done. } } *)
(*   iDestruct (heapbij_insert with "Hbij Hv_t Hv_s Hb hb_t hb_s") as ">(Hbij & #Haddr_null)". *)

(*   (** *Allocate main address *) *)
(*   (* Allocate at [Addr.main] on target side *) *)
(*   iCombine ("Ha_t Hst_t Hh_t") as "H". *)
(*   iPoseProof *)
(*     (heap_ctx_alloc _ main.1 *)
(*        DVALUE_None (({[Addr.null.1:=dvalue_to_block DVALUE_None]}, {[Addr.null.1]}) *)
(*          , Mem.Singleton [Addr.null.1]) [γf] _ _ _ _ _ DTYPE_Void) as "Halloc_t". *)
(*   { cbn; rewrite lookup_singleton_ne; auto. } *)
(*   { cbn; set_solver. } *)
(*   { constructor. } *)

(*   rewrite allocaS_eq /allocaS_def. rewrite /stack. *)
(*   cbn. rewrite !insert_empty !union_empty_r_L. *)
(*   iSpecialize ("Halloc_t" with "H"). iMod "Halloc_t". *)

(*   (* Allocate at [Addr.main] on source side *) *)
(*   iCombine ("Ha_s Hst_s Hh_s") as "H". *)
(*   iPoseProof *)
(*     (heap_ctx_alloc _ main.1 *)
(*        DVALUE_None (({[Addr.null.1:=dvalue_to_block DVALUE_None]}, {[Addr.null.1]}) *)
(*          , Mem.Singleton [Addr.null.1]) [γf0] _ _ _ _ _ DTYPE_Void) as "Halloc_s". *)
(*   { cbn; rewrite lookup_singleton_ne; auto. } *)
(*   { cbn; set_solver. } *)
(*   { constructor. } *)

(*   rewrite allocaS_eq /allocaS_def. rewrite /stack. *)
(*   iSpecialize ("Halloc_s" with "H"). iMod "Halloc_s". *)

(*   iDestruct "Halloc_t" as "(Hh_t & %Hin_t' & Ha_t & Hs_t & Hv_t & hb_t)". *)
(*   iDestruct "Halloc_s" as "(Hh_s & %Hin_s' & Ha_s & Hs_s & Hv_s & hb_s)". *)

(*   (* Extend global bij *) *)
(*   rewrite !mapsto_dval_eq /mapsto_dval_def. *)
(*   iDestruct (heapbij_insert with "Hbij Hv_t Hv_s Hb hb_t hb_s") as ">(H & #Haddr_main)". *)
(*   iDestruct "Hg_t" as "#Hg_t"; iDestruct "Hg_s" as "#Hg_s". *)

(*   iIntros "#Hf". *)
(*   iDestruct ("Hf" $! Hsh Hc Hhb) as "[Hg _]". *)

(*   iModIntro. *)
(*   iExists Hsh, Hhb, Hc. *)

(*   iSplitR "Hc2 Hs_t Hs_s". *)
(*   { iExists ∅, {[(main.1, main.1); (Addr.null.1, Addr.null.1)]}, g; iFrame. *)

(*     (* Global init *) *)
(*     rewrite /spec.globalbij_interp; cbn. *)
(*     rewrite !globals_eq /globals_def; cbn. iFrame. *)
(*     iDestruct "Haddr_null" as "(Haddr' & %H')". *)
(*     iSplitL "". { iPureIntro; set_solver. } *)
(*     iSplitL "". { iSplitL ""; done. } *)
(*     iSplitL "". { iPureIntro; set_solver. } *)
(*     iFrame "Hg_t Hg_s". done. } *)
(*   rewrite !globals_eq /globals_def. iFrame "Hg_t Hg_s". *)
(*   iExists γf, γf0; iFrame. *)
(* Qed. *)
Admitted.

(* The contextual refinement statement, with ghost state instantiated *)
Lemma contextual_ref `(vellirisGS Σ):
  ∀ e_t e_s γ_t γ_s C decl main,
  (* Well-formedness conditions *)
  ctx_wf C ->
  (* The names of the declarations are the same *)
  dc_name (df_prototype e_t) = dc_name (df_prototype e_s) ->
  (* The ghost resources for globals is set up *)
  (* target_globals (init_global (CFG_names C)) -∗ *)
  (* source_globals (init_global (CFG_names C)) -∗ *)
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
  iIntros (??????? H_wf WF_name) "#Hfun Hstack".

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
  2-4 : admit.

  iIntros (??) "H".
  iDestruct "H" as (????????)
    "(#Hv &  %Hl1 & %Hl2 & #(Hrel & %WF_t & %WF_s & #Hlr))"; subst.

  setoid_rewrite bind_ret_l. iModIntro.

  pose proof (mcfg_definitions_leaf _ _ _ _ _ _ Hl1 Hl2) as Hsame. subst.
  rewrite /mcfg_definitions in Hl1; iClear "Hrel Hlr".

  (* IY: This is the difficult part; WIP version is in [mcfg_contextual.v] *)
   iApply (contextual_denote_mcfg with "Hfun Hc Hs_t Hs_s").
Admitted.


(** *Top-level soundness theorem *)
Theorem soundness `{sheapGpreS Σ} `{heapbijGpreS Σ} `{checkedoutGpreS Σ}
  e_t e_s main decl:
  isat (∀ `(sheapGS Σ, checkedoutGS Σ, heapbijGS Σ),
        <pers> fun_logrel e_t e_s ∅) ->
  ctx_ref DTYPE_Void main [] (decl, e_t) (decl, e_s).
Proof.
  intros Hf C WF WF_name WF_pr.

  (* Use adequacy to move into the Iris logic *)
  eapply (@adequacy Σ isat); eauto; try typeclasses eauto; eapply sat_mono, Hf. clear Hf.

  iStartProof; iIntros "#Hf".

  (* Initialize state interpretation and resources *)
  iPoseProof (initialize_state_interp with "Hf") as ">SI".
  iDestruct "SI" as (???) "[SI [#Hg_t [#Hg_s [%γ_t [%γ_s Hc]]]]]".
  iExists H_sh, H_bij, H_c; iFrame.
  iSpecialize ("Hf" $! _ _ _).

  (* Follows by contextual refinement. *)
  iApply (contextual_ref with "Hg_t Hg_s He Hc"); eauto.
Admitted.
