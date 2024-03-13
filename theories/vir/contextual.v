From iris.prelude Require Import options.

From velliris.logic Require Import satisfiable.
From velliris.program_logic Require Import program_logic.
From velliris.vir Require Import vir logical_relations fundamental.

From Vellvm Require Import Syntax.DynamicTypes Handlers Syntax.LLVMAst
  Semantics.InterpretationStack.

Import LLVMEvents.

Set Default Proof Using "Type*".

(** *Top-level Contextual Refinement *)
Section CR_definition.

  Context (Σ : gFunctors).
  Context (I : vir_state -> vir_state -> Prop).
  Context (ret_typ : dtyp) (main : Addr.addr)
          (args : list uvalue)
          (main_function : definition dtyp (CFG.cfg dtyp))
          (glo_t glo_s : vir.globals).

  Import CFG.

  Definition hole (C : CFG.mcfg dtyp) (e : declaration dtyp * definition dtyp (CFG.cfg dtyp)) :=
    {| m_name := m_name C;
      m_target := m_target C;
      m_datalayout := m_datalayout C;
      m_type_defs := m_type_defs C;
      m_globals := m_globals C;
      m_declarations := e.1 :: m_declarations C;
      m_definitions := e.2 :: m_definitions C
    |}.
  Opaque hole.

  Definition context (C : CFG.mcfg dtyp) e :=
      Monad.bind (mcfg_definitions (hole C e))
        (fun defs => denote_mcfg defs ret_typ (DVALUE_Addr main) args).

  Notation " C ⎨ e_t ⎬ " := (context C e_t) (at level 40).

  Definition attributes (C : CFG.mcfg dtyp) := dc_attrs <$> CFG.m_declarations C.

  Definition contextual_refinement e_t e_s: Prop :=
    forall (C : CFG.mcfg dtyp) σ_t σ_s,
      (* Assuming some initial relation on states, *)
      I σ_t σ_s ->
      (* The names of the declarations are the same *)
      dc_name (df_prototype e_t.2) = dc_name (df_prototype e_s.2) ->
      (* The hole and context are syntactically well-formed *)
      CFG_WF (hole C e_t) glo_t glo_s ->
      CFG_WF (hole C e_s) glo_t glo_s ->
      well_formed (⟦ C ⎨ e_t ⎬ ⟧ σ_t) (⟦ C ⎨ e_s ⎬ ⟧ σ_s) ->
      eutt obs_val_res (⟦ C ⎨ e_t ⎬ ⟧ σ_t) (⟦ C ⎨ e_s ⎬ ⟧ σ_s).

End CR_definition.

Section CR_properties.

  Context {Σ} `{!sheapGS Σ, !checkedoutGS Σ, !heapbijGS Σ}.

  Lemma CFG_WF_hole C decl e_t g_t g_s:
    CFG_WF (hole C (decl, e_t)) g_t g_s ->
    CFG_WF C g_t g_s.
  Proof.
    rewrite /CFG_WF.
    intros. destructb.
    apply nodup_codomain_cons_inv in H5,H6; eauto.
    cbn in *. split; eauto. nodup.
    apply contains_keys_cons_inv in H3, H4.
    apply Forall_cons in H1, H2.
    destructb.
    repeat split; eauto.
  Qed.

  Lemma CFG_WF_hole_attr C decl e_t g_t g_s:
    CFG_WF (hole C (decl, e_t)) g_t g_s ->
    (dc_attrs decl = nil).
  Proof.
    rewrite /CFG_WF.
    intros. destructb.
    clear -H2. cbn in *.
    apply Forall_cons in H2; by destructb.
  Qed.

End CR_properties.

(* Initial relation on states; there is a [main] and [null] address in the state
  where the [main] and [null] addresses are not equivalent to each other.

  The memory and frame is empty except for the main and null address. *)
Definition I (main : addr) glo_t glo_s : vir_state -> vir_state -> Prop :=
  fun '(g_t, (l_t, ls_t), (m_t, f_t)) '(g_s, (l_s, ls_s), (m_s, f_s)) =>
  main.1 <> Addr.null.1 /\
  g_t = glo_t /\ g_s = glo_s
  /\ l_t = nil /\ l_s = nil
  /\ ls_t = nil /\ ls_s = nil
  /\ m_t = ({[ main.1 := dvalue_to_block DVALUE_None;
              Addr.null.1 := dvalue_to_block DVALUE_None ]},
            {[ main.1; Addr.null.1 ]})
  /\ m_s = ({[ main.1 := dvalue_to_block DVALUE_None;
              Addr.null.1 := dvalue_to_block DVALUE_None ]},
            {[ main.1; Addr.null.1 ]})
  /\ f_t = Mem.Singleton [ main.1; Addr.null.1 ]
  /\ f_s = Mem.Singleton [ main.1; Addr.null.1 ].

(** *Top-level soundness theorem *)
Theorem soundness `{sheapGpreS Σ} `{heapbijGpreS Σ} `{checkedoutGpreS Σ}
  e_t e_s main decl g:
  isat (∀ `(sheapGS Σ, checkedoutGS Σ, heapbijGS Σ),
    globals_WF g ∗ <pers> fun_logrel e_t e_s ∅) ->
  contextual_refinement (I main g g) DTYPE_Void main [] g g
      (decl, e_t) (decl, e_s).
Proof.
  intros Hf C ?? HI WF_name WF_cfg1 WF_cfg2 WF.
  eapply (@adequacy Σ isat); eauto; try typeclasses eauto.

  eapply sat_mono, Hf. clear Hf.
  iStartProof. iIntros "#Hf".

  iMod (@sheap_init Σ _ g g) as (Hsh) "(Hh_t & Hh_s & H)".
  iMod (@heapbij_init Σ _ _ ∅) as (Hhb) "Hbij".
  iMod (@checkedout_init Σ _ ∅) as (Hc) "[Hc1 Hc2]".

  rewrite /state_interp.

  iDestruct "H" as "(Hh_tf & Hb_t & Hg_t & Hh_sf & Hb_s & Hg_s & H)".

  iDestruct "H" as "(Ht & Hs)".
  iDestruct "Ht" as (?) "(Hst_t & Hl_t & Hld_t & Ha_t)".
  iDestruct "Hs" as (?) "(Hst_s & Hl_s & Hld_s & Ha_s)".

  (* Allocate null bij *)
  destruct σ_t as ((?&?&?)&(?&?)&?).
  destruct σ_s as ((?&?&?)&(?&?)&?).

  Opaque context.
  destruct HI as (Hun & ?&?&?&?&?&?&?&?&?&?); subst.
  inv H8; inv H9.

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
    { iIntros (???). inversion H2. }
    { done. } }
  iDestruct (heapbij_insert with "Hbij Hv_t Hv_s Hb hb_t hb_s") as ">(Hbij & #Haddr_null)".

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
       DVALUE_None (({[Addr.null.1:=dvalue_to_block DVALUE_None]}, {[Addr.null.1]})
         , Mem.Singleton [Addr.null.1]) [γf0] _ _ _ _ _ DTYPE_Void) as "Halloc_s".
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
  iExists Hsh, Hhb, Hc. cbn.

  iSplitR "Hc1 Hf Hs_t Hs_s".
  { iExists ∅, {[(main.1, main.1); (Addr.null.1, Addr.null.1)]}, g; iFrame.

    (* Global init *)
    rewrite /globalbij_interp; cbn.
    rewrite !globals_eq /globals_def; cbn. iFrame.
    iDestruct "Haddr_null" as "(Haddr' & %H')".
    iSplitL ""; first set_solver.
    iSplitL ""; first (iSplitL ""; done).
    iSplitL ""; first set_solver.
    iFrame "Hg_t Hg_s".
    iSpecialize ("Hf" $! _ _ _). iDestruct "Hf" as "(Hf & H)".
    done. }

  (* Initialize state interpretation and resources *)
  Transparent context. cbn.
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
    [ | iApply mcfg_definitions_refl' ]; eauto.
  3, 4: by rewrite globals_eq /globals_def.
  2 : by eapply CFG_WF_hole.

  iIntros (??) "H".
  iDestruct "H" as (????????)
    "(#Hv &  %Hl1 & %Hl2 & #(Hrel & %WF_t & %WF_s & #Hlr))"; subst.

  setoid_rewrite bind_ret_l. iModIntro.

  pose proof (mcfg_definitions_leaf _ _ _ _ _ _ Hl1 Hl2) as Hsame. subst.
  rewrite /mcfg_definitions in Hl1.

  iAssert (inv [γf] [γf0])%I with "[Hc1 Hs_t Hs_s]" as "Hinv".
  { iFrame. auto. }

  rewrite -H4 in H5.
  Admitted.
