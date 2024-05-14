From iris.prelude Require Import options.

From Equations Require Import Equations.

From ITree Require Import ITree Eq.Eqit Interp.InterpFacts Interp.TranslateFacts
  Events.StateFacts.
From simuliris.simulation Require Import slsls sim_properties reduction.
From Vellvm.Syntax Require Import LLVMAst DynamicTypes CFG.
From Vellvm.Semantics Require Import InterpretationStack.
From Vellvm.Theory Require Import DenotationTheory.
From simuliris.vir Require Import
  spec instr_laws bij_laws tactics fundamental_exp vir_util contextual_laws.
From simuliris.vir Require Import examples.notations.

From Vellvm Require Import Handlers.Handlers.
Import DenoteTactics.
Import CFG.

Local Open Scope Z_scope.

Import ListNotations.

(** *EXAMPLES *)

(** *1. load and readonly call
    readonly swap

    x <- !l;
    f #[readonly] (l);
    ret x
    ⪯
    f #{readonly} (l);
    x <- !l;
    ret x
 *)
Definition fn_name := string.

Definition load_readonly : fn_name := "load_readonly".

Definition load_readonly_source_code : code dtyp :=
  (IId (Raw 1), INSTR_Alloca (DTYPE_I 32) None None) ::
  (IVoid 2, INSTR_Store true
                  (DTYPE_I 32, EXP_Integer 42)
                  (DTYPE_Pointer, EXP_Ident (ID_Local (Raw 1)))
                   None) ::
  (IId (Raw 3), INSTR_Load true (DTYPE_I 32)
                (DTYPE_I 32, EXP_Ident (ID_Local (Raw 1))) None) ::
  (IId (Raw 4), INSTR_Call
                  (DTYPE_I 32, EXP_Integer 1)
                  ((DTYPE_Pointer, EXP_Ident (ID_Local (Raw 1))) :: nil)
                  [FNATTR_Readonly]) :: nil.

Definition load_readonly_target_code : code dtyp :=
  (IId (Raw 1), INSTR_Alloca (DTYPE_I 32) None None) ::
  (IVoid 2, INSTR_Store true
                  (DTYPE_I 32, EXP_Integer 42)
                  (DTYPE_Pointer, EXP_Ident (ID_Local (Raw 1)))
                   None) ::
  (IId (Raw 3), INSTR_Call
                  (DTYPE_I 32, EXP_Integer 1)
                  ((DTYPE_I 32, EXP_Ident (ID_Local (Raw 1))) :: nil)
                 [FNATTR_Readonly]) ::
  (IId (Raw 4), INSTR_Load true (DTYPE_I 32)
                (DTYPE_I 32, EXP_Ident (ID_Local (Raw 1))) None) ::
  nil.

(** *2. load and argmemonly call
    if p, l are separate locations

    x <- !l;
    f #[argmemonly] (p);
    ret x
    ⪯
    f #{argmemonly} (p);
    x <- !l;
    ret x
 *)
Definition load_argmemonly : fn_name := "load_argmemonly".

Definition load_argmemonly_source_code : code dtyp :=
  (IId (Raw 1), INSTR_Alloca (DTYPE_I 32) None None) ::
  (IVoid 2, INSTR_Store true
                  (DTYPE_I 32, EXP_Integer 42)
                  (DTYPE_Pointer, EXP_Ident (ID_Local (Raw 1)))
                   None) ::
  (IId (Raw 5), INSTR_Alloca (DTYPE_I 32) None None) ::
  (IVoid 2, INSTR_Store true
                  (DTYPE_I 32, EXP_Integer 2)
                  (DTYPE_Pointer, EXP_Ident (ID_Local (Raw 5)))
                   None) ::
  (IId (Raw 3), INSTR_Load true (DTYPE_I 32)
                (DTYPE_I 32, EXP_Ident (ID_Local (Raw 1))) None) ::
  (IId (Raw 4), INSTR_Call
                  (DTYPE_I 32, EXP_Integer 1)
                  ((DTYPE_Pointer, EXP_Ident (ID_Local (Raw 5))) :: nil)
                  [FNATTR_Argmemonly]) :: nil.

Definition load_argmemonly_target_code : code dtyp :=
  (IId (Raw 1), INSTR_Alloca (DTYPE_I 32) None None) ::
  (IVoid 2, INSTR_Store true
                  (DTYPE_I 32, EXP_Integer 42)
                  (DTYPE_Pointer, EXP_Ident (ID_Local (Raw 1)))
                   None) ::
  (IId (Raw 5), INSTR_Alloca (DTYPE_I 32) None None) ::
  (IVoid 2, INSTR_Store true
                  (DTYPE_I 32, EXP_Integer 2)
                  (DTYPE_Pointer, EXP_Ident (ID_Local (Raw 5)))
                   None) ::
  (IId (Raw 4), INSTR_Call
                  (DTYPE_I 32, EXP_Integer 1)
                  ((DTYPE_Pointer, EXP_Ident (ID_Local (Raw 5))) :: nil)
                  [FNATTR_Argmemonly]) ::
  (IId (Raw 3), INSTR_Load true (DTYPE_I 32)
                (DTYPE_I 32, EXP_Ident (ID_Local (Raw 5))) None) ::
  nil.

(** *3. store and argmemonly call
    if p, l are separate locations

    l := v;
    f #[argmemonly] (p);
    ret x
    ⪯
    f #{argmemonly} (p);
    l := v;
    ret x
 *)
Definition store_argmemonly : fn_name := "store_argmemonly".

Definition store_argmemonly_source_code : code dtyp :=
  (IId (Raw 1), INSTR_Alloca (DTYPE_I 32) None None) ::
  (IVoid 2, INSTR_Store true
                  (DTYPE_I 32, EXP_Integer 42)
                  (DTYPE_Pointer, EXP_Ident (ID_Local (Raw 1)))
                   None) ::
  (IId (Raw 5), INSTR_Alloca (DTYPE_I 32) None None) ::
  (IVoid 2, INSTR_Store true
                  (DTYPE_I 32, EXP_Integer 2)
                  (DTYPE_Pointer, EXP_Ident (ID_Local (Raw 5)))
                   None) ::
  (IId (Raw 4), INSTR_Call
                  (DTYPE_I 32, EXP_Integer 1)
                  ((DTYPE_Pointer, EXP_Ident (ID_Local (Raw 5))) :: nil)
                  [FNATTR_Argmemonly]) :: nil.

Definition store_argmemonly_target_code : code dtyp :=
  (IId (Raw 1), INSTR_Alloca (DTYPE_I 32) None None) ::
  (IId (Raw 5), INSTR_Alloca (DTYPE_I 32) None None) ::
  (IVoid 2, INSTR_Store true
                  (DTYPE_I 32, EXP_Integer 2)
                  (DTYPE_Pointer, EXP_Ident (ID_Local (Raw 5)))
                   None) ::
  (IId (Raw 4), INSTR_Call
                  (DTYPE_I 32, EXP_Integer 1)
                  ((DTYPE_Pointer, EXP_Ident (ID_Local (Raw 5))) :: nil)
                  [FNATTR_Argmemonly]) ::
  (IVoid 6, INSTR_Store true
                  (DTYPE_I 32, EXP_Integer 42)
                  (DTYPE_Pointer, EXP_Ident (ID_Local (Raw 1)))
                   None) ::
  nil.

Section examples.

  Context {Σ : gFunctors} `{!sheapGS Σ, !checkedoutGS Σ, !heapbijGS Σ}.
  Arguments denote_instr : simpl never.

  Example load_readonly_swap i_t i_s:
    ⊢ initial_frame_res [i_t] [i_s] ∅ -∗
    (<{{ (make_fn load_readonly load_readonly_source_code nil) (nil) }}> ) ⪯
    (<{{ (make_fn load_readonly load_readonly_target_code nil) (nil) }}> )
      [{ fun x y => initial_frame_res [i_t] [i_s] ∅ }].
  Proof with clean.
    iIntros "Hi"; iApply (code_to_fn_contextual with "Hi").
    iModIntro; iIntros (??) "(#HWF & Hbij)".
    rewrite /frame_resources_own -frame_resources_eq.
    iDestruct "Hbij" as "(Hbij & HC)".
    rewrite /load_readonly_source_code /load_readonly_target_code.
    to_instr.

    iApply sim_expr_bind; iApply (sim_expr_bupd_mono with "[HC]");
      [ | iApply (sim_instr_alloca1 with "Hbij")];
      [ | by intro | ..]...

    iDestruct "H" as (????) "(Hbij & Hl_t & Hl_s & H1_t & H1_s & Hb_t & Hb_s)"...

    iDestruct "Hbij" as "((Hs_t & Ha_t & Hd_t)&(Hs_s & Ha_s & Hd_s))"...

    source:
      iApply (source_instr_store1 with "Hl_s Hd_s Hs_s H1_s");
        first iApply source_red_denote_exp_i32;
        iModIntro; iIntros "Hd_s Hs_s H1_s Hl_s"; source_base...

    target:
      iApply (target_instr_store1 with "Hl_t Hd_t Hs_t H1_t");
        first iApply target_red_denote_exp_i32;
        iIntros "Hd_t Hs_t H1_t Hl_t"; target_base...

    target:
      iApply (target_instr_load with "Hl_t H1_t Hd_t Hs_t");
          [ constructor | constructor | cbn; set_solver | ].
    iIntros "H1 H3 Hl_t Hd_t Hs_t"; target_base.

    iApply sim_expr_bind.

    match goal with
    | [ |- context[INSTR_Call (?dt, ?f) ?l ?attrs] ] =>
        remember dt; remember f; remember l
    end.

   (* Process logic for [Call] *)
   iCombine "H1_s H1 Hl_t Hl_s Hb_t Hb_s" as "HP".
   iDestruct "HC" as "(HC & HA)".
   iPoseProof (sim_call_instr _ d (Raw 4) (Raw 3) e _ _ _ _
        with "HC HWF Hd_t Hd_s Hs_t Hs_s HP") as "Hinstr";
      [ set_solver | set_solver | set_solver | ].

    iApply (sim_expr_bupd_mono with "[Ha_t Ha_s H3] [Hinstr]");
      last iApply "Hinstr"; cycle 1.
    { subst; iApply exp_conv_to_instr; iApply expr_logrel_EXP_Integer. }

    { (* Denoting expression *)
      iIntros "(H1_t & H1 & Hl_t & Hl_s & Hb_t & Hb_s) Hd_t Hd_s Hs_t Hs_s".

      to_block.

      iApply (sim_insert_loc_bij with "Hl_t Hl_s Hb_t Hb_s").
      { iApply mem_byte_rel_write_stable;
          first iApply mem_byte_rel_make_empty_mem_block;
        iApply dval_rel_I32. }

      subst; iIntros "#Hloc"; rewrite loc_uval_rel !instr_conv_bind.

      iApply sim_expr_bind; iApply exp_conv_to_instr.
      iApply (sim_expr_bupd_mono with "[Hd_t Hd_s]");
        last iApply (sim_local_read_exp_conv with "Hs_t Hs_s H1 H1_t"); cont.

      iDestruct "H" as (??) "(Hs_t & Hs_s & Hl_t & Hl_s)".
      rewrite /instr_conv. setoid_rewrite bind_ret_l; setoid_rewrite interp_ret.
      iApply sim_expr_base; iExists _, _; do 2 (iSplitL ""; first done).
      iFrame; iSplitL ""; first (subst; cbn; by iSplitL).
      iCombine "Hloc Hl_t Hl_s" as "HL"; iModIntro; iExact "HL". }

    cont; iDestruct "H" as
      (??) "((#Hloc & H1_t & H1_s) &
          Hs_t & Hs_s & Hd_t & Hd_s & H3_t & H4_s & #Hv & HC)".
    rewrite -loc_uval_rel.
    cbn -[serialize_dvalue denote_instr].
    iApply (source_instr_bij_load with "Hloc HC H1_s Hd_s Hs_s"); first set_solver.
    iModIntro; iIntros (?) "H1 H4 HC Hd Hs".

    iApply sim_expr_base; frame_res_exists.
    iExists [l_t0], [l_s0]; iFrame "Hloc";
    repeat (iSplitL ""; try eauto using NoDup_singleton);
      cbn; iPureIntro; set_solver.
  Qed.

  Example load_argmemonly_swap i_t i_s:
    ⊢ initial_frame_res [i_t] [i_s] ∅ -∗
    (<{{ (make_fn load_argmemonly load_argmemonly_source_code nil) (nil) }}> ) ⪯
    (<{{ (make_fn load_argmemonly load_argmemonly_target_code nil) (nil) }}> )
      [{ fun x y => initial_frame_res [i_t] [i_s] ∅ }].
  Proof with clean.
    iIntros "Hi"; iApply (code_to_fn_contextual with "Hi").
    iModIntro; iIntros (??) "(#HWF & Hbij)".
    rewrite /frame_resources_own -frame_resources_eq.
    iDestruct "Hbij" as "(Hbij & HC)".
    rewrite /load_readonly_source_code /load_readonly_target_code.
    to_instr.

    iApply sim_expr_bind; iApply (sim_expr_bupd_mono with "[HC]");
      [ | iApply (sim_instr_alloca1 with "Hbij")];
      [ | by intro | ..]...

    iDestruct "H" as (????)
      "(Hbij & Hl_t & Hl_s & H1_t & H1_s & Hb_t & Hb_s)"...

    iDestruct "Hbij" as "((Hs_t & Ha_t & Hd_t)&(Hs_s & Ha_s & Hd_s))"...

    source:
      iApply (source_instr_store1 with "Hl_s Hd_s Hs_s H1_s");
        first iApply source_red_denote_exp_i32...
    iModIntro; iIntros "Hd_s Hs_s H1_s Hl_s"; source_base.
    target:
      iApply (target_instr_store1 with "Hl_t Hd_t Hs_t H1_t");
        first iApply target_red_denote_exp_i32.
    iIntros "Hd_t Hs_t H1_t Hl_t"; target_base...

    iApply sim_expr_bind;
      iApply (sim_expr_bupd_mono with
          "[HC H1_t Hl_t H1_s Hl_s Hb_t Hb_s]");
      [ | iApply (sim_instr_alloca with "Ha_t Ha_s Hd_t Hd_s Hs_t Hs_s")];
      [ | by intro | ..]...

    iDestruct "H" as (????)
      "(Hp_t & Hp_s & Ha_t & Ha_s & Hd_t & Hd_s
        & H5_t & H5_s & Hs_t & Hs_s & Hb_t1 & Hb_s1)".

    source:
      iApply (source_instr_store1 with "Hp_s Hd_s Hs_s H5_s");
        first iApply source_red_denote_exp_i32.
    iModIntro.
    iIntros "Hd_s Hs_s H5_s Hp_s"; source_base.
    target:
      iApply (target_instr_store1 with "Hp_t Hd_t Hs_t H5_t");
        first iApply target_red_denote_exp_i32.
    iIntros "Hd_t Hs_t H5_t Hp_t"; target_base...

    target:
      iApply (target_instr_load with "Hl_t H1_t Hd_t Hs_t");
          [ constructor | constructor | cbn; set_solver | ].

    iIntros "H1 H3 Hl_t Hd_t Hs_t"; target_base.
    iApply sim_expr_bind.

    match goal with
    | [ |- context[INSTR_Call (?dt, ?f) ?l ?attrs] ] =>
        remember dt; remember f; remember l
    end.

    (* Put [l_t1], [l_s1] into bijection *)
    to_block.
    iApply (sim_insert_loc_bij with "Hp_t Hp_s Hb_t1 Hb_s1").
    { iApply mem_byte_rel_write_stable;
        first iApply mem_byte_rel_make_empty_mem_block;
      iApply dval_rel_I32. }
    iIntros "#Hbij".

    clean.

   (* Process logic for [Call] *)
   iDestruct "HC" as "(HC & HA)".
   iCombine "H1_s H1 H3 H5_t H5_s Ha_t Ha_s HA Hb_t Hb_s" as "HP".

   iPoseProof (sim_call_argmemonly_instr _ _ (Raw 4) (Raw 4)
        with "Hl_t Hl_s HWF Hd_t Hd_s Hs_t Hs_s HC HP") as "H"...

    iApply (sim_expr_bupd_mono with "[] [H]");
      last iApply "H"; cycle 1.
    { subst; iApply exp_conv_to_instr; iApply expr_logrel_EXP_Integer. }

    { (* Denoting expression *)
      iIntros "(H1_s & H1_t & H3_t & H5_t & H5_s & Ha_t & Ha_s & HC)
          Hd_t Hd_s Hs_t Hs_s".

      subst; clean.
      rewrite instr_conv_bind.
      iApply sim_expr_bind; iApply exp_conv_to_instr.
      iApply (sim_expr_bupd_mono with
               "[H1_s H1_t H3_t HC Ha_t Ha_s Hd_t Hd_s]");
        last iApply (sim_local_read_exp_conv with "Hs_t Hs_s H5_t H5_s");
        cont.
      rewrite !instr_conv_ret.
      iApply sim_expr_base. iModIntro. repeat iExists _; base; cbn.
      iDestruct "H" as (??) "(Hst & Hss & H5_t & H5_s)".
      subst; iFrame.
      iSplitL ""; first (iSplit; last done); first by iApply loc_uval_rel.
      iSplitL ""; first done.
      iCombine "H1_s H1_t H3_t HC H5_t H5_s Ha_t Ha_s" as "HP"; iApply "HP". }

    cont.

    iDestruct "H" as (??) "((H1_s&H1_t&H3_t&CI&H5_t&H5_s&Ha_t&Ha_s) &
          Hs_t & Hs_s & Hl_t & Hl_s & Hd_t & Hd_s & H4_t & H4_s & Hv & HC)".

    (* Final source load *)
    iApply (source_instr_bij_load with "Hbij HC H5_s Hd_s Hs_s")...
    iModIntro; iIntros (?) "H5_s H3_s HC Hd Hs".

    iDestruct "CI" as "(CI & Hb_t & Hb_s)".

    (* Put [l_t0], [l_s0] into bijection *)
    to_block.
    iApply (sim_insert_loc_bij with "Hl_t Hl_s Hb_t Hb_s").
    { iApply mem_byte_rel_write_stable;
        first iApply mem_byte_rel_make_empty_mem_block;
      iApply dval_rel_I32. }
    iIntros "#Hbij0".

    iApply sim_expr_base; frame_res_exists...
    iExists [l_t1; l_t0], [l_s1; l_s0]; iFrame "Hbij";
    repeat (iSplitL ""; try eauto using NoDup_singleton);
      cbn; iPureIntro; try set_solver.
    all: repeat constructor; try solve [set_solver | eauto].
  Qed.

  Example store_argmemonly_swap i_t i_s:
    ⊢ initial_frame_res [i_t] [i_s] ∅ -∗
    (<{{ (make_fn store_argmemonly store_argmemonly_source_code nil) (nil) }}> ) ⪯
    (<{{ (make_fn store_argmemonly store_argmemonly_target_code nil) (nil) }}> )
      [{ fun x y => initial_frame_res [i_t] [i_s] ∅ }].
  Proof with clean.
    iIntros "Hi"; iApply (code_to_fn_contextual with "Hi").
    iModIntro; iIntros (??) "(#HWF & Hbij)".
    rewrite /frame_resources_own -frame_resources_eq.
    iDestruct "Hbij" as "(Hbij & HC)".
    rewrite /load_readonly_source_code /load_readonly_target_code.
    to_instr.

    iApply sim_expr_bind; iApply (sim_expr_bupd_mono with "[HC]");
      [ | iApply (sim_instr_alloca1 with "Hbij")];
      [ | by intro | ..]...

    iDestruct "H" as (????)
      "(Hbij & Hl_t & Hl_s & H1_t & H1_s & Hb_t & Hb_s)"...

    iDestruct "Hbij" as "((Hs_t & Ha_t & Hd_t)&(Hs_s & Ha_s & Hd_s))"...

    target:
      iApply (target_instr_store1 with "Hl_t Hd_t Hs_t H1_t");
        first iApply target_red_denote_exp_i32.
    iModIntro; iIntros "Hd_t Hs_t H1_t Hl_t"; target_base...

    iApply sim_expr_bind;
      iApply (sim_expr_bupd_mono with
          "[HC H1_t Hl_t H1_s Hl_s Hb_t Hb_s]");
      [ | iApply (sim_instr_alloca with "Ha_t Ha_s Hd_t Hd_s Hs_t Hs_s")];
      [ | by intro | ..]...

    iDestruct "H" as (????)
      "(Hp_t & Hp_s & Ha_t & Ha_s & Hd_t & Hd_s
        & H5_t & H5_s & Hs_t & Hs_s & Hb_t1 & Hb_s1)".

    source:
      iApply (source_instr_store1 with "Hp_s Hd_s Hs_s H5_s");
        first iApply source_red_denote_exp_i32.
    iModIntro.
    iIntros "Hd_s Hs_s H5_s Hp_s"; source_base.
    target:
      iApply (target_instr_store1 with "Hp_t Hd_t Hs_t H5_t");
        first iApply target_red_denote_exp_i32.
    iIntros "Hd_t Hs_t H5_t Hp_t"; target_base...

    iApply sim_expr_bind.

    match goal with
    | [ |- context[INSTR_Call (?dt, ?f) ?l ?attrs] ] =>
        remember dt; remember f; remember l
    end.

    (* Put [l_t1], [l_s1] into bijection *)
    to_block.
    iApply (sim_insert_loc_bij with "Hp_t Hp_s Hb_t1 Hb_s1").
    { iApply mem_byte_rel_write_stable;
        first iApply mem_byte_rel_make_empty_mem_block;
      iApply dval_rel_I32. }
    iIntros "#Hbij"...

    to_block.
    (* Process logic for [Call] *)
    iDestruct "HC" as "(HC & HA)".
    iCombine "H1_t H1_s H5_t H5_s Ha_t Ha_s HA Hb_t Hb_s" as "HP".

    iPoseProof (sim_call_argmemonly_instr1 _ _ (Raw 4) (Raw 4) with
                  "Hl_t Hl_s HWF Hd_t Hd_s Hs_t Hs_s HC HP") as "H"...

    iApply (sim_expr_bupd_mono with "[] [H]");
      last iApply "H"; cycle 1.
    { subst; iApply exp_conv_to_instr; iApply expr_logrel_EXP_Integer. }

    { (* Denoting expression *)
      iIntros "(H1_s & H1_t & H5_t & H5_s & Ha_t & Ha_s & HC)
          Hd_t Hd_s Hs_t Hs_s".

      subst; clean.
      rewrite instr_conv_bind.
      iApply sim_expr_bind; iApply exp_conv_to_instr.
      iApply (sim_expr_bupd_mono with
               "[H1_s H1_t HC Ha_t Ha_s Hd_t Hd_s]");
        last iApply (sim_local_read_exp_conv with "Hs_t Hs_s H5_t H5_s");
        cont.
      rewrite !instr_conv_ret.
      iApply sim_expr_base. iModIntro. repeat iExists _; base; cbn.
      iDestruct "H" as (??) "(Hst & Hss & H5_t & H5_s)".
      subst; iFrame.
      iSplitL ""; first (iSplit; last done); first by iApply loc_uval_rel.
      iSplitL ""; first done.
      iCombine "H1_s H1_t HC H5_t H5_s Ha_t Ha_s" as "HP"; iApply "HP". }

    cont.

    iDestruct "H" as (??) "((H1_s&H1_t&CI&H5_t&H5_s&Ha_t&Ha_s) &
          Hs_t & Hs_s & Hl_t & Hl_s & Hd_t & Hd_s & H4_t & H4_s & Hv & HC)".

    subst.
    source: iApply (source_instr_store1 with "Hl_s Hd_s Hs_s H1_t");
       first iApply source_red_denote_exp_i32.

    iModIntro; iIntros "Hd_s Hs_s H1_t Hl_s"; source_base...

    iDestruct "CI" as "(CI & Hb_t & Hb_s)".

    (* Put [l_t0], [l_s0] into bijection *)
    to_block.
    iApply (sim_insert_loc_bij with "Hl_t Hl_s Hb_t Hb_s").
    { iApply mem_byte_rel_write_stable;
        first iApply mem_byte_rel_make_empty_mem_block;
      iApply dval_rel_I32. }
    iIntros "#Hbij0".

    iApply sim_expr_base; frame_res_exists...
    iExists [l_t1; l_t0], [l_s1; l_s0]; iFrame "Hbij";
    repeat (iSplitL ""; try eauto using NoDup_singleton);
      cbn; iPureIntro; try set_solver.
    all: repeat constructor; try solve [set_solver | eauto].
  Qed.

End examples.

(* Existence proofs for function specifications *)
Section attr_fns.

  Context {Σ : gFunctors} `{!sheapGS Σ, !checkedoutGS Σ, !heapbijGS Σ}.

  Definition nil_fn_ex_name : fn_name := "nil_fn_ex".

  Definition nil_fn_ex : code dtyp := nil.

  Definition nil_fn_ex_fn :=
    make_fn nil_fn_ex_name nil_fn_ex nil.

  (* The empty function satisfies all attributes *)
  Lemma nil_fn_ex_sat dv C i_t i_s attr:
    attribute_interp
      (ExternalCall DTYPE_Void dv nil attr)
      (ExternalCall DTYPE_Void dv nil attr) C ->
    initial_frame_res [i_t] [i_s] C -∗
    (<{{ (make_fn nil_fn_ex_name nil_fn_ex nil) (nil) }}> ) ⪯
    (<{{ (make_fn nil_fn_ex_name nil_fn_ex nil) (nil) }}> )
    [{ fun x y =>
        initial_frame_res [i_t] [i_s] C }].
  Proof with clean.
    iIntros (?); simp attribute_interp in H.
    destruct H as (?&?).
    destruct x eqn: Hx;
    iIntros "Hi"; clear H;
    iApply (code_to_fn_contextual with "Hi");
    iModIntro; iIntros (??) "(#HWF & Hbij)";
    cbn; rewrite bind_ret_l;
    rewrite instr_conv_ret;
    iApply sim_expr_base;
      iExists _, _; do 2 (iSplitL ""; first done); iFrame "HWF";
    iDestruct "Hbij" as "(Hbij & HC)";
    iExists empty_frame, empty_frame; iFrame.
  Qed.

  (* Readonly *)
  Definition readonly_ex_name : fn_name := "readonly_ex".

  Definition readonly_ex : code dtyp :=
    (IId (Raw 1), INSTR_Alloca (DTYPE_I 32) None None) ::
    (IId (Raw 3), INSTR_Load true (DTYPE_I 32)
                  (DTYPE_I 32, EXP_Ident (ID_Local (Raw 1))) None) :: nil.

  Definition readonly_ex_fn :=
    make_fn readonly_ex_name readonly_ex nil.

  Lemma readonly_ex_sat dv C i_t i_s:
    attribute_interp
      (ExternalCall DTYPE_Void dv nil [FNATTR_Readonly])
      (ExternalCall DTYPE_Void dv nil [FNATTR_Readonly]) C ->
    initial_frame_res [i_t] [i_s] C -∗
    (<{{ (make_fn readonly_ex_name readonly_ex nil) (nil) }}> ) ⪯
    (<{{ (make_fn readonly_ex_name readonly_ex nil) (nil) }}> )
    [{ fun x y =>
        initial_frame_res [i_t] [i_s] C }].
  Proof with clean.
    iIntros (?); simp attribute_interp in H.
    destruct H as (?&?).
    destruct x eqn: Hx; cycle 4; destruct H as (?&?);
      compute in H; try done; cycle 1.
    { destruct H0 as (?&?&?); by compute in H0. }

    destruct H0.
    iIntros "Hi"; iApply (code_to_fn_contextual with "Hi").
    iModIntro; iIntros (??) "(#HWF & Hbij)".

    rewrite /frame_resources_own -frame_resources_eq.
    iDestruct "Hbij" as "(Hbij & HC)".
    rewrite /load_readonly_source_code /load_readonly_target_code.
    to_instr.
    iDestruct "HC" as "(HC & HA)".
    iDestruct "Hbij" as "((Hs_t & Ha_t & Hd_t)&(Hs_s & Ha_s & Hd_s))"...

    iApply sim_expr_bind; iApply (sim_expr_bupd_mono with "[HA]");
      [ | iApply (sim_instr_alloca_checkout with
              "Ha_t Ha_s Hd_t Hd_s Hs_t Hs_s HC")];
      [ | by intro | ..]...

    iDestruct "H" as (????)
        "(Hl_t & Hl_s & Ha_t & Ha_s & Hd_t & Hd_s &
            H1_t & H1_s & Hs_t & Hs_s & Hb_t & Hb_s & HC & %Hcn)"...

    target:
      iApply (target_instr_load1 with "Hl_t H1_t Hd_t Hs_t");
          [ constructor | cbn; set_solver | ].
    iModIntro. iIntros "H1 H3 Hl_t Hd_t Hs_t"; target_base.

    source:
      iApply (source_instr_load1 with "Hl_s H1_s Hd_s Hs_s");
          [ constructor | cbn; set_solver | ].
    iIntros "H1_s H3_s Hl_s Hd_s Hs_s"; source_base.

    iApply (sim_insert_loc_bij with "Hl_t Hl_s Hb_t Hb_s").
    { iApply lb_rel_empty_blocks. }
    iIntros "#Hbij".

    iApply sim_expr_base; frame_res_exists...
    iDestruct "HA" as (??????) "HA". iFrame.
    iExists [l_t0], [l_s0].
    repeat (iSplitL ""; try eauto using NoDup_singleton); cbn; eauto;
      try (iPureIntro; set_solver).
  Qed.

  (* Argmemonly, readonly *)
  Definition argmemonly_readonly_ex_name : fn_name := "argmemonly_readonly_ex".

  Definition argmemonly_readonly_ex : code dtyp :=
    (IId (Raw 3), INSTR_Load true (DTYPE_I 32)
                  (DTYPE_I 32, EXP_Ident (ID_Local (Raw 1))) None) :: nil.

  Definition argmemonly_readonly_ex_fn :=
    make_fn argmemonly_readonly_ex_name argmemonly_readonly_ex nil.

  Lemma argmemonly_readonly_ex_sat dv C i_t i_s l_t l_s:
    attribute_interp
      (ExternalCall DTYPE_Void dv [UVALUE_Addr l_t] [FNATTR_Argmemonly; FNATTR_Readonly])
      (ExternalCall DTYPE_Void dv [UVALUE_Addr l_s] [FNATTR_Argmemonly; FNATTR_Readonly]) C ->
    l_t ↔h l_s -∗
    initial_frame_res [i_t] [i_s] C -∗
    (<{{ (make_fn argmemonly_readonly_ex_name argmemonly_readonly_ex [Raw 1])
           ([UVALUE_Addr l_t]) }}> ) ⪯
    (<{{ (make_fn argmemonly_readonly_ex_name argmemonly_readonly_ex [Raw 1])
           ([UVALUE_Addr l_s]) }}> )
    [{ fun x y =>
        initial_frame_res [i_t] [i_s] C }].
  Proof with clean.
    iIntros (?); simp attribute_interp in H.
    destruct H as (?&?).
    destruct x eqn: Hx; cycle 4; destruct H as (?&?);
      compute in H; try done;
      try (destruct H0 as (?&?); by compute in H0).
    clear H.

    iIntros "#Hl Hi".
    iApply (code_to_fn_contextual_args with "Hi"); try done.
    { apply NoDup_singleton. }

    iModIntro; iIntros (??) "(#HWF & Hbij)".

    rewrite /frame_resources_own -frame_resources_eq.
    rewrite /local_args_own_target /local_args_own_source.
    iDestruct "Hbij" as "((Hbij & HC) & Hlv_t & Hlv_s)".
    to_instr.
    iDestruct "HC" as "(HC & HA)".
    iDestruct "Hbij" as "((Hs_t & Ha_t & Hd_t)&(Hs_s & Ha_s & Hd_s))"...
    iDestruct "Hlv_t" as "(Hlv_t & _)"; iDestruct "Hlv_s" as "(Hlv_s & _)".

    specialize (H0 l_t l_s 0%nat eq_refl).
    destruct H0 as (?&?&?).
    iApply sim_expr_bind.
    iApply (sim_expr_bupd_mono with "[Ha_t Ha_s HA]");
      last (iApply (sim_instr_load_bij_Some with
                "Hl HC Hd_t Hd_s Hs_t Hs_s Hlv_t Hlv_s");
        first eauto; try set_solver).
    2: try done. 2: try constructor.

    cont.
    iDestruct "H" as "(HC & Hd_t & Hd_s & Hs_t & Hs_s& H1_t & H1_s & H)".

    iApply sim_expr_base; iFrame.
    iExists tt, tt; do 2 (iSplitL ""; first done).
    iFrame "HWF".
    iExists (instr_laws.Frame ∅ {[Raw 3; Raw 1]}),
      (instr_laws.Frame ∅ {[Raw 3; Raw 1]}); by iFrame.
  Qed.

  (* Argmemonly *)
  Definition argmemonly_ex_name : fn_name := "argmemonly_ex".

  Definition argmemonly_ex : code dtyp :=
    (IVoid 2, INSTR_Store true
                    (DTYPE_I 32, EXP_Integer 2)
                    (DTYPE_Pointer, EXP_Ident (ID_Local (Raw 1)))
                    None) :: nil.

  Definition argmemonly_ex_fn :=
    make_fn argmemonly_ex_name argmemonly_ex nil.

  Lemma argmemonly_ex_sat dv C i_t i_s l_t l_s:
    attribute_interp
      (ExternalCall DTYPE_Void dv [UVALUE_Addr l_t] [FNATTR_Argmemonly])
      (ExternalCall DTYPE_Void dv [UVALUE_Addr l_s] [FNATTR_Argmemonly]) C ->
    l_t ↔h l_s -∗
    initial_frame_res [i_t] [i_s] C -∗
    (<{{ (make_fn argmemonly_ex_name argmemonly_ex [Raw 1])
           ([UVALUE_Addr l_t]) }}> ) ⪯
    (<{{ (make_fn argmemonly_ex_name argmemonly_ex [Raw 1])
           ([UVALUE_Addr l_s]) }}> )
    [{ fun x y =>
        initial_frame_res [i_t] [i_s] C }].
  Proof with clean.
    iIntros (?); simp attribute_interp in H.
    destruct H as (?&?).
    destruct x eqn: Hx; cycle 4; destruct H as (?&?);
      compute in H; try done;
      try (destruct H0 as (?&?); by compute in H0).
    clear H.

    iIntros "#Hl Hi".
    iApply (code_to_fn_contextual_args with "Hi"); try done.
    { apply NoDup_singleton. }

    iModIntro; iIntros (??) "(#HWF & Hbij)".

    rewrite /frame_resources_own -frame_resources_eq.
    rewrite /local_args_own_target /local_args_own_source.
    iDestruct "Hbij" as "((Hbij & HC) & Hlv_t & Hlv_s)".
    to_instr.
    iDestruct "HC" as "(HC & HA)".
    iDestruct "Hbij" as "((Hs_t & Ha_t & Hd_t)&(Hs_s & Ha_s & Hd_s))"...
    iDestruct "Hlv_t" as "(Hlv_t & _)"; iDestruct "Hlv_s" as "(Hlv_s & _)".
    destruct H0 as (?&?).

    specialize (H0 l_t l_s 0%nat eq_refl).
    iApply sim_expr_bind.
    iAssert (dval_rel
      (DVALUE_I32 (DynamicValues.Int32.repr 2))
      (DVALUE_I32 (DynamicValues.Int32.repr 2)))%I as "Hdv".
    { iApply dval_rel_I32. }
    iApply (sim_expr_bupd_mono with "[Ha_t Ha_s HA]");
      last (iApply (sim_instr_store_bij1 with
                "Hl HC Hd_t Hd_s Hs_t Hs_s Hdv Hlv_t Hlv_s");
        first eauto; try set_solver).
    2: try done. 2: try constructor.
    2: iApply target_red_denote_exp_i32.
    2: iApply source_red_denote_exp_i32.

    cont.
    iDestruct "H" as "(HC & Hd_t & Hd_s & Hs_t & Hs_s& H1_t & H1_s)".

    iApply sim_expr_base; iFrame.
    iExists tt, tt; do 2 (iSplitL ""; first done).
    iFrame "HWF".
    iExists (instr_laws.Frame ∅ {[Raw 1]}),
      (instr_laws.Frame ∅ {[Raw 1]}); by iFrame.
  Qed.

End attr_fns.
