From iris.prelude Require Import options.

From velliris.program_logic Require Import program_logic.
From velliris.vir Require Import
  vir val_rel heapbij adequacy spec globalbij logical_relations fundamental.

From Vellvm Require Import Syntax.DynamicTypes Handlers Syntax.LLVMAst
  Semantics.InterpretationStack.

From ITree Require Import Recursion.

Import LLVMEvents.

Set Default Proof Using "Type*".

Section mcfg_contextual.

  Context `(sheapGS Σ, checkedoutGS Σ, heapbijGS Σ).

  (* The contextual refinement on [denote_mcfg]. *)
  Lemma contextual_denote_mcfg :
    ∀ γ_t γ_s dv dv' e_t e_s main C,
    □ fun_logrel e_t e_s ∅ -∗
      checkout ∅ -∗
      stack_tgt [γ_t] -∗
      stack_src [γ_s] -∗
      denote_mcfg ((dv, e_t) :: C) DTYPE_Void (DVALUE_Addr main) []
      ⪯
      denote_mcfg ((dv', e_s) :: C) DTYPE_Void (DVALUE_Addr main) []
      [[ (λ x y : uvalue, ⌜obs_val x y⌝) ⤉ ]].
  Proof.
    iIntros (????????) "#Hfun Hc Hs_t Hs_s".
    rewrite /denote_mcfg.

  Admitted.

End mcfg_contextual.
