From iris.proofmode Require Export proofmode.
From iris.prelude Require Import options.

From velliris.utils Require Import tactics.
From ITree Require Import Eq.

(* Vellvm-related tactics *)
From Vellvm Require Import Semantics.LLVMEvents.

Ltac noncall_solve :=
  destruct_match_goal;
  try match goal with
    | |- context[raise] =>
      right; left; repeat eexists _ ; by tau_steps
    | |- context[raiseUB] =>
      right; right; left; repeat eexists _ ; by tau_steps
    end;
    try (left; repeat eexists _ ; by tau_steps).

(* Simuliris-related tactics *)
From velliris.program_logic Require Import program_logic.

Ltac step :=
  setoid_rewrite InterpFacts.interp_bind; iApply sim_expr_bind.

Ltac destruct_state σ :=
  destruct σ as ((?&?&?)&?&?).

Tactic Notation "source:" tactic(H) :=
  iApply source_red_sim_expr;
  iApply source_red_bind; H.

Ltac source_base :=
  do 2 iApply source_red_base;
  rewrite bind_ret_l.

Tactic Notation "target:" tactic(H) :=
  iApply target_red_sim_expr;
  iApply target_red_bind; H.

Ltac target_base :=
  do 2 iApply target_red_base;
  rewrite bind_ret_l.

Ltac cont :=
  let Hret1 := fresh "Hret1" in
  let Hret2 := fresh "Hret2" in
  iIntros (??) "H";
  iDestruct "H" as (?? Hret1 Hret2) "H";
    rewrite Hret1 Hret2 !bind_ret_l; clear Hret1 Hret2.

Ltac to_inner G :=
  change
    (|==>
      ∃ c : sim_case,
        match c with
        | BASE => ?Φ ?x ?y
        | STUTTER_L => stutter_l
        | STUTTER_R => stutter_r
        | TAU_STEP => tau_step
        | VIS_STEP => vis_step ?x ?y
        | SOURCE_UB => source_ub
        | SOURCE_EXC => source_exc
        end)%I with
        (sim_expr_inner G (sim_indF G) Φ x y).
