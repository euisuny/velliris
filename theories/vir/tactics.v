From iris.proofmode Require Export proofmode.
From iris.prelude Require Import options.

From simuliris.utils Require Import tactics.
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
From simuliris.simulation Require Import sim_properties reduction.

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
