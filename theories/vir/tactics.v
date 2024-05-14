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


(* Some useful tactics for reducing [sim_expr] for [vir] *)
From velliris.vir Require Import vir vir_sim_properties.

Ltac itree_vsimp e :=
  lazymatch e with
  (* Conversion lemmas *)
  | exp_conv (Ret _) => rewrite exp_conv_ret
  | exp_conv (bind _ _) => rewrite exp_conv_bind
  | exp_conv (ITree.bind _ _) => rewrite exp_conv_bind
  | instr_conv (trigger (Call _ _ _ _)) =>
      rewrite instr_conv_call
  | instr_conv (trigger _) =>
      rewrite instr_conv_noncall +
      rewrite instr_conv_noncall'
  | instr_conv (Ret ?x) => rewrite (instr_conv_ret x)
  | instr_conv (Ret _) => rewrite instr_conv_ret
  | instr_conv (bind _ _) => rewrite instr_conv_bind
  | instr_conv (ITree.bind _ _) => rewrite instr_conv_bind
  | L0'expr_conv (Ret _) => rewrite L0'expr_conv_ret
  | L0'expr_conv (bind _ _) => rewrite L0'expr_conv_bind
  | L0'expr_conv (ITree.bind _ _) => rewrite L0'expr_conv_bind

  (* Specific to level translations *)
  | interp (λ T e, Vis (instrE_conv T (exp_to_instr e)) (λ x : T , Ret x)) _ =>
      rewrite (eq_itree_interp _ _ eq2_exp_to_L0); last done
 end.

Ltac sim_expr_vsimp e :=
  match e with
  (* Event translation adjustment *)
  | sim_expr _ (L0'expr_conv (translate instr_to_L0' _))
              (L0'expr_conv (translate instr_to_L0' _)) =>
      iApply instr_to_L0'
  | sim_expr _ (instr_conv (translate exp_to_instr _))
              (instr_conv (translate exp_to_instr _)) =>
      iApply exp_conv_to_instr
  (* Vis to [trigger] *)
  | sim_expr _ (Vis _ _) (Vis _ _ ) =>
      iApply sim_expr_vis
  | sim_expr _ (vis _ _) (vis _ _ ) =>
      iApply sim_expr_vis
  (* Some symbolic execution under ITree rewrites *)
  | sim_expr _ ?l ?r =>
    (* Try doing ITree rewriting on both sides if possible *)
    (itree_vsimp l + itree_simp l) +
    (itree_vsimp r + itree_simp r)

  (* Some symbolic execution under ITree rewrites on [sim_expr']*)
  | sim_expr' _ ?l ?r =>
    (* Try doing ITree rewriting on both sides if possible *)
    (itree_vsimp l + itree_simp l) +
    (itree_vsimp r + itree_simp r)
  end.

Ltac vsimp := repeat
  lazymatch goal with
  | |- environments.envs_entails _ (bupd ?e) =>
      iModIntro
  | |- environments.envs_entails _ ?e =>
      sim_expr_vsimp e
  end.

Ltac final :=
  vsimp;
  repeat Tau;
  match goal with
  (* Base case *)
  | |- environments.envs_entails _
      (sim_expr _ (Ret _) (Ret _)) =>
      iApply sim_expr_base
  | |- environments.envs_entails _
      (sim_expr' _ (Ret _) (Ret _)) =>
      iApply sim_expr_base
  end.

Tactic Notation "mono:" tactic(tac) :=
  iApply sim_expr_bupd_mono; [ | tac; eauto ];
  try (iIntros (??) "HΦ"; iDestruct "HΦ" as (??->->) "HΦ").

Tactic Notation "mono:" tactic(tac) "with" constr(hyps) :=
  iApply (sim_expr_bupd_mono with hyps); [ | tac; eauto ];
  try (iIntros (??) "HΦ"; iDestruct "HΦ" as (??->->) "HΦ").

Ltac sfinal :=
  repeat iExists _;
  repeat (iSplitL ""; first (iPureIntro; done));
  iFrame; try done.

Ltac vfinal := final; sfinal.
