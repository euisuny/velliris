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

From Vellvm Require Import Handlers.Handlers.
Import DenoteTactics.
Import CFG.

Local Open Scope Z_scope.

Import ListNotations.

Require Import iris.proofmode.environments.

Declare Scope sim_scope.
Open Scope sim_scope.
Delimit Scope sim_scope with sim.

Notation "" := Enil (only printing) : sim_scope.
Notation "Γ H : P " := (Esnoc Γ (INamed H) P%I)
  (at level 1, P at level 200,
   left associativity, format "Γ H  :  '[' P ']' '//'", only printing) : sim_scope.

(* Simulation-specific notation *)
(* Source notation *)
Notation "Γ . H : l ↦{ q }s v" := (Esnoc Γ (INamed H) (l ↦{ q }s v)%I)
  (at level 1,
   left associativity,
format "Γ                                  .   H  :  '[' l  ↦{ q }s  v ']' '//'", only printing)
    : sim_scope.
Notation "Γ . H : l ↦s v" := (Esnoc Γ (INamed H) (l ↦s v)%I)
  (at level 1,
   left associativity,
format "Γ                                  . '['  H  :  l  ↦s  v ']' '//'", only printing)
    : sim_scope.
Notation "Γ . H : l ↦{ q }s [ v ]" := (Esnoc Γ (INamed H) (l ↦s [ v ])%I)
  (at level 1,
   left associativity,
format "Γ                                  . '['  H  :  l  ↦{ q }s [ v ] ']' '//'", only printing)
    : sim_scope.
Notation "Γ . H : l ↦s [ v ]" := (Esnoc Γ (INamed H) (l ↦s [ v ])%I)
  (at level 1,
   left associativity,
format "Γ                                  .  '['  H  :  l  ↦s [ v ] ']' '//'", only printing)
    : sim_scope.
Notation "Γ . H : [ l := v ]s i" := (Esnoc Γ (INamed H) ([ l := v ]s i)%I)
  (at level 1,
   left associativity,
format "Γ                                  .  '['  H  :  [  l  :=  v  ]s  i ']' '//'", only printing)
    : sim_scope.
Notation "Γ . H : 'ldomain' Q" := (Esnoc Γ (INamed H) (ldomain_src Q)%I)
  (at level 1,
   left associativity,
format "Γ                                  . '['   H  :  'ldomain'  Q  ']' '//'", only printing)
    : sim_scope.
Notation "Γ . H : 'block' l n" := (Esnoc Γ (INamed H) (source_block_size l n)%I)
  (at level 1, left associativity,
format "Γ                                  .  '['  H  :  'block'  l  n  ']' '//'", only printing)
    : sim_scope.
Notation "Γ . H : 'stack' P " := (Esnoc Γ (INamed H) (stack_src P)%I)
  (at level 1, P at level 200,
   left associativity,
format "Γ                                  .  '['  H  :  'stack'  P ']' '//'", only printing)
    : sim_scope.
Notation "Γ . H : 'alloca' Q" := (Esnoc Γ (INamed H) (alloca_src _ Q)%I)
  (at level 1,
   left associativity,
    format "Γ                                  .  '['  H  :  'alloca'  Q  ']' '//'", only printing)
    : sim_scope.

(* Target notation *)
Notation "Γ H : l ↦{ q }t v ." := (Esnoc Γ (INamed H) (l ↦{ q }t v)%I)
  (at level 1,
   left associativity,
format "Γ H  :  '[' l  ↦{ q }t  v            . ']' '//'", only printing)
    : sim_scope.
Notation "Γ H : l ↦t v " := (Esnoc Γ (INamed H) (l ↦t v)%I)
  (at level 1,
   left associativity,
format "Γ H  :  '[' l  ↦t  v                  ']' '//'", only printing)
    : sim_scope.
Notation "Γ H : l ↦t [ v ] " := (Esnoc Γ (INamed H) (l ↦t v)%I)
  (at level 1,
   left associativity,
format "Γ H  :  '[' l  ↦t [ v ]                 ']' '//'", only printing)
    : sim_scope.
Notation "Γ H : l ↦{ q }t [ v ] " := (Esnoc Γ (INamed H) (l ↦t v)%I)
  (at level 1,
   left associativity,
format "Γ H  :  '[' l  ↦{ q }t [ v ]                 ']' '//'", only printing)
    : sim_scope.
Notation "Γ H : [ l := v ]t i" := (Esnoc Γ (INamed H) ([ l := v ]t i)%I)
  (at level 1,
   left associativity,
format "Γ H  :  '[' [  l  :=  v  ]t  i                 ']' '//'", only printing)
    : sim_scope.
Notation "Γ H : 'ldomain' Q " := (Esnoc Γ (INamed H) (ldomain_tgt _ Q)%I)
  (at level 1, left associativity, format "Γ H  :  '[' 'ldomain'  Q           ']' '//'", only printing)
    : sim_scope.
Notation "Γ H : 'block' l n " := (Esnoc Γ (INamed H) (target_block_size l n)%I)
  (at level 1, left associativity,
format "Γ H  :  '[' 'block'  l  n ']' '//'", only printing)
    : sim_scope.
Notation "Γ H : 'stack' P . " := (Esnoc Γ (INamed H) (stack_tgt P)%I)
  (at level 1, P at level 200,
   left associativity,
format "Γ H  :  '[' 'stack'  P                . ']' '//'", only printing)
    : sim_scope.
Notation "Γ H : 'alloca' Q " := (Esnoc Γ (INamed H) (alloca_tgt _ Q)%I)
  (at level 1, left associativity,
    format "Γ H  :  '[' 'alloca'  Q             ']' '//'", only printing)
    : sim_scope.

Notation "Γ H : P" := (Esnoc Γ (INamed H) P%I)
  (at level 1, P at level 200,
   left associativity, format "Γ H  :  '[' P ']' '//'", only printing) : proof_scope.
Notation "Γ H : P " := (Esnoc Γ (INamed H) P%I)
  (at level 1, P at level 200,
   left associativity, format "Γ H  :  '[' P ']' '//'", only printing) : sim_scope.

Notation "Γ '_' : P" := (Esnoc Γ (IAnon _) P%I)
  (at level 1, P at level 200,
   left associativity, format "Γ '_'  :  '[' P ']' '//'", only printing) : proof_scope.

Notation "Γ '------------------------------------------------------------------' □ '_____________target______________._____________source______________' Δ '------------------------------------------------------------------' ∗ Q" :=
  (envs_entails (Envs Γ Δ _) Q%I)
  (at level 1, Q at level 200, left associativity,
  format "'[' Γ '------------------------------------------------------------------' □ '//' '_____________target______________._____________source______________' '//' '//' Δ '------------------------------------------------------------------' ∗ '//' Q ']'", only printing) :
  stdpp_scope.

Notation "'`````````````````````````(target_instrs)`````````````````````````' et '``````````````````````````````````````````````````````````````````' '❲⪯❳' '`````````````````````````(source_instrs)`````````````````````````' es '``````````````````````````````````````````````````````````````````' '(Post-condition)~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~'  Q " :=

  (sim_expr (fun e_t e_s => (∃ x y, ⌜e_t ≅ Ret x⌝ ∗ ⌜e_s ≅ Ret y⌝ ∗ Q)%I) et es)
    (at level 70, Q at level 200,
      format "'[' '[hv' '`````````````````````````(target_instrs)`````````````````````````' '//' et '//' '``````````````````````````````````````````````````````````````````'  ']' '/'                                 '❲⪯❳' '//' '//' '[hv' '`````````````````````````(source_instrs)`````````````````````````' '//' es '//' '``````````````````````````````````````````````````````````````````' '//' ']' '(Post-condition)~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~' '//' '//' '[ ' Q ']'  ']'") : bi_scope.

Open Scope Z_scope.
Notation "'_' id" := (Raw id) (at level 30, format "'_' id").
Notation "'@' addr" := (UVALUE_Addr addr) (at level 30, format "'@' addr").
Notation "u_i32{ n }" := (UVALUE_I32 (DynamicValues.Int32.repr n)).
Notation "'@' addr" := (UVALUE_Addr (addr, 0)) (at level 30, format "'@' addr").
Notation "'i32' n" := (DVALUE_I32 (DynamicValues.Int32.repr n)) (at level 30).
Notation "'_'" := (IVoid _) (at level 30, format "'_'").
Notation "∅{ b }" := (make_empty_logical_block b) (at level 30, format "∅{ b }").
Notation "'some' ( n )" := (Some (N.to_nat n)) (at level 30, format "'some' ( n )").

Notation "'alloca' dt" := (INSTR_Alloca dt _ _) (at level 30).
Notation "'load' dt , du * % ptr" :=
  (INSTR_Load _ dt (du,ptr) _) (at level 30, format "load  dt ,  du *  % ptr").
Notation "'store' dt val , du * % ptr" :=
  (INSTR_Store _ (dt, val) (du, ptr) _)
    (at level 30, format "store  dt  val ,  du *  % ptr").

Notation "'call' dt  @ exp  ( args ) # attrs" :=
  (INSTR_Call (dt, exp) args attrs)
    (at level 30, format "call  dt  @ exp  ( args )  # attrs").

Notation "'ptr'" := DTYPE_Pointer.
Notation "int{ n }" := (EXP_Integer n) (at level 10, format "'int{' n }").
Notation "id{ id }" := (EXP_Ident (ID_Local id)) (at level 10, format "'id{' id }").


Notation "'`````````````````````````(target_instrs)`````````````````````````' x1 = x2 '``````````````````````````````````````````````````````````````````' '❲⪯❳' '`````````````````````````(source_instrs)`````````````````````````' x3 = x4 '``````````````````````````````````````````````````````````````````' '(Post-condition)~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~'  Q " :=

  (sim_expr Q (instr_conv (denote_instr (pair x1 x2))) (instr_conv (denote_instr (pair x3 x4))))
    (at level 70, Q at level 200,
      format "'[' '[hv' '`````````````````````````(target_instrs)`````````````````````````' '//' x1  =  x2 '//' '``````````````````````````````````````````````````````````````````'  ']' '/'                                 '❲⪯❳' '//' '//' '[hv' '`````````````````````````(source_instrs)`````````````````````````' '//' x3  =  x4 '//' '``````````````````````````````````````````````````````````````````' '//' ']' '(Post-condition)~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~' '//' '//' '[ ' Q ']'  ']'") : bi_scope.

Notation "x1 = x2 k" :=
  (ITree.bind (instr_conv (denote_instr (pair x1 x2))) (fun _ => (k)))
    (at level 30, k at level 30,
      right associativity,
      format "'[' x1  =  x2 ']' '//' '[' k ']'").

Notation "x1 = x2 '↵'" :=
  (ITree.bind (instr_conv (denote_instr (pair x1 x2))) (fun _ => Ret _))
    (at level 30, right associativity, format "'[' x1  =  x2     '↵' ']'").

(* Util tactics for instr-level proofs *)
Ltac clean :=
  rewrite ?mapsto_block_to_dvalue; try solve [constructor];
  cbn -[serialize_dvalue denote_instr];
  rewrite ?union_empty_r_L; try set_solver; try cont.

Ltac to_block :=
  rewrite -!mapsto_block_to_dvalue; try solve [constructor].
