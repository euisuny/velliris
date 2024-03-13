(** *Specification of attributes and events. *)

From iris.proofmode Require Export proofmode.
From iris.prelude Require Import options.
From iris.program_logic Require Export weakestpre total_weakestpre.
From iris.algebra.lib Require Import gset_bij.
From iris.base_logic.lib Require Export gen_heap gen_inv_heap ghost_var.

From simuliris.logic Require Import satisfiable.
From simuliris.simulation Require Import slsls simulation weakbisim.
From simuliris.vir Require Export vir heap heapbij val_rel.

From ITree Require Import Eq.Eqit Basics.HeterogeneousRelations
                          ITree RecursionFacts Interp.InterpFacts.
From Vellvm.Semantics Require Import InterpretationStack LLVMEvents.
From Vellvm Require Import Syntax.LLVMAst Handlers.Handlers.

From Paco Require Import paco.

From Coq Require Import Program.Equality.

From Equations Require Import Equations.
Set Default Proof Using "Type*".

Open Scope Z_scope.
Notation "# l" := (DVALUE_Addr (to_addr l)) (at level 30).

#[global] Instance attr_eq_dec: EqDecision fn_attr.
Proof. solve_decision. Defined.

Definition HasAttr : fn_attr -> list fn_attr -> bool :=
  fun attr l => 
    match l with
    | nil => false
    | l => 
      foldl (fun p b => 
        p || (Coqlib.proj_sumbool (decide (b = attr)))) false l
    end.

Definition HaveAttr : fn_attr -> list fn_attr -> list fn_attr -> bool :=
  fun attr l l' => HasAttr attr l && HasAttr attr l'.

Notation "d  ̂" := (dvalue_to_uvalue d) (at level 40).

(** *Attribute specifications *)
Section spec.
  Context Σ `{!sheapGS Σ, !checkedoutGS Σ, !heapbijGS Σ}.

  Definition frame_WF {A} (i_t i_s : list A) : iPropI Σ :=
    ((⌜length i_s > 0 -> length i_t > 0⌝)%Z)%I.

  Definition state_lookup (state : language.state vir_lang) (a : Z) v : iProp Σ :=
    let h := (vir_heap state.2) in
    ⌜h !! a = v⌝.

  Variant attr_case : Type :=
    | ARG_READ
    | WRITEONLY
    | NOFREE
    | ARGMONLY
    | READONLY
    | INACC_OR_ARGMONLY
    | OTHER.

  (** *Specification of memory-related function attributes

      Invariants about the checked-out set that holds before and after a call. *)
  (* For now, we only express invariants for specific attribute lists (instead of
     allowing for an arbitrary number of attribute combinations and disallowing
     certain combinations). *)
  Equations attribute_interp :
    ∀ {X Y : Type}, ExternalCallE X → ExternalCallE Y → gmap (loc * loc) Qp -> Prop :=
    attribute_interp
      (ExternalCall a f args_t attr_t)
      (ExternalCall a0 f0 args_s attr_s) C :=
       let attr_t := remove_tag attr_t in
       let attr_s := remove_tag attr_s in
       let have := fun attr => HaveAttr attr attr_t attr_s in
       ∃ (c : attr_case),
         match c with
         | ARG_READ => have FNATTR_Argmemonly && have FNATTR_Readonly /\
              (∀ l_t l_s n,
                  nth_error (zip args_t args_s) n =
                    Some (UVALUE_Addr l_t, UVALUE_Addr l_s) ->
                      ∃ q, C !! (l_t.1, l_s.1) = Some q ∧ Qp.lt q 1)
         | WRITEONLY => have FNATTR_Writeonly /\ C = ∅
         | NOFREE => have FNATTR_Nofree /\ C = ∅
         | ARGMONLY => have FNATTR_Argmemonly /\ not (have FNATTR_Readonly) /\
                      (∀ l_t l_s n,
                        nth_error (zip args_t args_s) n =
                          Some (UVALUE_Addr l_t, UVALUE_Addr l_s) ->
                        C !! (l_t.1, l_s.1) = None)
         | READONLY => have FNATTR_Readonly /\ not (have FNATTR_Argmemonly) /\
                        (∀ (l_t l_s : loc) q, C !! (l_t, l_s) = Some q -> Qp.lt q 1)
         | INACC_OR_ARGMONLY => have FNATTR_Inaccessiblemem_or_argmemonly /\
                      (∀ l_t l_s n,
                        nth_error (zip args_t args_s) n =
                          Some (UVALUE_Addr l_t, UVALUE_Addr l_s) ->
                        C !! (l_t.1, l_s.1) = None) /\
                      (∀ (l_t l_s : Z * Z),
                          (l_t.1, l_s.1) ∈ dom C ->
                          (UVALUE_Addr l_t, UVALUE_Addr l_s) ∉ (zip args_t args_s) ->
                          C !! (l_t.1, l_s.1) = Some 1%Qp)
         | OTHER =>
             not (have FNATTR_Argmemonly) /\
             not (have FNATTR_Readonly) /\
             not (have FNATTR_Writeonly) /\
             not (have FNATTR_Nofree) /\
             not (have FNATTR_Inaccessiblemem_or_argmemonly) /\
                  let ev_t := ExternalCall a f args_t attr_t in
                  let ev_s := ExternalCall a0 f0 args_s attr_s in
                   ev_t ~= ev_s /\ C = ∅
         end.

  Equations vir_call_ev {X Y} :
    language.CallE (call_events vir_lang) X →
    language.CallE (call_events vir_lang) Y →
    (gmap (loc * loc) Qp * list frame_names * list frame_names)%type -> iPropI Σ :=
    vir_call_ev (ExternalCall t f args attr) (ExternalCall t0 f0 args0 attr0) (C, i_t, i_s) :=
      (dval_rel f f0 ∗
        ⌜t = t0⌝ ∗ ⌜attr = attr0⌝ ∗ ([∗ list] x;y ∈ args; args0, uval_rel x y) ∗
        checkout C ∗ frame_WF i_t i_s ∗ stack_tgt i_t ∗ stack_src i_s ∗
        ⌜attribute_interp (ExternalCall t f args attr) (ExternalCall t0 f0 args0 attr0) C⌝)%I.

  Equations vir_call_ans {X Y : Type} :
    language.CallE (call_events vir_lang) X → X ->
    language.CallE (call_events vir_lang) Y → Y ->
    (gmap (loc * loc) Qp * list frame_names * list frame_names) -> iPropI Σ :=
      vir_call_ans (ExternalCall t f args attr) v_t
                  (ExternalCall t0 f0 args0 attr0) v_s (C, i_t, i_s) :=
        (checkout C ∗ stack_tgt i_t ∗ stack_src i_s ∗ uval_rel v_t v_s)%I.

  (* Readonly :
      initial and final states are identical. *)
  Equations readonly_ans_spec {R1 R2}
    (ev_t : CallEvents vir_lang R1) (v_t : R1) (ev_s : CallEvents vir_lang R2) (v_s : R2) : Prop :=
    readonly_ans_spec
      (StateEff (call_events vir_lang) (s, ExternalCall t f args attr)) v_t
      (StateEff (call_events vir_lang) (s0, ExternalCall t0 f0 args0 attr0)) v_s :=
    (v_t.1 = s /\ v_s.1 = s0).

  (* ArgMemOnly :
      All addr arguments have related values stored in the heap *)
  Equations argmemonly_ev_spec {R1 R2}
    (ev_t : CallEvents vir_lang R1) (ev_s : CallEvents vir_lang R2) : Prop :=
    argmemonly_ev_spec
      (StateEff (call_events vir_lang) (s, ExternalCall t f args attr))
      (StateEff (call_events vir_lang) (s0, ExternalCall t0 f0 args0 attr0)) :=
    (forall a v, UVALUE_Addr (a, 0)%Z ∈ args -> vir_heap s.2 !! a = Some v ->
            exists a0 v0, UVALUE_Addr (a0, 0)%Z ∈ args0 /\ vir_heap s0.2 !! a0 = Some v0 /\ v = v0) /\
    (forall a v, UVALUE_Addr (a, 0) ∈ args0 -> vir_heap s0.2 !! a = Some v ->
            exists a0 v0, UVALUE_Addr (a0, 0)%Z ∈ args /\ vir_heap s.2 !! a0 = Some v0 /\ v = v0).

  (* Every piece of state that is not part of the arguments is unchanged. *)
  Equations argmemonly_ans_spec {R1 R2}
    (ev_t : CallEvents vir_lang R1) (v_t : R1) (ev_s : CallEvents vir_lang R2) (v_s : R2) : Prop :=
    argmemonly_ans_spec
      (StateEff (call_events vir_lang) (s, ExternalCall t f args attr)) v_t
      (StateEff (call_events vir_lang) (s0, ExternalCall t0 f0 args0 attr0)) v_s :=
    ((∀ a v, vir_heap v_t.1.2 !! a = Some v ->
                UVALUE_Addr (a, 0) ∉ args ->
                vir_heap s.2 !! a = Some v) /\
          (∀ a v, vir_heap v_s.1.2 !! a = Some v ->
                  UVALUE_Addr (a, 0) ∉ args ->
                  vir_heap s0.2 !! a = Some v)).

  (* Specification for [nofree] and [writeonly] *)
  Equations no_free_ans_spec {R1 R2}
    (ev_t : CallEvents vir_lang R1) (v_t : R1) (ev_s : CallEvents vir_lang R2) (v_s : R2) : Prop :=
    no_free_ans_spec
      (StateEff (call_events vir_lang) (s, ExternalCall t f args attr)) v_t
      (StateEff (call_events vir_lang) (s0, ExternalCall t0 f0 args0 attr0)) v_s :=
      (forall a v, vir_heap s.2 !! a = Some v ->
             exists v', vir_heap v_t.1.2 !! a = Some v') /\
      (forall a v, vir_heap s0.2 !! a = Some v ->
             exists v', vir_heap v_s.1.2 !! a = Some v').

  Definition vir_E_ans : ∀ X Y : Type, E vir_lang X → X → E vir_lang Y → Y → Prop :=
    λ (X Y : Type) (X0 : E vir_lang X) (X1 : X) (X2 : E vir_lang Y) (X3 : Y),
      (X1 ~= X3 ∧ X0 ~= X2).

  Definition vir_call_ev_ : ∀ X Y : Type, CallEvents vir_lang X → CallEvents vir_lang Y → Prop :=
    λ (X Y : Type) (e1 : CallEvents vir_lang X) (e2 : CallEvents vir_lang Y),
    argmemonly_ev_spec e1 e2.

  Definition vir_E_ev : ∀ X Y : Type, E vir_lang X → E vir_lang Y → Prop :=
    λ (X Y : Type) (X0 : E vir_lang X) (X2 : E vir_lang Y), X0 ~= X2.

  Definition globalbij_interp (gs_t gs_s : vir.globals) : iProp Σ :=
      (Addr.null ↔h Addr.null) ∗
     ⌜dom gs_s ⊆ dom gs_t⌝ ∗ (* LATER: duplicated info: remove? *)
      target_globals (gs_t : leibnizO _) ∗ source_globals gs_s  ∗
     ([∗ map] g ↦ v ∈ gs_s, ∃ v', ⌜gs_t !! g = Some v'⌝ ∗ dval_rel v' v).

  #[global] Instance globalbij_interp_persistent gs_t gs_s:
    Persistent (globalbij_interp gs_t gs_s).
  Proof. apply _. Qed.

  #[global]
   Instance vir_simulirisGS : simulirisGS (iPropI Σ) vir_lang :=
    {| state_interp :=
        (fun (σ_t σ_s : vir_state) =>
           ∃ C S G,
                heap_ctx sheapG_heap_source
                  (vir_heap σ_s.2, vir_dyn σ_s.2) (vir.frames σ_s) G
                  (vir_locals σ_s)
                  (vir_local_stack σ_s)
              ∗ heap_ctx sheapG_heap_target
                  (vir_heap σ_t.2, vir_dyn σ_t.2) (vir.frames σ_t) G
                  (vir_locals σ_t)
                  (vir_local_stack σ_t)
              ∗ ghost_var checkedoutG_bij_name (1/2) C
              ∗ heapbij_interp S C ∗ ⌜dom C ⊆ S⌝
              ∗ globalbij_interp σ_t.1.1 σ_s.1.1
        )%I;
      call_ev := @vir_call_ev;
      call_ans := @vir_call_ans;
      arg_val_rel :=
        (λ '(u0, l0) '(u, l) '(C, i_t, i_s),
          frame_WF i_t i_s ∗
          checkout ∅ ∗ stack_tgt i_t ∗ stack_src i_s ∗
            dval_rel u0 u ∗ [∗ list] x;y ∈ l0; l, uval_rel x y)%I;
      res_val_rel :=
        (λ u v '(C, i_t, i_s),
          checkout ∅ ∗ stack_tgt i_t ∗ stack_src i_s ∗
           uval_rel u v)%I ; |}.

End spec.

Arguments frame_WF {_ _}.

#[global] Instance SimE_vir_iProp {Σ} `{!sheapGS Σ, !checkedoutGS Σ, !heapbijGS Σ}:
  SimE (iPropI Σ) vir_lang := sim_expr_stutter (η := vir_handler).

Arguments attribute_interp {_ _}.
Arguments sim_coind_ub {_ _ _ _ _} [_] {_ _ _ _ _}.
Arguments sim_coind_exc {_ _ _ _ _} [_] {_ _ _ _ _}.

From ITree Require Import Events.StateFacts.

(* Global Hint Extern 0 (handlers _) => apply vir_handler: typeclasses_instances. *)

Section vir_sim_properties.

  Context {Σ} `{!sheapGS Σ, !checkedoutGS Σ, !heapbijGS Σ}.

  Lemma sim_expr_exception {R} (e : _ R) s0 Φ:
    ⊢ e ⪯ trigger (Exception.Throw (print_msg s0)) [{ Φ }].
  Proof.
    rewrite sim_expr_eq /sim_expr_.
    iIntros (??) "SI". iModIntro.
    rewrite /interp_L2.
    rewrite StateFacts.interp_state_vis; cbn; rewrite /add_tau.
    cbn; rewrite /pure_state. rewrite bind_tau !bind_vis.
    iApply sim_coind_tauR.
    iApply sim_coind_exc.
  Qed.

  Lemma sim_expr_pick fn P:
    ⊢ trigger (pick fn P) ⪯ trigger (pick fn P) [{ (v_t, v_s), ⌜v_t = v_s⌝}].
  Proof.
    rewrite sim_expr_eq /sim_expr_.
    iIntros (??) "SI". iModIntro.
    rewrite /interp_L2.
    rewrite !interp_state_vis.
    rewrite /add_tau; cbn.
    rewrite /lift_undef_or_err.
    rewrite !bind_tau !bind_bind.

    iApply sim_coind_tau; cbn.
    rewrite /lift_undef_or_err.

    destruct (concretize_uvalue fn), unEitherT; [ | destruct s].
    { iApply sim_coind_ub. }
    { iApply sim_coind_exc. }

    rewrite !bind_ret_l !interp_state_ret.
    iApply sim_coind_tau.
    iApply sim_coind_base.
    iFrame.
    iExists _, _; eauto.
  Qed.

End vir_sim_properties.

From simuliris.simulation Require Import sim_properties.
From ITree Require Import Interp.TranslateFacts Events.StateFacts.

Notation "et '⪯' es [[ Φ ]]" :=
  (sim_expr' (η := vir_handler) Φ et es) (at level 70, Φ at level 200,
        format "'[hv' et  '⪯'  '/' es  '/' [[  '[ ' Φ  ']' ]] ']'") : bi_scope.

Section conv_properties.

  Context {Σ} `{!sheapGS Σ, !checkedoutGS Σ, !heapbijGS Σ}.

  Notation st_expr_rel' R1 R2 :=
    (@st_exprO' vir_lang R1 -d> @st_exprO' vir_lang R2 -d> iPropI Σ).

  Lemma eq2_exp_to_L0 :
    eq2 (cat exp_to_instr instrE_conv) exp_to_L0.
  Proof.
    repeat intro.
    rewrite /cat /Cat_IFun.
    destruct a as [ | [ | [ | [ | [ |  ] ] ] ] ]; rewrite /exp_to_instr;
      simp instrE_conv; rewrite /exp_to_L0 /instr_to_L0; auto.
  Qed.

  Lemma exp_conv_to_instr :
    forall T e1 e2 Φ,
      exp_conv e1 ⪯ exp_conv e2 [{ Φ }] -∗
      instr_conv (translate (T := T) exp_to_instr e1) ⪯
      instr_conv (translate (T := T) exp_to_instr e2) [{ Φ }].
  Proof.
    intros.
    iIntros "H".
    rewrite /instr_conv /exp_conv.
    rewrite !interp_translate.
    rewrite (eq_itree_interp
               (λ (T0 : Type) (e : exp_E T0), Vis (instrE_conv T0 (exp_to_instr e)) Monad.ret));
      last done.
    1 : rewrite (eq_itree_interp (λ (T0 : Type) (e : exp_E T0), Vis (instrE_conv T0 (exp_to_instr e)) Monad.ret));
      last done.
    1 : done.
    all: repeat intro; by rewrite -eq2_exp_to_L0.
  Qed.

  Lemma instr_to_L0' {T} e_t e_s Φ :
    instr_conv e_t ⪯ instr_conv e_s [[ Φ ]] -∗
    L0'expr_conv (translate (T := T) instr_to_L0' e_t) ⪯
    L0'expr_conv (translate (T := T) instr_to_L0' e_s) [[ Φ ]].
  Proof.
    iIntros "H".
    rewrite /instr_conv /L0'expr_conv.
    rewrite !interp_translate.
    rewrite (eq_itree_interp (λ (T0 : Type) (e : instr_E T0), Vis (call_conv T0 (instr_to_L0' e)) Monad.ret)
               _ _ _ _ e_t);
      [ | | done].
    1 : rewrite (eq_itree_interp (λ (T0 : Type) (e : instr_E T0), Vis (call_conv T0 (instr_to_L0' e)) Monad.ret));
      [ | | done].
    1: done.
    all: repeat intro;
      destruct a; try done;
      destruct s; try done;
      simp call_conv; cbn;
      destruct e; eauto;
      try destruct s; eauto;
      simp call_conv; cbn; eauto;
      repeat destruct s; cbn; try reflexivity.
  Qed.

  Lemma exp_conv_raise {R1 R2} e s (Φ : _ R1 -> _ R2 -> _):
    (⊢ e ⪯ exp_conv (raise s) [{ Φ }])%I.
  Proof.
    rewrite /exp_conv.
    rewrite <- bind_ret_r.
    setoid_rewrite interp_bind. iApply sim_expr_bind.
    rewrite interp_vis.
    rewrite sim_expr_eq /sim_expr_. rewrite /interp_L2.
    iIntros (??) "SI".
    rewrite interp_state_bind.
    rewrite interp_state_vis bind_bind. cbn; rewrite /add_tau;
      cbn; rewrite bind_tau /pure_state; cbn; rewrite !bind_bind bind_vis.
    iApply sim_coind_tauR; iApply sim_coind_exc.
  Qed.

  Lemma exp_conv_raiseUB {R1 R2} e s (Φ : _ R1 -> _ R2 -> _):
    (⊢ e ⪯ exp_conv (raiseUB s) [{ Φ }])%I.
  Proof.
    setoid_rewrite interp_bind.
    rewrite interp_vis.
    rewrite sim_expr_eq /sim_expr_. rewrite /interp_L2.
    iIntros (??) "SI".
    rewrite bind_bind interp_state_bind interp_state_vis; cbn; rewrite /add_tau;
      cbn; rewrite bind_tau /pure_state; cbn; rewrite !bind_bind bind_tau !bind_vis.
    iApply sim_coind_tauR; iApply sim_coind_ub.
  Qed.
   Lemma instr_conv_raise {R1 R2} e s (Φ : _ R1 -> _ R2 -> _):
    (⊢ e ⪯ instr_conv (raise s) [{ Φ }])%I.
  Proof.
    rewrite /instr_conv.
    rewrite <- bind_ret_r.
    setoid_rewrite interp_bind. iApply sim_expr_bind.
    rewrite interp_vis.
    rewrite sim_expr_eq /sim_expr_. rewrite /interp_L2.
    iIntros (??) "SI".
    rewrite interp_state_bind interp_state_vis; cbn; rewrite /add_tau;
      cbn; rewrite bind_tau /pure_state; cbn;
      rewrite !bind_bind bind_vis bind_tau bind_vis.
    iApply sim_coind_tauR; iApply sim_coind_exc.
  Qed.

  Lemma instr_conv_raiseUB {R1 R2} e s (Φ : _ R1 -> _ R2 -> _):
    (⊢ e ⪯ instr_conv (raiseUB s) [{ Φ }])%I.
  Proof.
    rewrite /instr_conv.
    setoid_rewrite interp_bind.
    rewrite interp_vis.
    rewrite sim_expr_eq /sim_expr_. rewrite /interp_L2.
    iIntros (??) "SI".
    rewrite !interp_state_bind bind_bind interp_state_vis bind_bind.
    rewrite /add_tau;
      cbn; rewrite bind_tau /pure_state; cbn -[state_interp].
    rewrite !bind_bind !bind_vis.
    iApply sim_coind_tauR; iApply sim_coind_ub.
  Qed.

  Lemma sim_pick (v_t v_s : uvalue) f_t f_s
    (Φ : expr vir_lang dvalue -> expr vir_lang dvalue -> iPropI Σ):
    uval_rel v_t v_s -∗
    trigger (pick v_t f_t) ⪯ trigger (pick v_s f_s)
    [{ (dv_t, dv_s), dval_rel dv_t dv_s }].
  Proof.
    iIntros "Hv".

    rewrite sim_expr_eq /sim_expr_.
    iIntros (??) "SI".

    rewrite /interp_L2 /instr_conv /concretize_or_pick.
    rewrite !interp_state_vis; cbn.
    rewrite /add_tau; cbn.
    rewrite /lift_undef_or_err; cbn.
    rewrite !bind_tau !bind_bind.
    iApply sim_coind_tau.

    destruct (concretize_uvalue v_s) eqn: Hv_s.
    destruct unEitherT; [ | destruct s].

    { (* UB case*)
      setoid_rewrite bind_vis; iApply sim_coind_ub. }
    { (* Exc case*)
      setoid_rewrite bind_vis; iApply sim_coind_exc. }

    iSpecialize ("Hv" $! _ Hv_s).
    iDestruct "Hv" as (??) "Hv". rewrite H; cbn.

    rewrite !bind_ret_l !interp_state_ret.
    iApply sim_coind_tau; iApply sim_coind_base; iFrame;
      iExists _, _; do 2 (iSplitL ""; [ done | ]); done.
  Qed.

  Lemma exp_conv_concretize_or_pick v_t v_s P_t P_s:
    uval_rel v_t v_s -∗
    exp_conv (concretize_or_pick v_t P_t) ⪯ exp_conv (concretize_or_pick v_s P_s)
    [{ (dv_t, dv_s), dval_rel dv_t dv_s }].
  Proof.
    iIntros "Hv".
    rewrite sim_expr_eq /sim_expr_.
    iIntros (??) "SI".

    rewrite /interp_L2 /exp_conv /concretize_or_pick.
    (* If both are concrete, that's fine *)
    destruct (is_concrete v_s) eqn: Hvs.
    { apply Is_true_eq_left in Hvs.
      apply is_concrete_concretize_uvalue in Hvs.
      destruct Hvs as (?&?&?); subst.
      iSpecialize ("Hv" $! _ H).
      iDestruct "Hv" as (??) "Hv".
      rewrite uvalue_to_dvalue_of_dvalue_to_uvalue.

      destruct (is_concrete v_t) eqn: Hvt.
      { apply Is_true_eq_left in Hvt.
        apply is_concrete_concretize_uvalue in Hvt.
        destruct Hvt as (?&?&?); subst. rewrite H1 in H0.
        inversion H0. rewrite uvalue_to_dvalue_of_dvalue_to_uvalue.
        rewrite /lift_err.
        iApply sim_coind_Proper.
        { cbn; rewrite interp_ret interp_state_ret; reflexivity. }
        { cbn; rewrite interp_ret interp_state_ret; reflexivity. }
        iApply sim_coind_base; iFrame.
        iExists _, _; iFrame; cbn; iSplitL ""; done. }
      { iApply sim_coind_Proper.
        { cbn; rewrite interp_vis bind_trigger; cbn.
          rewrite interp_state_vis; cbn.
          rewrite /add_tau; cbn; rewrite /lift_undef_or_err.
          rewrite bind_tau bind_bind.
          setoid_rewrite bind_ret_l.
          setoid_rewrite interp_state_tau; cbn.
          setoid_rewrite interp_ret.
          setoid_rewrite interp_state_ret; cbn.
          reflexivity. }
        { cbn; rewrite interp_ret interp_state_ret; reflexivity. }
        rewrite H0; cbn -[state_interp].

        iApply sim_coind_Proper; [ | reflexivity | ].
        { rewrite bind_ret_l; reflexivity. }

        do 3 iApply sim_coind_tauL; iApply sim_coind_base; iFrame.
        iExists _, _; iFrame; cbn; iSplitL ""; done. } }

    (* [v_s] not concrete *)
    destruct (is_concrete v_t) eqn: Hvt.
    { (* Problem : v_s is not concrete, v_t is concrete *)
      apply Is_true_eq_left in Hvt.
      apply is_concrete_concretize_uvalue in Hvt.
      destruct Hvt as (?&?&?); subst.
      iApply sim_coind_Proper.
      { rewrite /lift_err; cbn.
        rewrite uvalue_to_dvalue_of_dvalue_to_uvalue.
        rewrite interp_ret interp_state_ret; reflexivity. }
      { cbn; rewrite interp_vis bind_vis interp_state_vis; cbn.
        rewrite /add_tau; cbn; rewrite /lift_undef_or_err.
        rewrite bind_tau bind_bind.
        setoid_rewrite bind_ret_l.
        setoid_rewrite interp_ret.
        cbn. setoid_rewrite interp_state_bind.
        setoid_rewrite interp_state_ret; cbn.
        setoid_rewrite bind_ret_l.
        setoid_rewrite interp_state_tau.
        setoid_rewrite interp_state_ret; cbn.
        reflexivity. }

      iApply sim_coind_tauR.
      destruct (concretize_uvalue v_s) eqn: Hconc_v_s; destruct unEitherT; [ | destruct s].
      { iApply sim_coind_Proper; [ reflexivity | | ].
        { do 2 setoid_rewrite bind_vis; reflexivity. }
        iApply sim_coind_ub. }
      { iApply sim_coind_Proper; [ reflexivity | | ].
        { do 2 setoid_rewrite bind_vis; reflexivity. }
        iApply sim_coind_exc. }
      iApply sim_coind_Proper; [ reflexivity | by rewrite bind_ret_l | ].
      do 2 iApply sim_coind_tauR.
      iApply sim_coind_base; iFrame.
      iSpecialize ("Hv" $! _ Hconc_v_s).
      iDestruct "Hv" as (??) "Hv".
      rewrite concretize_uvalue_dvalue_to_uvalue in H0; inversion H0; subst.
      iExists _, _; iFrame; eauto. }

    (* both not concrete *)
    iApply sim_coind_Proper.
    { cbn; rewrite interp_vis bind_vis interp_state_vis; cbn.
      rewrite /add_tau; cbn.
      rewrite /lift_undef_or_err; cbn.
      rewrite bind_tau bind_bind.
      reflexivity. }
    { cbn; rewrite interp_vis bind_vis interp_state_vis; cbn.
      rewrite /add_tau; cbn.
      rewrite /lift_undef_or_err; cbn.
      rewrite bind_tau bind_bind.
      reflexivity. }
    iApply sim_coind_tau.

    destruct (concretize_uvalue v_s) eqn: Hv_s.
    destruct unEitherT eqn: H; [  | destruct s].

    { (* UB case*)
      iApply sim_coind_Proper; [ reflexivity | | ].
      { setoid_rewrite bind_vis. reflexivity. }
      iApply sim_coind_ub. }
    { (* Exc case*)
      iApply sim_coind_Proper; [ reflexivity | | ].
      { setoid_rewrite bind_vis. reflexivity. }
      iApply sim_coind_exc. }

    iSpecialize ("Hv" $! _ Hv_s).
    iDestruct "Hv" as (??) "Hv"; rewrite H0; cbn -[state_interp].
    iApply sim_coind_Proper;
    [ repeat rewrite bind_ret_l; by rewrite interp_ret interp_state_tau interp_state_ret |
      repeat rewrite bind_ret_l; by rewrite interp_ret interp_state_tau interp_state_ret |].
    do 2 iApply sim_coind_tau; iApply sim_coind_base; iFrame;
      iExists _, _; do 2 (iSplitL ""; [ done | ]); done.
  Qed.

  Lemma determine_uvalue_dvalue_to_uvalue v:
    determine_uvalue (dvalue_to_uvalue v) v.
  Proof.
    rewrite /determine_uvalue.
    rewrite is_concrete_dvalue_to_uvalue.
    by rewrite uvalue_to_dvalue_of_dvalue_to_uvalue.
  Qed.

  Lemma L0_conv_concretize_or_pick_strong v_t v_s P_t P_s:
    uval_rel v_t v_s -∗
    L0'expr_conv (concretize_or_pick v_t P_t) ⪯ L0'expr_conv (concretize_or_pick v_s P_s)
    [{ (dv_t, dv_s), dval_rel dv_t dv_s ∗
          ⌜determine_uvalue v_t dv_t⌝ ∗ ⌜determine_uvalue v_s dv_s⌝}].
  Proof.
    iIntros "Hv".
    rewrite sim_expr_eq /sim_expr_.
    iIntros (??) "SI".

    rewrite /interp_L2 /L0'expr_conv /concretize_or_pick.
    (* If both are concrete, that's fine *)
    destruct (is_concrete v_s) eqn: Hvs.
    { apply Is_true_eq_left in Hvs.
      apply is_concrete_concretize_uvalue in Hvs.
      destruct Hvs as (?&?&?); subst.
      iSpecialize ("Hv" $! _ H).
      iDestruct "Hv" as (??) "Hv".
      rewrite uvalue_to_dvalue_of_dvalue_to_uvalue.

      destruct (is_concrete v_t) eqn: Hvt.
      { apply Is_true_eq_left in Hvt.
        apply is_concrete_concretize_uvalue in Hvt.
        destruct Hvt as (?&?&?); subst. rewrite H1 in H0.
        inversion H0. rewrite uvalue_to_dvalue_of_dvalue_to_uvalue.
        rewrite /lift_err.
        iApply sim_coind_Proper.
        { cbn; rewrite interp_ret interp_state_ret; reflexivity. }
        { cbn; rewrite interp_ret interp_state_ret; reflexivity. }
        iApply sim_coind_base; iFrame.
        iExists _, _; iFrame; cbn; subst; repeat iSplitL ""; try done;
          iPureIntro; apply determine_uvalue_dvalue_to_uvalue. }
      { iApply sim_coind_Proper.
        { cbn; rewrite interp_vis bind_trigger interp_state_vis; cbn.
          rewrite /add_tau; cbn; rewrite /lift_undef_or_err.
          rewrite bind_tau bind_bind.
          setoid_rewrite bind_ret_l.
          setoid_rewrite interp_ret.
          setoid_rewrite interp_state_tau.
          setoid_rewrite interp_state_ret; cbn.
          reflexivity. }
        { cbn; rewrite interp_ret interp_state_ret; reflexivity. }
        rewrite H0; cbn -[state_interp].

        iApply sim_coind_Proper; [ | reflexivity | ].
        { rewrite bind_ret_l ; reflexivity. }

        do 3 iApply sim_coind_tauL; iApply sim_coind_base; iFrame.
        iExists _, _; iFrame; cbn; repeat iSplitL ""; try done; subst;
          [ | iPureIntro; apply determine_uvalue_dvalue_to_uvalue ].
        iPureIntro. rewrite /determine_uvalue.
        by rewrite Hvt. } }
    (* [v_s] not concrete *)
    destruct (is_concrete v_t) eqn: Hvt.
    { (* Problem : v_s is not concrete, v_t is concrete *)
      apply Is_true_eq_left in Hvt.
      apply is_concrete_concretize_uvalue in Hvt.
      destruct Hvt as (?&?&?); subst.
      iApply sim_coind_Proper.
      { rewrite /lift_err; cbn.
        rewrite uvalue_to_dvalue_of_dvalue_to_uvalue.
        rewrite interp_ret interp_state_ret; reflexivity. }
      { cbn; rewrite interp_vis bind_trigger interp_state_vis; cbn.
        rewrite /add_tau; cbn; rewrite /lift_undef_or_err.
        rewrite bind_tau bind_bind.
        setoid_rewrite bind_ret_l.
        setoid_rewrite interp_ret.
        setoid_rewrite interp_state_tau; cbn.
        setoid_rewrite interp_state_ret; cbn.
        reflexivity. }

      iApply sim_coind_tauR.
      destruct (concretize_uvalue v_s) eqn: Hconc_v_s; destruct unEitherT; [ | destruct s].
      { iApply sim_coind_Proper; [ reflexivity | | ].
        { do 2 setoid_rewrite bind_vis; reflexivity. }
        iApply sim_coind_ub. }
      { iApply sim_coind_Proper; [ reflexivity | | ].
        { do 2 setoid_rewrite bind_vis; reflexivity. }
        iApply sim_coind_exc. }
      iApply sim_coind_Proper; [ reflexivity | by rewrite bind_ret_l | ].
      do 2 iApply sim_coind_tauR.
      iApply sim_coind_base; iFrame.
      iSpecialize ("Hv" $! _ Hconc_v_s).
      iDestruct "Hv" as (??) "Hv".
      rewrite concretize_uvalue_dvalue_to_uvalue in H0; inversion H0; subst.
      iExists _, _; iFrame; eauto.
      try repeat iSplitL""; try done;
          [ iPureIntro; apply determine_uvalue_dvalue_to_uvalue | ].
      iPureIntro. rewrite /determine_uvalue. by rewrite Hvs. }

    (* both not concrete *)
    iApply sim_coind_Proper.
    { cbn; rewrite interp_vis bind_vis interp_state_vis; cbn.
      rewrite /add_tau; cbn.
      rewrite /lift_undef_or_err; cbn.
      rewrite bind_tau bind_bind.
      rewrite /concretize_picks; cbn.
      rewrite /lift_undef_or_err; cbn.
      reflexivity. }
    { cbn; rewrite interp_vis bind_vis interp_state_vis; cbn.
      rewrite /add_tau; cbn.
      rewrite /lift_undef_or_err; cbn.
      rewrite bind_tau bind_bind.
      rewrite /concretize_picks; cbn.
      rewrite /lift_undef_or_err; cbn.
      reflexivity. }
    iApply sim_coind_tau.

    destruct (concretize_uvalue v_s) eqn: Hv_s.

    destruct unEitherT eqn: H; [  | destruct s].

    { (* UB case*)
      iApply sim_coind_Proper; [ reflexivity | | ].
      { setoid_rewrite bind_vis. reflexivity. }
      iApply sim_coind_ub. }
    { (* Exc case*)
      iApply sim_coind_Proper; [ reflexivity | | ].
      { setoid_rewrite bind_vis. reflexivity. }
      iApply sim_coind_exc. }

    iSpecialize ("Hv" $! _ Hv_s).
    iDestruct "Hv" as (??) "Hv"; rewrite H0; cbn -[state_interp].
    iApply sim_coind_Proper;
    [ repeat rewrite bind_ret_l;
        rewrite interp_ret interp_state_tau interp_state_ret; by cbn |
      repeat rewrite bind_ret_l;
        rewrite interp_ret interp_state_tau interp_state_ret; by cbn | ];
    do 2 iApply sim_coind_tau; iApply sim_coind_base; iFrame;
      iExists _, _; do 2 (iSplitL ""; [ done | ]); try done; iFrame.
    cbn.

    rewrite /determine_uvalue; rewrite Hvs Hvt. iSplitL ""; done.
  Qed.

  Lemma instr_conv_concretize_or_pick_strong v_t v_s P_t P_s:
    uval_rel v_t v_s -∗
    instr_conv (concretize_or_pick v_t P_t) ⪯ instr_conv (concretize_or_pick v_s P_s)
    [{ (dv_t, dv_s), dval_rel dv_t dv_s ∗
          ⌜determine_uvalue v_t dv_t⌝ ∗ ⌜determine_uvalue v_s dv_s⌝}].
  Proof.
    iIntros "Hv".
    rewrite sim_expr_eq /sim_expr_.
    iIntros (??) "SI".

    rewrite /interp_L2 /instr_conv /concretize_or_pick.
    (* If both are concrete, that's fine *)
    destruct (is_concrete v_s) eqn: Hvs.
    { apply Is_true_eq_left in Hvs.
      apply is_concrete_concretize_uvalue in Hvs.
      destruct Hvs as (?&?&?); subst.
      iSpecialize ("Hv" $! _ H).
      iDestruct "Hv" as (??) "Hv".
      rewrite uvalue_to_dvalue_of_dvalue_to_uvalue.

      destruct (is_concrete v_t) eqn: Hvt.
      { apply Is_true_eq_left in Hvt.
        apply is_concrete_concretize_uvalue in Hvt.
        destruct Hvt as (?&?&?); subst. rewrite H1 in H0.
        inversion H0. rewrite uvalue_to_dvalue_of_dvalue_to_uvalue.
        rewrite /lift_err.
        iApply sim_coind_Proper.
        { cbn; rewrite interp_ret interp_state_ret; reflexivity. }
        { cbn; rewrite interp_ret interp_state_ret; reflexivity. }
        iApply sim_coind_base; iFrame.
        iExists _, _; iFrame; cbn; subst; repeat iSplitL ""; try done;
          iPureIntro; apply determine_uvalue_dvalue_to_uvalue. }
      { iApply sim_coind_Proper.
        { cbn; rewrite interp_vis bind_trigger interp_state_vis; cbn.
          rewrite /add_tau; cbn; rewrite /lift_undef_or_err.
          rewrite bind_tau bind_bind.
          setoid_rewrite bind_ret_l.
          setoid_rewrite interp_ret.
          setoid_rewrite interp_state_tau.
          setoid_rewrite interp_state_ret; cbn.
          reflexivity. }
        { cbn; rewrite interp_ret interp_state_ret; reflexivity. }
        rewrite H0; cbn -[state_interp].

        iApply sim_coind_Proper; [ | reflexivity | ].
        { rewrite bind_ret_l ; reflexivity. }

        do 3 iApply sim_coind_tauL; iApply sim_coind_base; iFrame.
        iExists _, _; iFrame; cbn; repeat iSplitL ""; try done; subst;
          [ | iPureIntro; apply determine_uvalue_dvalue_to_uvalue ].
        iPureIntro. rewrite /determine_uvalue.
        by rewrite Hvt. } }
    (* [v_s] not concrete *)
    destruct (is_concrete v_t) eqn: Hvt.
    { (* Problem : v_s is not concrete, v_t is concrete *)
      apply Is_true_eq_left in Hvt.
      apply is_concrete_concretize_uvalue in Hvt.
      destruct Hvt as (?&?&?); subst.
      iApply sim_coind_Proper.
      { rewrite /lift_err; cbn.
        rewrite uvalue_to_dvalue_of_dvalue_to_uvalue.
        rewrite interp_ret interp_state_ret; reflexivity. }
      { cbn; rewrite interp_vis bind_trigger interp_state_vis; cbn.
        rewrite /add_tau; cbn; rewrite /lift_undef_or_err.
        rewrite bind_tau bind_bind.
        setoid_rewrite bind_ret_l.
        setoid_rewrite interp_ret.
        setoid_rewrite interp_state_tau; cbn.
        setoid_rewrite interp_state_ret; cbn.
        reflexivity. }

      iApply sim_coind_tauR.
      destruct (concretize_uvalue v_s) eqn: Hconc_v_s; destruct unEitherT; [ | destruct s].
      { iApply sim_coind_Proper; [ reflexivity | | ].
        { do 2 setoid_rewrite bind_vis; reflexivity. }
        iApply sim_coind_ub. }
      { iApply sim_coind_Proper; [ reflexivity | | ].
        { do 2 setoid_rewrite bind_vis; reflexivity. }
        iApply sim_coind_exc. }
      iApply sim_coind_Proper; [ reflexivity | by rewrite bind_ret_l | ].
      do 2 iApply sim_coind_tauR.
      iApply sim_coind_base; iFrame.
      iSpecialize ("Hv" $! _ Hconc_v_s).
      iDestruct "Hv" as (??) "Hv".
      rewrite concretize_uvalue_dvalue_to_uvalue in H0; inversion H0; subst.
      iExists _, _; iFrame; eauto.
      try repeat iSplitL""; try done;
          [ iPureIntro; apply determine_uvalue_dvalue_to_uvalue | ].
      iPureIntro. rewrite /determine_uvalue. by rewrite Hvs. }

    (* both not concrete *)
    iApply sim_coind_Proper.
    { cbn; rewrite interp_vis bind_vis interp_state_vis; cbn.
      rewrite /add_tau; cbn.
      rewrite /lift_undef_or_err; cbn.
      rewrite bind_tau bind_bind.
      rewrite /concretize_picks; cbn.
      rewrite /lift_undef_or_err; cbn.
      reflexivity. }
    { cbn; rewrite interp_vis bind_vis interp_state_vis; cbn.
      rewrite /add_tau; cbn.
      rewrite /lift_undef_or_err; cbn.
      rewrite bind_tau bind_bind.
      rewrite /concretize_picks; cbn.
      rewrite /lift_undef_or_err; cbn.
      reflexivity. }
    iApply sim_coind_tau.

    destruct (concretize_uvalue v_s) eqn: Hv_s.

    destruct unEitherT eqn: H; [  | destruct s].

    { (* UB case*)
      iApply sim_coind_Proper; [ reflexivity | | ].
      { setoid_rewrite bind_vis. reflexivity. }
      iApply sim_coind_ub. }
    { (* Exc case*)
      iApply sim_coind_Proper; [ reflexivity | | ].
      { setoid_rewrite bind_vis. reflexivity. }
      iApply sim_coind_exc. }

    iSpecialize ("Hv" $! _ Hv_s).
    iDestruct "Hv" as (??) "Hv"; rewrite H0; cbn -[state_interp].
    iApply sim_coind_Proper;
    [ repeat rewrite bind_ret_l;
        rewrite interp_ret interp_state_tau interp_state_ret; by cbn |
      repeat rewrite bind_ret_l;
        rewrite interp_ret interp_state_tau interp_state_ret; by cbn | ];
    do 2 iApply sim_coind_tau; iApply sim_coind_base; iFrame;
      iExists _, _; do 2 (iSplitL ""; [ done | ]); try done; iFrame.
    cbn.

    rewrite /determine_uvalue; rewrite Hvs Hvt. iSplitL ""; done.
  Qed.

  Lemma instr_conv_concretize_or_pick v_t v_s P_t P_s:
    uval_rel v_t v_s -∗
    instr_conv (concretize_or_pick v_t P_t) ⪯ instr_conv (concretize_or_pick v_s P_s)
    [{ (dv_t, dv_s), dval_rel dv_t dv_s }].
  Proof.
    iIntros "Hv".
    rewrite sim_expr_eq /sim_expr_.
    iIntros (??) "SI".

    rewrite /interp_L2 /instr_conv /concretize_or_pick.
    (* If both are concrete, that's fine *)
    destruct (is_concrete v_s) eqn: Hvs.
    { apply Is_true_eq_left in Hvs.
      apply is_concrete_concretize_uvalue in Hvs.
      destruct Hvs as (?&?&?); subst.
      iSpecialize ("Hv" $! _ H).
      iDestruct "Hv" as (??) "Hv".
      rewrite uvalue_to_dvalue_of_dvalue_to_uvalue.

      destruct (is_concrete v_t) eqn: Hvt.
      { apply Is_true_eq_left in Hvt.
        apply is_concrete_concretize_uvalue in Hvt.
        destruct Hvt as (?&?&?); subst. rewrite H1 in H0.
        inversion H0. rewrite uvalue_to_dvalue_of_dvalue_to_uvalue.
        rewrite /lift_err.
        iApply sim_coind_Proper.
        { cbn; rewrite interp_ret interp_state_ret; reflexivity. }
        { cbn; rewrite interp_ret interp_state_ret; reflexivity. }
        iApply sim_coind_base; iFrame.
        iExists _, _; iFrame; cbn; iSplitL ""; done. }
      { iApply sim_coind_Proper.
        { cbn; rewrite interp_vis bind_trigger interp_state_vis; cbn.
          rewrite /add_tau; cbn; rewrite /lift_undef_or_err.
          rewrite bind_tau bind_bind.
          setoid_rewrite bind_ret_l.
          setoid_rewrite interp_ret.
          setoid_rewrite interp_state_tau; cbn.
          setoid_rewrite interp_state_ret; cbn.
          reflexivity. }
        { cbn; rewrite interp_ret interp_state_ret; reflexivity. }
        rewrite H0; cbn -[state_interp].

        iApply sim_coind_Proper; [ | reflexivity | ].
        { rewrite bind_ret_l; reflexivity. }

        do 3 iApply sim_coind_tauL; iApply sim_coind_base; iFrame.
        iExists _, _; iFrame; cbn; iSplitL ""; done. } }

    (* [v_s] not concrete *)
    destruct (is_concrete v_t) eqn: Hvt.
    { (* Problem : v_s is not concrete, v_t is concrete *)
      apply Is_true_eq_left in Hvt.
      apply is_concrete_concretize_uvalue in Hvt.
      destruct Hvt as (?&?&?); subst.
      iApply sim_coind_Proper.
      { rewrite /lift_err; cbn.
        rewrite uvalue_to_dvalue_of_dvalue_to_uvalue.
        rewrite interp_ret interp_state_ret; reflexivity. }
      { cbn; rewrite interp_vis bind_trigger interp_state_vis; cbn.
        rewrite /add_tau; cbn; rewrite /lift_undef_or_err.
        rewrite bind_tau bind_bind.
        setoid_rewrite bind_ret_l.
        setoid_rewrite interp_ret.
        setoid_rewrite interp_state_tau; cbn.
        setoid_rewrite interp_state_ret; cbn.
        reflexivity. }

      iApply sim_coind_tauR.
      destruct (concretize_uvalue v_s) eqn: Hconc_v_s; destruct unEitherT; [ | destruct s].
      { iApply sim_coind_Proper; [ reflexivity | | ].
        { do 2 setoid_rewrite bind_vis; reflexivity. }
        iApply sim_coind_ub. }
      { iApply sim_coind_Proper; [ reflexivity | | ].
        { do 2 setoid_rewrite bind_vis; reflexivity. }
        iApply sim_coind_exc. }
      iApply sim_coind_Proper; [ reflexivity | by rewrite bind_ret_l | ].
      do 2 iApply sim_coind_tauR.
      iApply sim_coind_base; iFrame.
      iSpecialize ("Hv" $! _ Hconc_v_s).
      iDestruct "Hv" as (??) "Hv".
      rewrite concretize_uvalue_dvalue_to_uvalue in H0; inversion H0; subst.
      iExists _, _; iFrame; eauto. }

    (* both not concrete *)
    iApply sim_coind_Proper.
    { cbn; rewrite interp_vis bind_vis interp_state_vis; cbn.
      rewrite /add_tau; cbn.
      rewrite /lift_undef_or_err; cbn.
      rewrite bind_tau bind_bind.
      rewrite /concretize_picks; cbn.
      rewrite /lift_undef_or_err; cbn.
      reflexivity. }
    { cbn; rewrite interp_vis bind_vis interp_state_vis; cbn.
      rewrite /add_tau; cbn.
      rewrite /lift_undef_or_err; cbn.
      rewrite bind_tau bind_bind.
      rewrite /concretize_picks; cbn.
      rewrite /lift_undef_or_err; cbn.
      reflexivity. }
    iApply sim_coind_tau.

    destruct (concretize_uvalue v_s) eqn: Hv_s.

    destruct unEitherT eqn: H; [  | destruct s].

    { (* UB case*)
      iApply sim_coind_Proper; [ reflexivity | | ].
      { setoid_rewrite bind_vis. reflexivity. }
      iApply sim_coind_ub. }
    { (* Exc case*)
      iApply sim_coind_Proper; [ reflexivity | | ].
      { setoid_rewrite bind_vis. reflexivity. }
      iApply sim_coind_exc. }

    iSpecialize ("Hv" $! _ Hv_s).
    iDestruct "Hv" as (??) "Hv"; rewrite H0; cbn -[state_interp].
    iApply sim_coind_Proper;
    [ repeat rewrite bind_ret_l;
        rewrite interp_ret interp_state_tau interp_state_ret; by cbn |
      repeat rewrite bind_ret_l;
        rewrite interp_ret interp_state_tau interp_state_ret; by cbn | ];
    do 2 iApply sim_coind_tau; iApply sim_coind_base; iFrame;
      iExists _, _; do 2 (iSplitL ""; [ done | ]); done.
  Qed.

  Lemma state_interp_null_bij σ_t σ_s :
    state_interp σ_t σ_s -∗
      Addr.null ↔h Addr.null ∗ state_interp σ_t σ_s.
  Proof.
    iIntros "SI".
    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & %Hbij_WF & SI)".
    iDestruct "SI" as "(#N & SI)". iFrame.
    iSplitL ""; [done | ].
    repeat iExists _; iFrame; by iSplitL "".
  Qed.

  Lemma sim_null_bij {R1 R2} (e_t : _ R1) (e_s : _ R2) Φ:
    (Addr.null ↔h Addr.null -∗ e_t ⪯ e_s [{ Φ }]) -∗
    e_t ⪯ e_s [{ Φ }].
  Proof.
    iIntros "H".
    iApply sim_update_si.
    iIntros (??) "SI".
    iDestruct (state_interp_null_bij with "SI") as "(#Hnull&SI)".
    iSpecialize ("H" with "Hnull").
    by iFrame.
  Qed.

End conv_properties.
