From iris.prelude Require Import options.

From velliris.program_logic Require Import program_logic.
From velliris.vir.lang Require Export lang.
From velliris.vir.rules Require Export event_laws frame_laws instr_laws.

Import DenoteTactics.

Set Default Proof Using "Type*".

(*TODO move *)
Global Arguments sim_expr' : simpl never.

Section simulations.
  Context `{!vellirisGS Σ}.

(** Expression simulation / triples *)
  Definition expr_sim (e1 e2 : exp dtyp) (t1 t2 : option dtyp) (Φ : expr vir_lang uvalue → expr vir_lang uvalue → iProp Σ) : iProp Σ :=
    exp_conv (denote_exp t1 e1) ⪯ exp_conv (denote_exp t2 e2) [{ Φ }].
  Definition expr_source_red (e : exp dtyp) (t : option dtyp) (Φ : expr vir_lang uvalue → iProp Σ) : iProp Σ :=
    source_red (exp_conv (denote_exp t e)) Φ.
  Definition expr_target_red (e : exp dtyp) (t : option dtyp) (Φ : expr vir_lang uvalue → iProp Σ) : iProp Σ :=
    target_red (exp_conv (denote_exp t e)) Φ.

  (** Single instruction simulation / triples *)
Definition instr_sim (s1 s2 : instr_id * instr dtyp) (Φ : expr vir_lang () → expr vir_lang () → iProp Σ) : iProp Σ :=
instr_conv (denote_instr s1) ⪯ instr_conv (denote_instr s2) [{ Φ }].
  Definition instr_source_red (s : instr_id * instr dtyp) (Φ : expr vir_lang () → iProp Σ) : iProp Σ :=
    source_red (instr_conv (denote_instr s)) Φ.
  Definition instr_target_red (s : instr_id * instr dtyp) (Φ : expr vir_lang () → iProp Σ) : iProp Σ :=
    target_red (instr_conv (denote_instr s)) Φ.


(*
  denote_mcfg
  denote_function
  denote_cfg
  Search mcfg.
  mcfg
  cfg
  ocfg

  (*Definition code_sim (p1 : *)

  denote_terminator
denote_cfg
denote_ocfg
  *)

  Record block_context : Type := mk_block_context {
    (* current block *)
    block_src : block_id;
    (* previous block *)
    block_from : block_id;
    (* ocfg *)
    block_ocfg : ocfg dtyp;
  }.
  Definition block_context_branch (b : block_context) (to : block_id) : block_context :=
    mk_block_context to b.(block_src) b.(block_ocfg).

  Record block_body : Type := mk_block_body {
    block_phis : list (local_id * phi dtyp);
    block_code : code dtyp;
    block_term : terminator dtyp;
  }.

  Definition body_of_block (b : LLVMAst.block dtyp) : block_body :=
    mk_block_body b.(blk_phis) b.(blk_code) b.(blk_term).

  (* Simulate the whole function starting in the current context *)
  (* Returns pair of current and next block, or return value *)
  Definition block_context_sim (κ_t κ_s : block_context) (Φ : expr vir_lang (block_id * block_id + uvalue) → expr vir_lang (block_id * block_id + uvalue) → iProp Σ) : iProp Σ :=
    instr_conv (denote_ocfg κ_t.(block_ocfg) (κ_t.(block_from), κ_t.(block_src))) ⪯
    instr_conv (denote_ocfg κ_s.(block_ocfg) (κ_s.(block_from), κ_s.(block_src))) ⦉ Φ ⦊.

  (* Denote the current function, starting with a (partial) block body *)
  Definition denote_partial_block (b : block_body) (κ : block_context) :=
    (* First denote the current block... *)
    bind (denote_phis κ.(block_from) b.(block_phis))
      (λ _, bind (denote_code b.(block_code))
        (λ _, bind (translate exp_to_instr (denote_terminator b.(block_term)))
          (* ... then optionally continue with the next block *)
          (λ r, match r with
                | inl bnext => Tau (denote_ocfg κ.(block_ocfg) (κ.(block_src), bnext))
                | inr res => Ret (inr res)
                end
          )
        )).

  (* simulate fragments of blocks *)
  (* Returns the next block to jump to, or the return value *)
  Definition block_sim (body_t body_s : block_body) (κ_t κ_s : block_context) (Φ : expr vir_lang (block_id * block_id + uvalue) → expr vir_lang (block_id * block_id + uvalue) → iProp Σ) : iProp Σ :=
    instr_conv (denote_partial_block body_t κ_t) ⪯
    instr_conv (denote_partial_block body_s κ_s) ⦉ Φ ⦊.



  (*
     This doesn't allow us to go to the next block on just one side.
      To go to the post,  we need a Ret on both sides, so that doesn't work.
   *)

  (*
     Q: does branch evaluate to a value or does it continue?
      - for coinduction I want it to evaluate to a value.
      - for other stuff it should be continuing.

   *)

  (* What if I make it part of the syntax -> doesn't work because we need itrees as syntax.
  *)

  (*
     If I go with the direct syntax thing I can get from Simuliris, I will have the problem that I don't get access to the block_context in the post.




   *)



  (*Definition block_sim_iter :=*)
    (*curry (fixpoint.bi_least_fixpoint block_sim_iter_step).*)
      (*(λ rec *)


  (* I guess I could do a least fixpoint where I only interpret one step at a time, and iterate this. *)


  (* We can unfold the source of the current block. *)
  Lemma block_context_sim_unfold_block κ_t κ_s b_t b_s Φ :
    find_block κ_t.(block_ocfg) κ_t.(block_src) = Some b_t →
    find_block κ_s.(block_ocfg) κ_s.(block_src) = Some b_s →
    block_sim (body_of_block b_t) (body_of_block b_s) κ_t κ_s Φ -∗
    block_context_sim κ_t κ_s Φ.
  Proof.
  Admitted.
End simulations.

Notation "'p:' p 's:' s 't:' t" := (mk_block_body p s t) (at level 60).
Notation "'s:' s 't:' t" := (mk_block_body [] s t) (at level 60).
Notation "'t:' t" := (mk_block_body [] [] t) (at level 60).

Notation "'SIM{' κt ';' κs '}' bt '⪯' bs '[{' Φ '}]'" := (block_sim bt bs κt κs Φ) (at level 70, bt at level 60, bs at level 60) : bi_scope.

(*Lemma denote_code_cons : *)

Section block_laws.
  Context `{!vellirisGS Σ}.

  (** Focus on instructions *)
  Lemma block_focus_instr_target κt κs i_t t_t s_t b_s Φ :
    target_red <{ i_t }> (lift_unary_post (λ _,
        SIM{κt; κs} s: s_t t: t_t ⪯ b_s [{ Φ }])) -∗
    SIM{κt; κs} s: i_t :: s_t t: t_t ⪯ b_s [{ Φ }].
  Proof.
    iIntros "Ht".
    rewrite /block_sim /denote_partial_block.

    iApply target_red_sim_expr'.
    simpl.
    target_simp.
    iApply target_red_eq_itree.
    { rewrite denote_code_cons. rewrite instr_conv_bind. reflexivity. }
    target_simp.

    iApply (target_red_wand with "Ht").
    iIntros (?) "(%v & %Heq & Hsim)".
    target_simp.
    target_simp.
    iApply target_red_base.
    iApply target_red_base.


    (* TODO: needs some kind of inversion / better rewriting with equivalences *)
    (*Search sim_expr "inv".*)
  Admitted.

  Lemma block_focus_instr_source κt κs i_s t_s s_s b_t Φ :
    source_red <{ i_s }> (lift_unary_post (λ _,
        SIM{κt; κs} b_t ⪯ s: s_s t: t_s [{ Φ }])) -∗
    SIM{κt; κs} b_t ⪯ s: i_s :: s_s t: t_s [{ Φ }].
  Proof.

  Admitted.

  (** Return *)
  Lemma block_return κt κs e_t e_s Φ :
    target_red <{ e_t }>te (lift_unary_post (λ v_t,
      source_red <{ e_s }>te (lift_unary_post (λ v_s,
        Φ (Ret (inr v_t)) (Ret (inr v_s)))))) -∗
    SIM{κt; κs} t: TERM_Ret e_t ⪯ t: TERM_Ret e_s [{ Φ }].
  Proof.
    iIntros "Ha".
    rewrite /block_sim /denote_partial_block.
    simpl.

    iApply target_red_sim_expr'.
    target_simp.
    destruct e_t.
    iApply target_red_eq_itree.
    { rewrite exp_conv_bind. reflexivity. }
    target_simp.
    iApply (target_red_wand with "Ha").
    iIntros (e_t') "(%v_t & %Heq_t & Ha)".
    target_simp. target_simp.

    iApply source_red_sim_expr'.
    source_simp.
    destruct e_s.
    iApply source_red_eq_itree.
    { rewrite exp_conv_bind. reflexivity. }
    source_simp.
    iApply (source_red_wand with "Ha").
    iIntros (e_s') "(%v_s & %Heq_s & Ha)".
    source_simp. source_simp.

    by iApply sim_expr'_base.
  Qed.

  Lemma block_return_void κt κs Φ :
    Φ (Ret (inr UVALUE_None)) (Ret (inr UVALUE_None)) -∗
    SIM{κt; κs} t: TERM_Ret_void ⪯ t: TERM_Ret_void [{ Φ }].
  Proof.
    iIntros "Ha".
    rewrite /block_sim /denote_partial_block.
    simpl.
    iApply target_red_sim_expr'.
    target_simp.

    iApply source_red_sim_expr'.
    source_simp.

    by iApply sim_expr'_base.
  Qed.

  Lemma denote_ocfg_unfold oc from src b :
    find_block oc src = Some b →
    denote_ocfg oc (from, src) ≅
    Tau (bind (denote_phis from (blk_phis b))
    (λ _ : (),
       bind (denote_code (blk_code b))
         (λ _ : (),
            bind (translate exp_to_instr (denote_terminator (blk_term b)))
              (λ r : block_id + uvalue,
                 match r with
                 | inl bnext =>
                     (denote_ocfg oc (src, bnext))
                 | inr res => Ret (inr res)
                 end)))).
  Proof.
    intros Hlook.
    rewrite /denote_ocfg.
    rewrite unfold_iter_ktree.
    rewrite Hlook.
    (*
    rewrite ret_bind_l.
    rewrite /bind. simpl.

    (*rewrite iter_unfold. *)
    Search CategoryOps.iter.
    rewrite unfold_iter.
    Search ITree.iter.
    denote_partial_block
     *)
  Abort.


  (** Branch *)
  Lemma block_branch_target κt κs b_t b_s b_t' Φ :
    let κt' := block_context_branch κt b_t in
    find_block κt.(block_ocfg) b_t = Some b_t' →
    SIM{κt'; κs} body_of_block b_t' ⪯ b_s [{ Φ }] -∗
    SIM{κt; κs} t: TERM_Br_1 b_t ⪯ b_s [{ Φ }].
  Proof.
    iIntros (κt' Hfind) "Ha".
    rewrite /block_sim /denote_partial_block.
    iApply target_red_sim_expr'.
    simpl.
    target_simp.
    (*iApply target_red_eq_itree.*)
    (*{ rewrite instr_conv_tau.*)
      (*reflexivity. } *)
    iApply target_red_base.

    (* TODO: can I commute the Tau? *)


    (*

      rewrite /denote_ocfg.
      rewrite unfold_iter_ktree.
      rewrite Hfind.
      (*rewrite instr_conv_bind.*)
      do 3 rewrite instr_conv_bind.
      reflexivity. }
    target_simp.
    iApply target_red_base.
    iApply target_red_base.
    Search "guarded" "iter".
    Search ITree.guarded_iter
    denote_ocfg
     *)

    (* TODO: what about the tau I have here? *)
  Admitted.

  Lemma block_branch_source κt κs b_t b_s b_s' Φ :
    let κs' := block_context_branch κs b_s in
    find_block κs.(block_ocfg) b_s = Some b_s' →
    SIM{κt; κs'} b_t ⪯ body_of_block b_s' [{ Φ }] -∗
    SIM{κt; κs} b_t ⪯ t: TERM_Br_1 b_s [{ Φ }].
  Proof.
  Admitted.

  (* TODO: conditional branches *)

  (** Coinduction *)

  (* Go to the postcondition during a branch on both sides *)
  Lemma block_branch_base κt κs b_t b_s Φ :
    Φ (instr_conv $ denote_ocfg κt.(block_ocfg) (κt.(block_src), b_t)) (instr_conv $ denote_ocfg κs.(block_ocfg) (κs.(block_src), b_s)) -∗
    SIM{κt; κs} t: TERM_Br_1 b_t ⪯ t: TERM_Br_1 b_s [{ Φ }].
  Proof.
    iIntros "Ha".
    rewrite /block_sim /denote_partial_block.

    iApply target_red_sim_expr'.
    simpl.
    target_simp.
    iApply target_red_base.

    iApply source_red_sim_expr'.
    simpl.
    source_simp.
    iApply source_red_base.

    iApply sim_expr'_base.
    done.
  Qed.

  (* Problem: we should be able to return if we have reached a branch.
     I guess we need a dedicated rule where we return with that.
     Problem: that will be an itree but not a Ret, whereas we would probably like to have a Ret here.

     Or we could require an itree expression there.
      But then the current rules don't really work.

     Either I interpret the whole thing, but then I can't go to the post with the next block to go to.
     - I could go with the whole expression, but then I don't know anymore which block I come from.
       So this will be hard to formulate.

     Or I intepret only the current block.
     - Then I can't really simulate multiple blocks, I guess.


     Can I get both at the same time, so that I have a choice:
      either we return current and next block, but then there's an implicit obligation to go to the next block
      or we go directly and resume execution.

     I guess then I need two postconditions in our simulation:
     - one we need to prove for bailing out. If we go to that one, we implicitly get the post plus the addditional obligation of starting from that block.
     - one we prove for proper return.


     Insight: the expr thing from Simuliris doesn't really work because we also need to know the previous block.
      maybe it's still useful for the low-level soundness proof of our higher-level mechanism?
      We have to show that we result in the same itree again, so that is strong enough.

  (**)*)
  Local Definition block_coind_pred (P : block_id → block_id → iProp Σ) (l_t l_s : block_id) κt κs (e_t : expr vir_lang (block_id * block_id + uvalue)) (e_s : expr vir_lang (block_id * block_id + uvalue)) : iProp Σ :=
    ∃ l_t'' l_s'',
      ⌜e_t = instr_conv $ denote_ocfg κt.(block_ocfg) (l_t'', l_t)⌝ ∗ ⌜e_s = instr_conv $ denote_ocfg κs.(block_ocfg) (l_s'', l_s)⌝ ∗ P l_t'' l_s''.

  Lemma block_coind κt κs l_t l_s b_t b_s P Φ :
    find_block κt.(block_ocfg) l_t = Some b_t →
    find_block κs.(block_ocfg) l_s = Some b_s →
    P κt.(block_src) κs.(block_src) -∗
    (□ ∀ l_t' l_s',
      let κt' := mk_block_context l_t l_t' κt.(block_ocfg) in
      let κs' := mk_block_context l_s l_s' κs.(block_ocfg) in
      P l_t' l_s' -∗
      SIM{κt'; κs'} (body_of_block b_t) ⪯ (body_of_block b_s) [{ λ e_t' e_s',
        Φ e_t' e_s' ∨
        block_coind_pred P l_t l_s κt κs e_t' e_s'
      }]) -∗
    SIM{κt; κs} t: TERM_Br_1 l_t ⪯ t: TERM_Br_1 l_s [{ Φ }].
  Proof.
    iIntros (Hlook_t Hlook_s) "HP #Hinv".
    rewrite /block_sim.
    iEval (rewrite /denote_partial_block).
    iApply target_red_sim_expr'.
    simpl.
    target_simp1_notau.
    iApply target_red_base.
    iApply source_red_sim_expr'.
    simpl.
    source_simp1_notau.
    iApply source_red_base.

    iApply (sim_expr_paco_tau (λ _, block_coind_pred P l_t l_s κt κs)).
    - iModIntro. iIntros (??) "Hx". eauto.
    - iModIntro. iIntros (? e_t e_s) "(%l_t' & %l_s' & -> & -> & Hp)".
      rewrite /join_expr.
      iPoseProof ("Hinv" with "Hp") as "Ha".
      rewrite /denote_ocfg.
      simpl.
      (*rewrite iter_unfold.*)
      rewrite !unfold_iter_ktree.
      rewrite Hlook_t Hlook_s.
      (* TODO: same tau problem as above *)
      admit.
    - iExists _, _. iSplitR; first done. iSplitR; first done. done.
  Admitted.


  (** Phi *)

  Definition phi_eval_expr_target (bfrom : block_id) (phis : list (local_id * phi dtyp)) (init : list (local_id * uvalue)) (Φ : list (local_id * uvalue) → iProp Σ) :=
    fold_right (λ '(id, Phi dt args) acc,
      λ ids,
        match Util.assoc bfrom args with
        | Some op =>
            target_red (<{ op @ Some dt }>e) (lift_unary_post (λ v,
              acc ((id, v) :: ids)))
        | None =>
            False%I
        end
    ) Φ phis init.
  Definition phi_eval_expr_source (bfrom : block_id) (phis : list (local_id * phi dtyp)) (init : list (local_id * uvalue)) (Φ : list (local_id * uvalue) → iProp Σ) :=
    fold_right (λ '(id, Phi dt args) acc,
      λ ids,
        match Util.assoc bfrom args with
        | Some op =>
            source_red (<{ op @ Some dt }>e) (lift_unary_post (λ v,
              acc ((id, v) :: ids)))
        | None =>
            False%I
        end
    ) Φ phis init.

  Lemma phi_eval_expr_target_elim' bfrom (phis : list _) init_phis Φ :
    phi_eval_expr_target bfrom phis init_phis Φ -∗
    target_red (instr_conv $ map_monad (m := itree _) (λ x : local_id * phi dtyp, translate exp_to_instr (denote_phi bfrom x)) phis) (lift_unary_post (λ dvs,
      Φ (reverse dvs ++ init_phis) ∗ ⌜phis.*1 = dvs.*1⌝)).
  Proof.
    iIntros "Ha".
    rewrite /phi_eval_expr_target.
    iInduction phis as [ | [id [dt args]] phis] "IH" forall (init_phis).
    { simpl. target_simp. iExists _. iSplitR; first done. iSplitL; done. }
    simpl.
    destruct (Util.assoc bfrom args) as [op | ]; last done.
    target_simp.
    iApply (target_red_wand with "Ha").
    iIntros (e_t')  "(%v_t & %Heq & Ha)".
    target_simp.
    target_simp.
    iPoseProof ("IH" with "Ha") as "Ha".
    iApply (target_red_wand with "Ha").
    iIntros (e_t2) "(%vs & %Heq2 & Ha & %Hx)".
    target_simp. target_simp.
    iExists _. iSplitR; first done.
    simpl. rewrite reverse_cons -app_assoc. iSplitL; first done.
    iPureIntro. f_equiv. done.
  Qed.
  Lemma phi_eval_expr_target_elim bfrom (phis : list _) Φ :
    phi_eval_expr_target bfrom phis [] Φ -∗
    target_red (instr_conv $ map_monad (m := itree _) (λ x : local_id * phi dtyp, translate exp_to_instr (denote_phi bfrom x)) phis) (lift_unary_post (λ dvs, Φ (reverse dvs) ∗ ⌜phis.*1 = dvs.*1⌝)).
  Proof.
    iIntros "Ha". iPoseProof (phi_eval_expr_target_elim' with "Ha") as "Ha".
    iApply (target_red_wand with "Ha").
    iIntros (?) "(% &  % & Ha)".
    rewrite app_nil_r. iExists _. eauto with iFrame.
  Qed.

  Lemma phi_store_target' i L dvs0 dvs Φ :
    NoDup (dvs0 ++ dvs).*1 →
    stack_tgt i -∗
    ldomain_tgt i (list_to_set dvs0.*1 ∪ L) -∗
    ([∗ list] x ∈ dvs0, [x.1 := x.2]t i) -∗
    ([∗ list] x ∈ dvs.*1, (∃ v, [x := v]t i) ∨ ⌜x ∉ L⌝) -∗
    (stack_tgt i -∗
     ldomain_tgt i (list_to_set (dvs0 ++ dvs).*1 ∪ L) -∗
     ([∗ list] x ∈ dvs0 ++ dvs, [x.1 := x.2]t i) -∗
     Φ tt
    ) -∗
    target_red (instr_conv $ (map_monad (m := itree _) (λ '(id, dv), trigger (LocalWrite id dv)) dvs)) (lift_unary_post (λ _, Φ tt)).
  Proof.
    iInduction dvs as [ | [id v] dvs] "IH" forall (dvs0).
    { iIntros (?) "Hs Hd Ha _ HP".
      simpl. target_simp. rewrite !app_nil_r.
      iExists _. iSplitR; first done.
      iApply ("HP" with "Hs Hd Ha"). }
    iIntros (Hnd) "Hs Hd Hx0 (Hh & Hx) Hp". simpl.
    target_simp.

    iDestruct "Hh" as "[(%v' & Hh) | %Hnel]".
    - (* TODO: get that the variable is part of the domain *)
      iApply (target_local_write with "Hh Hs").
      iIntros "Hh Hs". target_simp.
      iPoseProof ("IH" $! (app dvs0 [(id, v)]) with "[] Hs [Hd] [Hx0 Hh] Hx [Hp]") as "Ha".
      { rewrite -app_assoc. done. }
      { rewrite fmap_app. simpl. rewrite list_to_set_app_L.
        admit. }
      { rewrite big_sepL_app. iFrame. done. }
      { rewrite -app_assoc. done. }
      iApply (target_red_wand with "Ha").
      iIntros (?) "(% & %Heq & Ha)". target_simp. target_simp.
      iExists _. iSplitR; first done. done.
    - iApply (target_local_write_alloc with "Hd Hs").
      { admit. }
      iIntros "Hh Hd Hs". target_simp.
      iPoseProof ("IH" $! (app dvs0 [(id, v)]) with "[] Hs [Hd] [Hx0 Hh] Hx [Hp]") as "Ha".
      { rewrite -app_assoc//. }
      { rewrite fmap_app. simpl. rewrite list_to_set_app_L.
        simpl. rewrite right_id_L.
        iEval (rewrite -union_assoc_L union_comm_L).
        iEval (rewrite -union_assoc_L [L ∪ _]union_comm_L).
        done. }
      { rewrite big_sepL_app. iFrame. done. }
      { rewrite -app_assoc. done. }
      iApply (target_red_wand with "Ha").
      iIntros (?) "(% & %Heq & Ha)". target_simp. target_simp.
      iExists _. iSplitR; first done. done.
  Admitted.

  Lemma phi_store_target i L dvs Φ :
    NoDup (dvs).*1 →
    stack_tgt i -∗
    ldomain_tgt i L -∗
    ([∗ list] x ∈ dvs.*1, (∃ v, [x := v]t i) ∨ ⌜x ∉ L⌝) -∗
    (stack_tgt i -∗
     ldomain_tgt i (list_to_set dvs.*1  ∪ L) -∗
     ([∗ list] x ∈ dvs, [x.1 := x.2]t i) -∗
     Φ ()
    ) -∗
    target_red (instr_conv $ (map_monad (m := itree _) (λ '(id, dv), trigger (LocalWrite id dv)) dvs)) (lift_unary_post (λ _, Φ tt)).
  Proof.
    iIntros (?) "Hs Hd Ha Hp".
    iApply (phi_store_target' _ _ [] with "Hs [Hd] [] Ha [Hp]").
    { done. }
    { simpl. rewrite left_id_L. done. }
    { done. }
    { done. }
  Qed.

  (* TODO move *)
  Lemma big_sepL_reverse {A} (l : list A) (Φ : A → iProp Σ) :
    ([∗ list] x ∈ l, Φ x)%I ⊣⊢ ([∗ list] x ∈ reverse l, Φ x)%I.
  Proof.
    iInduction l as [ | x l] "IH"; simpl; first done.
    rewrite reverse_cons big_sepL_app big_sepL_singleton.
    iSplit.
    - iIntros "($ & Hb)". by iApply "IH".
    - iIntros "(Ha & $)". by iApply "IH".
  Qed.

  Lemma sim_phi_target phi_t s_t t_t b_s κt κs Φ :
    NoDup phi_t.*1 →
    phi_eval_expr_target κt.(block_from) phi_t [] (λ phis,
      ∃ i L, stack_tgt i ∗
      ldomain_tgt i L ∗
      ([∗ list] x ∈ phis.*1, (∃ v, [x := v]t i) ∨ ⌜x ∉ L⌝) ∗
      (stack_tgt i -∗
       ldomain_tgt i (list_to_set phis.*1 ∪ L) -∗
      ([∗ list] x ∈ phis, [x.1 := x.2]t i) -∗
      SIM{κt; κs} s: s_t t: t_t ⪯ b_s [{ Φ }])) -∗
    SIM{κt; κs} p: phi_t s: s_t t: t_t ⪯ b_s [{ Φ }].
  Proof.
    iIntros (Hnd) "Ha".
    iPoseProof (phi_eval_expr_target_elim with "Ha") as "Ha".
    rewrite /block_sim.
    iEval (rewrite {1}/denote_partial_block).
    iApply target_red_sim_expr'.
    target_simp.
    iApply (target_red_wand with "Ha").
    iIntros (?) "(% & %Heq & Ha & %Hphis)".
    iDestruct "Ha" as "(%i & %L & Hs & Hd & Hl & Ha)".
    target_simp. target_simp.
    iPoseProof (phi_store_target _ _ v (λ _, instr_conv (denote_partial_block (s: s_t t: t_t) κt) ⪯ instr_conv (denote_partial_block b_s κs) ⦉ Φ ⦊)%I with "Hs Hd [Hl] [Ha]") as "Hb".
    { admit. }
    { rewrite fmap_reverse. rewrite -big_sepL_reverse//. }
    { iIntros "Hs Hl Hd".
      admit. }
    iApply (target_red_wand with "Hb").
    iIntros (?) "(% & % & Ha)".
    target_simp. target_simp.
    iApply target_red_base.
    target_simp.
    iApply target_red_eq_itree.
    { rewrite instr_conv_ret. reflexivity. }
    target_simp1.
    iApply target_red_base.
    rewrite {1}/denote_partial_block.
    simpl.
  Admitted.

  Lemma sim_phi_source phi_s s_s t_s b_t κt κs Φ :
    NoDup phi_s.*1 →
    phi_eval_expr_source κs.(block_from) phi_s [] (λ phis,
      ∃ i L, stack_src i ∗
      ldomain_src i L ∗
      ([∗ list] x ∈ phis.*1, (∃ v, [x := v]s i) ∨ ⌜x ∉ L⌝) ∗
      (stack_src i -∗
       ldomain_src i (list_to_set phis.*1 ∪ L) -∗
      ([∗ list] x ∈ phis, [x.1 := x.2]s i) -∗
      SIM{κt; κs} b_t ⪯ s: s_s t: t_s [{ Φ }])) -∗
    SIM{κt; κs} b_t ⪯ p: phi_s s: s_s t: t_s [{ Φ }].
  Proof.
  Admitted.
End block_laws.

Section function.
  Context `{!vellirisGS Σ}.

  (* Resources for the current frame *)
  Definition in_frame_tgt (i : list frame_names) (allocas : gset Z) (locals : list local_id) : iProp Σ :=
    stack_tgt i ∗ frame_tgt i locals ∗ alloca_tgt i allocas.
  Definition in_frame_src (i : list frame_names) (allocas : gset Z) (locals : list local_id) : iProp Σ :=
    (* should we use ldomain instead of frame? *)
    stack_src i ∗ frame_src i locals ∗ alloca_src i allocas.

  (** Function simulation *)
  Definition function_sim (f_t f_s : cfg dtyp) (Φ : expr vir_lang uvalue → expr vir_lang uvalue → iProp Σ) : iProp Σ :=
    ∀ (i_t i_s : list frame_names) (vs_t vs_s : list uvalue),
    (* precondition *)
    in_frame_tgt i_t ∅ f_t.(args) -∗
    in_frame_src i_s ∅ f_s.(args) -∗
    ([∗ list] x; v ∈ f_t.(args); vs_t, [ x := v ]t i_t) -∗
    ([∗ list] x; v ∈ f_s.(args); vs_s, [ x := v ]s i_s) -∗
    ([∗ list] v_t; v_s ∈ vs_t; vs_s, uval_rel v_t v_s) -∗
    checkout ∅ -∗
    (* postcondition *)
    (∀ r_t r_s V_t V_s,
      in_frame_tgt i_t ∅ V_t -∗
      in_frame_src i_s ∅ V_s -∗
      ([∗ list] x ∈ V_t, ∃ v, [ x := v ]t i_t) -∗
      ([∗ list] x ∈ V_s, ∃ v, [ x := v ]s i_s) -∗
      uval_rel r_t r_s -∗
      checkout ∅ -∗
      Φ (Ret r_t) (Ret r_s)
    ) -∗
    block_context_sim (mk_block_context f_t.(init) f_t.(init) f_t.(blks)) (mk_block_context f_s.(init) f_s.(init) f_s.(blks))
      (λ a b, ∃ r_t r_s : uvalue, ⌜a = Ret (inr r_t)⌝ ∧ ⌜b = Ret (inr r_s)⌝ ∧ Φ (Ret r_t) (Ret r_s)).

  (* An alternative definition in terms of the function denotation *)
  Definition function_sim' (f_t f_s : definition dtyp (cfg dtyp)) (Φ : expr vir_lang uvalue → expr vir_lang uvalue → iProp Σ) : iProp Σ :=
    ∀ vs_t vs_s,
      L0'expr_conv (denote_function f_t vs_t) ⪯ L0'expr_conv (denote_function f_s vs_s) [{ Φ }].

  Lemma function_sim_impl f_t f_s Φ :
    (* TODO: Probably needs some resources for the frame *)
    function_sim f_t.(df_instrs) f_s.(df_instrs) Φ -∗
    function_sim' f_t f_s Φ.
  Proof.
  Abort.

End function.
