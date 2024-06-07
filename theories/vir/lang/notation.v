From iris.prelude Require Import options.

From velliris.vir.lang Require Export vir.
From velliris.vir.util Require Export vir_util.

Declare Custom Entry vir.

Notation "<{ e }>" :=
  (instr_conv (denote_instr e))
      (e custom vir at level 99).
Notation "x" := x (in custom vir at level 0, x constr at level 0).
Notation "% id '=' e" := (id, e)
    (in custom vir at level 50,
        format "% id  =  e").
Notation "'alloca' dt" :=
  (INSTR_Alloca dt _ _)
    (in custom vir at level 0, dt constr at level 0).
Notation "'load' dt , du * % ptr" :=
  (INSTR_Load _ dt (du,ptr) _)
    (in custom vir at level 0,
        dt constr at level 0,
        du constr at level 0,
        ptr constr at level 0,
    format "load  dt ,  du *  % ptr").
Notation "'store' dt val , du * % ptr" :=
  (INSTR_Store _ (dt, val) (du, ptr) _)
    (in custom vir at level 0,
        dt constr at level 0,
        val constr at level 0,
        du constr at level 0,
        ptr constr at level 0,
    format "store  dt  val ,  du *  % ptr").
Notation "<{{ e ( args ) }}> " :=
  (L0'expr_conv (denote_function e args))
      (e custom vir at level 99, args custom vir at level 99).

Notation "x1 :== x2   ;;; k " :=
  (ITree.bind (instr_conv (denote_instr (pair x1 x2))) (fun _ => (k)))
    (at level 30, x2 custom vir, k custom vir,
      right associativity).
Notation "'i32'" := (DynamicTypes.DTYPE_I 32) (at level 30).
Notation "' id '" := (EXP_Ident (ID_Local id)) (at level 30).
Notation "% id " := (IId (Raw id))  (at level 30).


(* Change code context into instr-notation compatible proof environment *)
Ltac instr_conv_normalize :=
  repeat match goal with
    | |- context[instr_conv (ITree.bind (denote_instr ?x) _)] =>
        let Hx := fresh "Hx" in
          epose proof (instr_conv_bind (denote_instr x)) as Hx;
          setoid_rewrite Hx; clear Hx
  end.

Ltac to_instr :=
  repeat setoid_rewrite denote_code_cons;
  instr_conv_normalize;
  setoid_rewrite instr_conv_nil.

Ltac cont :=
  let Hret1 := fresh "Hret1" in
  let Hret2 := fresh "Hret2" in
  iIntros (??) "H";
  iDestruct "H" as (?? Hret1 Hret2) "H";
    rewrite Hret1 Hret2 !bind_ret_l; clear Hret1 Hret2.

Ltac unary_post :=
  rewrite /lift_unary_post; iExists _; iSplitL ""; first done.
