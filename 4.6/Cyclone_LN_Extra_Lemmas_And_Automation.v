(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Defining type safety, page 67.

*)

Set Implicit Arguments.
Set Implicit Arguments.
Require Export Cyclone_Formal_Syntax Cyclone_Static_Semantics_Kinding_And_Context_Well_Formedness.
Require Export Cyclone_Static_Semantics_Typing_Heap_Objects.
Require Export Cyclone_LN_Tactics.
Close Scope list_scope.
Import LibEnvNotations.
Import LVPE.LibVarPathEnvNotations.

Hint Extern 1 (ok empty) => trace_goal; apply ok_empty.
Hint Extern 1 (ok empty) => trace_goal; apply ok_empty.
Hint Extern 1 (ok empty) => trace_goal; apply ok_empty.
Hint Extern 1 (ok nil) =>   trace_goal;  rewrite <- empty_def; apply ok_empty.
Hint Extern 1 (LVPE.okp LVPE.V.empty) => trace_goal; apply LVPE.okp_empty.
Hint Extern 1 (LVPE.okp nil) => trace_goal; rewrite <- empty_def; apply LVPE.okp_empty.

Lemma WFD_iff_ok:
  forall d,  WFD d <-> ok d.
Proof.
  intros.
  split.
  introv WFDd.
  lets: ok_push.
  lets: get_none_inv.
  induction* WFDd.
  introv OKd.
  induction* OKd.
Qed.

Lemma WFU_okp:
  forall u,  WFU u -> LVPE.okp u.
Proof.
  lets: LVPE.okp_push.
  lets: LVPE.get_none_inv.
  introv WFUu.
  induction* WFUu.
Qed.

Lemma extends_get:
  forall A alpha (d : env A) v,
    get alpha d = Some v ->
    forall d', 
      extends d d' ->
      get alpha d' = Some v.
Proof.
  intros.
  unfold extends in H0.
  specialize (H0 alpha v).
  induction H0.
  reflexivity.
  assumption.
Qed.
Ltac extends_get :=
  match goal with
  | H: get ?alpha ?d0 = Some ?v,
    I: extends ?d0 ?d'
 |- get ?alpha ?d' = Some ?v =>
   apply extends_get with (d:=d0); assumption
end.                  
Hint Extern 1 (get _ _  = Some _) => extends_get.

Lemma extends_empty:
  forall A (E : env A),
    extends E empty ->
    E = empty.
Proof.
  intros.
  induction E.
  rewrite* empty_def.
  unfold extends, binds in H.
  destruct a.
  specialize (H v a).
  rewrite get_def in H.
  rewrite empty_def in H.
  compute in H.
  case_var.
  assert (Some a = Some a); auto.
  apply H in H0.
  inversion H0.
Qed.

Lemma empty_extends:
  forall A (E : env A),
    extends empty E.
Proof.
  intros.
  induction E.
  rewrite* empty_def.
  unfold extends, binds.
  intros.
  inversion H.
  rewrite get_empty in H1.
  inversion H1.
Qed.

Hint Extern 1 (extends empty _) => (* idtac "(extends empty _)";*) trace_goal; apply empty_extends.
Hint Extern 1 (extends empty _) => (* idtac "(extends empty _)";*) trace_goal; apply empty_extends.
Hint Extern 1 (LVPE.extends LVPE.V.empty _) => (* idtac "(LVPE.extends LVPE.V.empty _)";*) trace_goal; apply empty_extends.
Hint Extern 1 (extends empty _) => (* idtac "(extends empty _)";*) trace_goal; apply empty_extends.

Lemma extends_push_both:
  forall A (E1 E2 : env A),
    extends E1 E2 ->
    forall x, 
    x # E2 ->
     forall v, 
       extends (E1 & x ~ v) (E2 & x ~ v).
Proof.
  introv E.
  intros.
  unfold extends, binds in *.
  intros.
  rewrite get_push in H0.
  case_var*.
Qed.
Hint Extern 1 (extends (_ & _ ~ _) (_ & _ ~ _)) => (* idtac "trying extendspb";*)apply* extends_push_both.

Lemma lvpe_extends_get:
  forall A (E E' : LVPE.varpathenv A),
    LVPE.extends E E' ->
    forall x v,
      LVPE.V.get x E  = Some v ->
      LVPE.V.get x E' = Some v.
Proof.
  intros.
  unfold LVPE.extends, LVPE.binds in H.
  induction E'; auto.
Qed.
Ltac lvpe_extends_get :=
  match goal with
  | H: LVPE.V.get ?alpha ?d0 = Some ?v,
    I: LVPE.extends ?d0 ?d'
 |- LVPE.V.get ?alpha ?d' = Some ?v =>
   apply lvpe_extends_get with (d:=d0); assumption
end.                  
Hint Extern 1 (LVPE.V.get _ _  = Some _) => lvpe_extends_get.


Ltac solve_get_extends :=
  match goal with
    | H: extends ?u ?u', I: get ?x ?u  = Some ?v |- get ?x ?u' = Some ?v =>
      try apply extends_get with (E:= u); auto
    | H: LVPE.extends ?u ?u',  I: LVPE.V.get ?x ?u = Some ?v |- LVPE.V.get ?x ?u' = Some ?v =>
      try apply lvpe_extends_get with (E:= u); auto
  end.

Hint Extern 1 (get _ _ _) => (* idtac "(get _ _ _)";*) trace_goal; try solve_get_extends.
Hint Extern 1 (LVPE.V.get _ _ _) => (* idtac "(LVPE.V.get _ _ _)";*) trace_goal; try solve_get_extends.