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

Hint Extern 1 (ok ddot) => unfold ddot.
Hint Extern 1 (ok gdot) => unfold gdot.
Hint Extern 1 (LVPE.okp udot) => unfold udot.
Hint Extern 1 (ok hdot) => unfold hdot.

Lemma WFD_ok:
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
  constructor*.
  apply* get_none.
Qed.

Lemma WFU_okp:
  forall u,  WFU u -> LVPE.okp u.
Proof.
  introv WFUu.
  lets: LVPE.okp_push.
  lets: LVPE.get_none_inv.
  induction* WFUu.
Qed.

(* not needed
Lemma binds_ok_free:
  forall A alpha v (d d' : env A),
    binds alpha v d ->
    ok d  ->
    ok d' ->
    ok (d & d') ->
    alpha # d'.
Admitted.

Lemma binds_ok_binds:
  forall A alpha v (d d' : env A),
    binds alpha v d ->
    ok d  ->
    ok d' ->
    ok (d & d') ->
    binds alpha v (d & d').
Proof.
  unfold binds in *.
  intros.
  rewrite get_concat.
  assert(get alpha d' = None).
  induction d'.
  rewrite <- empty_def.
  apply get_empty.
  inversion H2.
  rewrite empty_def in H4.
  admit. (* Should be able to invert. *)
  admit.
  rewrite H3.
  assumption.
Qed.

Hint Extern 3 (binds _ _ (_ & _)) => try apply binds_ok_binds.
*)

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
  unfold binds.
  assumption.
Qed.

Lemma extends_empty:
  forall A (E : env A),
    extends E empty ->
    E = empty.
Proof.
  intros.
  induction E.
  rewrite* empty_def.
  unfold extends in H.
  destruct a.
  specialize (H v a).
  unfold binds in H.
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
  unfold extends.
  intros.
  inversion H.
  rewrite get_empty in H1.
  inversion H1.
Qed.

Hint Extern 1 (extends ddot _) => unfold ddot; apply empty_extends.
Hint Extern 1 (extends gdot _) => unfold gdot; apply empty_extends.
Hint Extern 1 (LVPE.extends udot _) => unfold udot; apply empty_extends.
Hint Extern 1 (extends hdot _) => unfold hdot; apply empty_extends.

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
  unfold extends.
  intros.
  unfold binds in H0.
  rewrite get_push in H0.
  case_var*.
  inversion H0.
  subst.
  unfold binds.
  rewrite get_push.
  case_var*.
Qed.

Lemma extends_binds:
  forall A (E E' : env A),
    extends E E' ->
    forall x v,
      binds x v E ->
      binds x v E'.
Proof.
  intros.
  induction E'; auto.
Qed.

Lemma lvpe_extends_binds:
  forall A (E E' : LVPE.varpathenv A),
    LVPE.extends E E' ->
    forall x v,
      LVPE.binds x v E ->
      LVPE.binds x v E'.
Proof.
  intros.
  induction E'; auto.
Qed.

Ltac solve_binds_extends :=
  match goal with
    | H: extends ?u ?u', I: binds ?x ?v ?u |- binds ?x ?v ?u' =>
      try apply extends_binds with (E:= u); auto
    | H: LVPE.extends ?u ?u',  I: LVPE.binds ?x ?v ?u |- LVPE.binds ?x ?v ?u' =>
      try apply lvpe_extends_binds with (E:= u); auto
  end.

Hint Extern 1 (binds _ _ _) => try solve_binds_extends.
Hint Extern 1 (LVPE.binds _ _ _) => try solve_binds_extends.