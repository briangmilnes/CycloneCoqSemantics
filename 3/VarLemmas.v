(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Some useful lemmas about Vars.

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.

Require Export CpdtTactics.
Require Export Case.
Require Export FormalSyntax.

Lemma beq_tvar_symmetric:
  forall (alpha beta : TVar),
    beq_tvar alpha beta = beq_tvar beta alpha.
Proof.
  intros alpha beta.
  case_eq (beq_tvar alpha beta); case_eq (beq_tvar beta alpha); intros; try reflexivity; destruct alpha; destruct beta; unfold beq_tvar in H; unfold beq_tvar in H0.
  symmetry in H0.
  apply beq_nat_eq in H0.
  apply beq_nat_false in H.
  congruence.
  symmetry in H.
  apply beq_nat_eq in H.
  apply beq_nat_false in H0.
  congruence.
Qed.

Lemma beq_tvar_eq:
  forall (alpha beta : TVar),
    beq_tvar alpha beta = true ->
    alpha = beta.
Proof.
  intros.
  case_eq (beq_tvar alpha beta).
  intros.
  destruct alpha; destruct beta.
  unfold beq_tvar in H.
  unfold beq_tvar in H0.
  symmetry in H.
  apply beq_nat_eq in H.
  rewrite H.
  reflexivity.
  intros.
  rewrite H in H0.
  inversion H0.
Qed.

Lemma beq_tvar_neq:
  forall (alpha beta : TVar),
    beq_tvar alpha beta = false ->
    alpha <> beta.
Proof.
  intros.
  case_eq (beq_tvar alpha beta).
  intros.
  destruct alpha; destruct beta.
  unfold beq_tvar in H.
  unfold beq_tvar in H0.
  apply beq_nat_false in H.
  congruence.
  intros.
  destruct alpha; destruct beta.  
  unfold beq_tvar in H.
  fold beq_tvar in H.
  apply beq_nat_false in H.
  congruence.
Qed.  