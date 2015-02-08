(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Combine the definition of variables and its proofs.

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.
Require Import Coq.Init.Logic.

Require Export CpdtTactics.
Require Export Case.
Require Export NatLemmas.
Require Export NonceSigDef.
Require Export VariablesSigDef.

Set Implicit Arguments.

Module VariablesFun(n : NonceSig) <: VariablesSig.
 Include n.

 Inductive Var : Type :=
  | var   : nat -> Var.

 Function beq_t (x y : Var) : bool :=
   match x, y with
     | (var x'), (var y') => beq_nat x' y'
  end.
 Hint Resolve beq_t.

Lemma beq_t_refl:
 forall (a : Var),
   beq_t a a = true.
Proof.
  intros.
  destruct a.
  unfold beq_t.
  apply eq_sym.
  apply beq_nat_refl.
Qed.
Hint Resolve beq_t_refl.

Lemma beq_t_sym : forall x y : Var, beq_t x y = beq_t y x.
Proof.
  intros.
  destruct x.
  destruct y.
  unfold beq_t.
  rewrite beq_nat_sym.
  reflexivity.
Qed.
Hint Immediate beq_t_sym.

Lemma beq_t_trans : 
  forall x y z,
    beq_t x y = true -> beq_t y z = true -> beq_t x z = true.
Proof.
   destruct x.
   destruct y.
   destruct z.
   apply beq_nat_trans.
Qed.
Hint Resolve beq_t_trans.

Lemma beq_t_eq:
  forall (alpha beta : Var),
    beq_t alpha beta = true ->
    alpha = beta.
Proof.
  destruct alpha. 
  destruct beta.
  simpl.
  intros.
  symmetry in H.
  apply beq_nat_eq in H.
  rewrite H.
  reflexivity.
Qed.
Hint Resolve beq_t_eq.

Lemma beq_t_neq:
  forall (alpha beta : Var),
    beq_t alpha beta = false ->
    alpha <> beta.
Proof.
  intros.
  case_eq (beq_t alpha beta).
  intros.
  destruct alpha; destruct beta.
  unfold beq_t in H.
  unfold beq_t in H0.
  apply beq_nat_false in H.
  congruence.
  intros.
  destruct alpha; destruct beta.  
  unfold beq_t in H.
  fold beq_t in H.
  apply beq_nat_false in H.
  congruence.
Qed.  
Hint Resolve beq_t_neq.

Lemma beq_t_iff_eq:    forall a b, beq_t a b = true <-> a = b.
Proof.
  destruct a; destruct b; crush.
  rewrite beq_nat_refl with (n:= n0).
  reflexivity.
Qed.
Hint Resolve beq_t_iff_eq.

Lemma beq_t_iff_neq:   forall a b, beq_t a b = false <-> a <> b.
Proof.
  destruct a; destruct b.
  unfold beq_t.
  rewrite beq_nat_false_iff.
  crush.
Qed.
Hint Resolve beq_t_iff_neq.

 Definition T := Var.
End VariablesFun.
