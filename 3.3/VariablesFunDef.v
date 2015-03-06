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
Require Import Coq.Structures.Equalities.

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

 Definition t := Var.

 Function eqb (x y : Var) : bool :=
   match x, y with
     | (var x'), (var y') => beq_nat x' y'
  end.
 Hint Resolve eqb.

 Fixpoint eq (a b : t) : Prop :=
    match eqb a b with
     | false => False
     | true => True
    end.

Lemma eqb_refl:
 forall (a : Var),
   eqb a a = true.
Proof.
  intros.
  destruct a.
  unfold eqb.
  apply eq_sym.
  apply beq_nat_refl.
Qed.
Hint Resolve eqb_refl.

Lemma eq_refl:
 forall (a : t),
   eq a a.
Proof.
  destruct a; unfold eq; unfold eqb.
  rewrite <- beq_nat_refl.
  trivial.
Qed.

Lemma eqb_sym : forall x y : Var, eqb x y = eqb y x.
Proof.
  intros.
  destruct x.
  destruct y.
  unfold eqb.
  rewrite beq_nat_sym.
  reflexivity.
Qed.
Hint Immediate eqb_sym.

Lemma eq_sym : forall x y : t, eq x y -> eq y x.
Proof.
  intros.
  destruct x.
  destruct y.
  unfold eq in *.
  unfold eqb in *.
  rewrite beq_nat_sym.
  assumption.
Qed.

Lemma eqb_trans : 
  forall x y z,
    eqb x y = true -> eqb y z = true -> eqb x z = true.
Proof.
   destruct x.
   destruct y.
   destruct z.
   apply beq_nat_trans.
Qed.
Hint Resolve eqb_trans.

Lemma eq_trans : 
  forall x y z,
    eq x y -> eq y z -> eq x z.
Proof.
Admitted.

Lemma eqb_to_eq:
  forall (alpha beta : t),
    eqb alpha beta = true ->
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
Hint Resolve eqb_to_eq.

Lemma eqb_to_neq:
  forall (alpha beta : Var),
    eqb alpha beta = false ->
    alpha <> beta.
Proof.
  intros.
  case_eq (eqb alpha beta).
  intros.
  destruct alpha; destruct beta.
  unfold eqb in H.
  unfold eqb in H0.
  apply beq_nat_false in H.
  congruence.
  intros.
  destruct alpha; destruct beta.  
  unfold eqb in H.
  fold eqb in H.
  apply beq_nat_false in H.
  congruence.
Qed.  
Hint Resolve eqb_to_neq.

Lemma eqb_iff_eq:    forall a b, eqb a b = true <-> a = b.
Proof.
  destruct a; destruct b; crush.
  rewrite beq_nat_refl with (n:= n0).
  reflexivity.
Qed.
Hint Resolve eqb_iff_eq.

Lemma eqb_iff_neq:   forall a b, eqb a b = false <-> a <> b.
Proof.
  destruct a; destruct b.
  unfold eqb.
  rewrite beq_nat_false_iff.
  crush.
Qed.
Hint Resolve eqb_iff_neq.

Lemma eqb_eq : forall x y : t, eqb x y = true <-> eq x y.
Proof.
  destruct x; destruct y; case_eq (beq_nat n n0); intros.
  symmetry in H.
  apply beq_nat_eq in H.
  subst.
  crush.
  rewrite beq_nat_refl with (n:= n0).
  reflexivity.
  simpl.
  rewrite H.
  crush.
Qed.

Instance eq_equiv : Equivalence eq.
Proof. 
  split.
  exact eq_refl.
  exact eq_sym.
  exact eq_trans.
Defined.

Lemma eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
Proof.   
  intros.
  destruct x; destruct y;  unfold eq; unfold eqb; destruct(beq_nat n n0); crush.
Qed.

End VariablesFun.
