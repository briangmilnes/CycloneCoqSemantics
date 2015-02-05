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

 Function beq_var (x y : Var) : bool :=
   match x, y with
     | (var x'), (var y') => beq_nat x' y'
  end.
 Hint Resolve beq_var.

Lemma beq_var_refl:
 forall (a : Var),
   beq_var a a = true.
Proof.
  intros.
  destruct a.
  unfold beq_var.
  apply eq_sym.
  apply beq_nat_refl.
Qed.
Hint Resolve beq_var_refl.

Lemma beq_var_sym : forall x y : Var, beq_var x y = beq_var y x.
Proof.
  intros.
  destruct x.
  destruct y.
  unfold beq_var.
  rewrite beq_nat_sym.
  reflexivity.
Qed.
Hint Immediate beq_var_sym.

Lemma beq_var_trans : 
  forall x y z,
    beq_var x y = true -> beq_var y z = true -> beq_var x z = true.
Proof.
   destruct x.
   destruct y.
   destruct z.
   apply beq_nat_trans.
Qed.
Hint Resolve beq_var_trans.

Lemma beq_var_eq:
  forall (alpha beta : Var),
    beq_var alpha beta = true ->
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
Hint Resolve beq_var_eq.

Lemma beq_var_neq:
  forall (alpha beta : Var),
    beq_var alpha beta = false ->
    alpha <> beta.
Proof.
  intros.
  case_eq (beq_var alpha beta).
  intros.
  destruct alpha; destruct beta.
  unfold beq_var in H.
  unfold beq_var in H0.
  apply beq_nat_false in H.
  congruence.
  intros.
  destruct alpha; destruct beta.  
  unfold beq_var in H.
  fold beq_var in H.
  apply beq_nat_false in H.
  congruence.
Qed.  
Hint Resolve beq_var_neq.

 Definition T := Var.
 Definition beq_t := beq_var.
 Definition beq_t_refl := beq_var_refl.
 Definition beq_t_sym := beq_var_sym.
 Definition beq_t_trans := beq_var_trans.

 Definition beq_t_eq := beq_var_eq.
 Definition beq_t_neq := beq_var_neq.

End VariablesFun.
