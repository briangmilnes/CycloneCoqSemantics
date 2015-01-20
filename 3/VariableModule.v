(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  An attempt at a variable module in a context. 

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.
Require Import Coq.Init.Logic.

Require Export CpdtTactics.
Require Export Case.
Require Export TacticNotations.

Set Implicit Arguments.

Module Type Nonce.
End Nonce.

Module TVarNonce : Nonce.
End TVarNonce.

Module EVarNonce : Nonce.
End EVarNonce.

Module Type VariablesSig.
 Parameter V : Type.
 Parameter beq_v : V -> V -> bool.
 Axiom beq_v_refl:   forall a,   beq_v a a = true.
 Axiom beq_v_eq:  forall a b, beq_v a b = true -> a = b.
 Axiom beq_v_neq: forall a b, beq_v a b = false -> a <> b.
End VariablesSig.
Print VariablesSig.

Module VariablesFun(B : Nonce)  <: VariablesSig.
 Inductive V' : Type := var : nat -> V'. 
 Function beq_v (x y : V') : bool :=
   match x, y with
     | (var x'), (var y') => beq_nat x' y'
  end.
 Definition V := V'.

Lemma beq_v_refl:
 forall (alpha : V),
   beq_v alpha alpha = true.
Proof.
  intros.
  destruct alpha.
  unfold beq_v.
  apply eq_sym.
  apply beq_nat_refl.
Qed.

Lemma beq_v_eq:
  forall (alpha beta : V),
    beq_v alpha beta = true ->
    alpha = beta.
Proof.
  intros.
  case_eq (beq_v alpha beta).
  intros.
  destruct alpha; destruct beta.
  unfold beq_v in H.
  unfold beq_v in H0.
  symmetry in H.
  apply beq_nat_eq in H.
  rewrite H.
  reflexivity.
  intros.
  rewrite H in H0.
  inversion H0.
Qed.

Lemma beq_v_neq:
  forall (alpha beta : V),
    beq_v alpha beta = false ->
    alpha <> beta.
Proof.
  intros.
  case_eq (beq_v alpha beta).
  intros.
  destruct alpha; destruct beta.
  unfold beq_v in H.
  unfold beq_v in H0.
  apply beq_nat_false in H.
  congruence.
  intros.
  destruct alpha; destruct beta.  
  unfold beq_v in H.
  fold beq_v in H.
  apply beq_nat_false in H.
  congruence.
Qed.  

End VariablesFun.
Print VariablesFun.

(* LOL no empty functor arguments, no parameters, means they're the same type! *)
Module TVar := VariablesFun(TVarNonce).
Module EVar := VariablesFun(EVarNonce).

Check TVar.var(0).
Check EVar.var(0).
Check TVar.var(0) : TVar.V'.
Check EVar.var(0) : EVar.V'.
(* Check EVar.var(0) : TVar.V'. Should fail. *)

Import TVar.
Lemma beq_tvar_reflexive:
 forall (v : TVar.V),
   TVar.beq_v v v = true.
Proof.
  intros.
  apply TVar.beq_v_refl.
Qed.