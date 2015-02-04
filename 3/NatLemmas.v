(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  A couple of missing Nat lemmas.

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.
Require Import Coq.Init.Logic.

Require Export CpdtTactics.
Require Export Case.
Require Export TacticNotations.

(* Why are these not in the standard library ? *)
Lemma beq_nat_sym : forall (n m : nat),
                      beq_nat n m = beq_nat m n.
Proof.
  apply NPeano.Nat.eqb_sym.
Qed.

Lemma beq_nat_trans : 
  forall n1 n2 n3, 
    beq_nat n1 n2 = true ->
    beq_nat n2 n3 = true -> 
    beq_nat n1 n3 = true.
Proof.
  induction n1; destruct n2;
  induction n3; simpl; auto. intros. inversion H.
  apply IHn1.
Qed.

