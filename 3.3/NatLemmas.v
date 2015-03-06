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

(* Why are these not in the standard library ? *)
Lemma beq_nat_sym : forall (n m : nat),
                      beq_nat n m = beq_nat m n.
Proof.
  apply NPeano.Nat.eqb_sym.
Qed.
Hint Rewrite beq_nat_sym.

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
Hint Resolve beq_nat_trans.

Lemma Zeq_bool_refl:
  forall i, Zeq_bool i i = true.
Admitted.
Hint Resolve Zeq_bool_refl.

Lemma Zeq_bool_sym:
  forall i i', Zeq_bool i i' = Zeq_bool i' i.
Admitted.
Hint Resolve Zeq_bool_sym.

Lemma Zeq_bool_trans:
  forall i i0 i1,  
    Zeq_bool i i0 = true ->
    Zeq_bool i0 i1 = true ->
    Zeq_bool i i1 = true.
Admitted.
Hint Resolve Zeq_bool_trans.

Lemma Zeq_bool_eq:
  forall i i', Zeq_bool i i' = true -> i = i'.
Admitted.
Hint Resolve Zeq_bool_eq.

Lemma Zeq_bool_neq:
  forall i i', Zeq_bool i i' = false -> i <> i'.
Admitted.
Hint Resolve Zeq_bool_neq.