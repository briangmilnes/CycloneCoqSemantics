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
Require Export NatLemmas.

Set Implicit Arguments.

Module Type VariablesSig.
  Inductive Var : Set :=
  | var   : nat -> Var.

 Axiom beq_var : Var -> Var -> bool.
 Hint Resolve beq_var.
End VariablesSig.
