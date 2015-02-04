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
Require Export VariablesSigDef.

Module Variables <: VariablesSig.
 Inductive Var : Type :=
  | var   : nat -> Var.

 Function beq_var (x y : Var) : bool :=
   match x, y with
     | (var x'), (var y') => beq_nat x' y'
  end.
 Hint Resolve beq_var.
End Variables.

