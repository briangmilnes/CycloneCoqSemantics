(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  An attempt at a context module.

*)

Require Import List.
Export ListNotations.
Require Export ZArith.
Require Import Init.Datatypes.
Require Export Coq.Bool.Bool.

Require Import DynamicSemanticsTypeSubstitution.
Require Export CpdtTactics.
Require Export Case.
Require Import FormalSyntax.

Require Import VariableModule2.
Require Import TypingInfoModule2.

Set Implicit Arguments.



Module Delta := ContextFun EVar TVar.
Print Delta.
