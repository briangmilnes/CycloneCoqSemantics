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
Require Import VariableModule2.

Set Implicit Arguments.
Set Printing Universes.

Module Type TypingInfoSig.
  Parameter T : Type.
  Axiom beq_t : T -> T -> bool.
  Hint Resolve beq_t.
End TypingInfoSig.
