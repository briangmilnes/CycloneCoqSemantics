(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Program or expression variables.

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.
Require Import Coq.Init.Logic.

Require Export VariablesFunDef.
Require Export NonceSigDef.

Set Implicit Arguments.

Module EVarNonce : NonceSig.
End EVarNonce.
Module EVarModule := VariablesFun(EVarNonce).

