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

Add LoadPath "/home/milnes/Desktop/Research/Cyclone/CycloneCoq/3".
Require Export VariablesFunDef.
Require Export NonceSigDef.

Set Implicit Arguments.

Module EVarNonce : NonceSig.
End EVarNonce.
Module EVarModule := VariablesFun(EVarNonce).

