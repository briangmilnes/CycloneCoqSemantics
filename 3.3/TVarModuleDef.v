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
Require Export NonceSigDef.
Require Export VariablesFunDef.

Set Implicit Arguments.

Module TVarNonce : NonceSig.
End TVarNonce.
Module TVarModule := VariablesFun(TVarNonce).
