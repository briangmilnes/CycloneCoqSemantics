(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Program or expression variables.

*)

Set Implicit Arguments.
Require Export VariablesFunDef.
Require Export NonceSigDef.

Module EVarNonce : NonceSig.
End EVarNonce.
Module EVarModule := VariablesFun(EVarNonce).

