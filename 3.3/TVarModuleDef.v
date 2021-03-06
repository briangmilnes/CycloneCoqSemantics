(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Combine the definition of variables and its proofs.

*)
Set Implicit Arguments.
Require Export NonceSigDef.
Require Export VariablesFunDef.

Module TVarNonce : NonceSig.
End TVarNonce.
Module TVarModule := VariablesFun(TVarNonce).
