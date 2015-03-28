(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Combine the definition of variables and its proofs.

*)
Set Implicit Arguments.
Require Export VariableEqualityFunDef.
Require Export VariableEqualitySetFunDef.
Require Export NonceDef.

Module EVarNonce : Nonce.
End EVarNonce.

Module EVarModule := VariableEqualityFun(EVarNonce).
Module EVarModuleSet := VariableEqualitySetFun(EVarModule).
