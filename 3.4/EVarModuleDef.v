(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Combine the definition of variables and its proofs.

*)
Set Implicit Arguments.
Require Export VariablesFunDef.
Require Export BooleanEqualitySetFunDef.
Require Export NonceDef.

Module EVarNonce : Nonce.
End EVarNonce.

Module EVarModule := VariablesFun(EVarNonce).
Module EVarModuleSet := BooleanEqualitySetFun(EVarModule).
