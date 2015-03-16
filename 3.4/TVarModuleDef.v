(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Combine the definition of variables and its proofs.

*)
Set Implicit Arguments.
Require Export VariablesFunDef.
Require Export BooleanEqualitySetFunDef.
Require Export NonceDef.

Module TVarNonce : Nonce.
End TVarNonce.

Module TVarModule := VariablesFun(TVarNonce).
Module TVarModuleSet := BooleanEqualitySetFun(TVarModule).
