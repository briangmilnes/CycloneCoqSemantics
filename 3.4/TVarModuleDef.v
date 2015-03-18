(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Combine the definition of variables and its proofs.

*)
Set Implicit Arguments.
Require Export VariableEqualityFunDef.
Require Export VariableEqualitySetFunDef.
Require Export NonceDef.

Module TVarNonce : Nonce.
End TVarNonce.

Module TVarModule := VariableEqualityFun(TVarNonce).
Module TVarModuleSet := VariableEqualitySetFun(TVarModule).
