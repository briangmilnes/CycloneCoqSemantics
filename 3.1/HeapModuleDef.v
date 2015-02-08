(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  An attempt at a context module, just the operations, proofs in 
 another module.

*)

Require Import List.
Export ListNotations.
Require Export ZArith.
Require Import Init.Datatypes.
Require Export Coq.Bool.Bool.

Require Export CpdtTactics.
Require Export Case.

Require Export ContextSigDef.
Require Export BoolEqualitySigDef.
Require Export EVarModuleDef.
Require Export ContextFunDef.
Require Export TermModuleDef.

Module HeapModule := ContextFun EVarModule TermModule.
