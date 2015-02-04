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

Add LoadPath "/home/milnes/Desktop/Research/Cyclone/CycloneCoq/3".
Require Export CpdtTactics.
Require Export Case.

Require Export ContextSigDef.
Require Export BoolEqualitySigDef.
Require Export EVarModuleDef.
Require Export TauModuleDef.
Require Export ContextFunDef.

Module DeltaModule := ContextFun TVarModule KappaModule.
