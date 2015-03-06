(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  The typing context mapping expression variables to their types.

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
Require Export TauModuleDef.
Require Export ContextFunDef.

(* TODO Delete. *)
Module GammaModule := ContextFun EVarModule TauModule.
