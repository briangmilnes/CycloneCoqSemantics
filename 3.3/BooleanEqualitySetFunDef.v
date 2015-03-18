(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Make a variable set. 

*)
Set Implicit Arguments.
Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.
Require Import Coq.Init.Logic.
Require Import Coq.Structures.Equalities.

Require Export Coq.MSets.MSets.
Require Export Coq.MSets.MSetInterface.
Require Export Coq.MSets.MSetWeakList.

Require Export BoolEqualitySigDef.

Module BooleanEqualitySetFun(v : BoolEqualitySig).
  Module set := Ops(v).
  Include set.
End BooleanEqualitySetFun.

