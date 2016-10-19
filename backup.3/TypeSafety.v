(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  The few definitions for TypeSafety, pg. 67.

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.
Require Import Coq.Init.Logic.

Require Export FormalSyntax.
Require Export DynamicSemanticsTypeSubstitution.
Require Export DynamicSemanticsHeapObjects.
Require Export DynamicSemantics.
Require Export DynamicSemanticsTypeSubstitution.
Require Export StaticSemanticsKindingAndContextWellFormedness.
Require Export StaticSemantics.

Inductive NotStuck : H -> St -> Prop :=
  | NotStuck_return : forall (h : H) (v : E),
                        Value v ->
                        NotStuck h (retn v)
  | NotStuck_progress :
      forall (h: H) (s : St),
      (exists (h' : H) (s' : St), Sstar h s h' s') ->
      NotStuck h s.

Definition Stuck : H -> St -> Prop := 
  fun h: H => fun s: St => ~ (NotStuck h s).

Hint Constructors NotStuck    : Chapter3.

