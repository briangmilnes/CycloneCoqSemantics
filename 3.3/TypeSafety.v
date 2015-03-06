(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  The few definitions for TypeSafety, pg. 67.

*)

Set Implicit Arguments.
Require Export LanguageModuleDef.
Require Export DynamicSemanticsTypeSubstitution.
Require Export DynamicSemanticsHeapObjects.
Require Export DynamicSemantics.
Require Export DynamicSemanticsTypeSubstitution.
Require Export StaticSemanticsKindingAndContextWellFormedness.
Require Export StaticSemantics.

Inductive NotStuck : Heap -> St -> Prop :=
  | NotStuck_return : forall (h : Heap) (v : E),
                        Value v ->
                        NotStuck h (retn v)
  | NotStuck_progress :
      forall (h: Heap) (s : St),
      (exists (h' : Heap) (s' : St), Sstar h s h' s') ->
      NotStuck h s.

Definition Stuck : Heap -> St -> Prop := 
  fun h: Heap => fun s: St => ~ (NotStuck h s).

Hint Constructors NotStuck    : Chapter3.
