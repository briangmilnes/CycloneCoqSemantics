(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  An attempt at a context module.

*)

Require Import List.
Export ListNotations.
Require Export ZArith.
Require Import Init.Datatypes.
Require Export Coq.Bool.Bool.

Require Import DynamicSemanticsTypeSubstitution.
Require Export CpdtTactics.
Require Export Case.
Require Import FormalSyntax.
Require Export VariablesProofsSigDef.
Require Export TypingInfoProofsSigDef.

Set Implicit Arguments.

Module Type ContextSig.
  Declare Module K : VariablesProofsSig.
  Declare Module T : TypingInfoProofsSig.

  Parameter K    : Type.
  Parameter K_eq : K -> K -> bool.
  Parameter T    : Type.
  Parameter T_eq : T -> T -> bool.

  Parameter Context : Type -> Type -> Type.
  Parameter empty   : Context K T.
  Parameter add     : Context K T -> K -> T -> Context K T.
  Parameter map     : Context K T -> K -> option T.
  Parameter nodup   : Context K T -> bool.
  Parameter equal   : Context K T -> Context K T -> bool.
  Parameter extends  : Context K T -> Context K T -> bool.

(*
  Parameter extends1 : Context K T -> K -> T -> Context K T -> Prop.
  Parameter remove  : Context K T -> K -> Context K T.
*)
  Axiom map_empty_none: forall k, map empty k = None.

End ContextSig.

