(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Signature for a context module.

*)

Require Import List.
Export ListNotations.
Require Export ZArith.
Require Import Init.Datatypes.
Require Export Coq.Bool.Bool.
Require Import Coq.Structures.Equalities.
Require Export Coq.MSets.MSets.

Require Export VariablesSigDef.
Require Export BoolEqualitySetSigDef.

Set Implicit Arguments.

Module Type ContextSig.
  Declare Module K : BoolEqualitySetSig.
  Declare Module T : BoolEqualitySetSig.
  Declare Module KSet : WOps(K).

  Parameter K    : Type.
  Parameter K_eq : K -> K -> bool.
  Parameter T    : Type.
  Parameter T_eq : T -> T -> bool.

  Parameter Context : Type.
  Parameter empty   : Context.
  Parameter add     : Context -> K -> T -> Context.
  Parameter map     : Context -> K -> option T.
  Parameter nodup   : Context -> bool.
  Parameter equal   : Context -> Context -> bool.
  Parameter concat  : Context -> Context -> Context.
  Parameter dom     : Context -> KSet.t.

  Parameter extends  : Context -> Context -> bool.
  (* Can I add k t into c' and extend c? *)
  Parameter extends1 : Context -> K -> T -> Context -> bool.
(* Parameter remove  : Context K T -> K -> Context K T. *)
  Axiom map_empty_none: forall k, map empty k = None.

End ContextSig.

