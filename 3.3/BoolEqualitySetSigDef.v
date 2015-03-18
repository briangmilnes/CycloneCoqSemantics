(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Boolean Equalities and a weak set on them.

*)
Set Implicit Arguments.
Require Import BoolEqualitySigDef.
Require Export Coq.MSets.MSets.

Require Export BoolEqualitySigDef.

Module Type BoolEqualitySetSig.
  Include BoolEqualitySig.
  (* This is WOps without t, I don't know how to do this in the module system. *)
  Parameter elt : Type.
  Parameter empty : t.
  Parameter is_empty : t -> bool.
  Parameter mem : elt -> t -> bool.
  Parameter add : elt -> t -> t.
  Parameter singleton : elt -> t.
  Parameter remove : elt -> t -> t.
  Parameter union : t -> t -> t.
  Parameter inter : t -> t -> t.
  Parameter diff : t -> t -> t.
  Parameter equal : t -> t -> bool.
  Parameter subset : t -> t -> bool.
  Parameter fold : forall A : Type, (elt -> A -> A) -> t -> A -> A.
  Parameter for_all : (elt -> bool) -> t -> bool.
  Parameter exists_ : (elt -> bool) -> t -> bool.
  Parameter filter : (elt -> bool) -> t -> t.
  Parameter partition : (elt -> bool) -> t -> t * t.
  Parameter cardinal : t -> nat.
  Parameter elements : t -> list elt.
  Parameter choose : t -> option elt.
End BoolEqualitySetSig.
