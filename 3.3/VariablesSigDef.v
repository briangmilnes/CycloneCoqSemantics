(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  A variable module. 

*)

Set Implicit Arguments.
Require Import List.
Export ListNotations.

Require Import ZArith.
Require Import Init.Datatypes.
Require Import Coq.Init.Logic.
Require Import Coq.Structures.Equalities.

Require Export BoolEqualitySetSigDef.

Module Type VariablesSig <: BoolEqualitySetSig.
  Inductive Var : Set :=
  | var   : nat -> Var.

 Definition  t := Var.

 Parameter eq : t -> t -> Prop.
 Parameter eq_equiv : Equivalence eq.
 Parameter eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
 Parameter eqb : t -> t -> bool.
 Parameter eqb_eq : forall x y : t, eqb x y = true <-> eq x y.
 Hint Resolve eqb.

 Parameter eqb_refl:  forall a,     eqb a a = true.
 Hint Resolve eqb_refl.
 Hint Rewrite eqb_refl.

 Parameter eqb_sym:   forall a b,   eqb a b = eqb b a.
 Hint Immediate eqb_sym.
 Parameter eqb_trans: forall a b c, eqb a b = true -> eqb b c = true -> eqb a c = true.
 Hint Resolve eqb_trans.
 Parameter eq_trans: forall a b c, eq a b -> eq b c -> eq a c.

 Parameter eqb_to_eq:    forall a b, eqb a b = true -> a = b.

 Hint Resolve eqb_eq.
 Parameter eqb_to_neq:   forall a b, eqb a b = false -> a <> b.
 Hint Resolve eqb_to_neq.

 Parameter eqb_iff_eq:    forall a b, eqb a b = true <-> a = b.
 Hint Resolve eqb_iff_eq.

 Parameter eqb_iff_neq:   forall a b, eqb a b = false <-> a <> b.
 Hint Resolve eqb_iff_neq.

(* Again so you can see what you have to work with. *)
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

End VariablesSig.
