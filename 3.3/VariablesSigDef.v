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

Require Export BoolEqualitySigDef.

Module Type VariablesSig <: BoolEqualitySig.
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

(* Now get finite weak list sets for variables. *)
End VariablesSig.
