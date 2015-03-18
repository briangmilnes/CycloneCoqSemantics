(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  A variable module. 

*)

Set Implicit Arguments.
Require Export BooleanEqualityDef.

Module Type VariableEquality <: BooleanEquality.
  Inductive Var : Set :=
  | var   : nat -> Var.
  Definition t := Var.

   Parameter eq : t -> t -> Prop.
   Parameter eq_equiv : Equivalence eq.
   Parameter eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
   Parameter eqb : t -> t -> bool.
   Parameter eqb_eq : forall x y : t, eqb x y = true <-> eq x y.
   Parameter eqb_refl : forall a : t, eqb a a = true.
   Parameter eqb_sym : forall x y : t, eqb x y = eqb y x.
   Parameter eqb_trans :
     forall x y z : t, eqb x y = true -> eqb y z = true -> eqb x z = true.
   Parameter eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
   Parameter eqb_to_eq : forall a b : t, eqb a b = true -> a = b.
   Parameter eqb_to_neq : forall a b : t, eqb a b = false -> a <> b.
   Parameter eqb_iff_eq : forall a b : t, eqb a b = true <-> a = b.
   Parameter eqb_iff_neq : forall a b : t, eqb a b = false <-> a <> b.

  Hint Resolve eqb.
  Hint Resolve eqb_refl.
  Hint Rewrite eqb_refl.
  Hint Immediate eqb_sym.
  Hint Resolve eqb_trans.
  Hint Resolve eq_trans.
  Hint Resolve eqb_to_eq.
  Hint Resolve eqb_to_neq.
  Hint Resolve eqb_iff_eq.
  Hint Resolve eqb_iff_neq.
End VariableEquality.
