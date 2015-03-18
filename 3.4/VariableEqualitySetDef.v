(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 
*)

Set Implicit Arguments.
Require Export Coq.MSets.MSets.
Require Export Coq.MSets.MSetWeakList.

Require Export BooleanEqualitySetDef.
Require Export VariableEqualityDef.

(* Repeat the definitions of BooleanEquality and WOps(BooleanEquality) as I can't
get type inference to work otherwise. *)
Module Type VariableEqualitySet <: BooleanEqualitySet.
   Declare Module BE : VariableEquality.
   Include WOps(BE).
   Parameter eq : elt -> elt -> Prop.
   Parameter eq_equiv : Equivalence eq.
   Parameter eq_dec : forall x y : elt, {eq x y} + {~ eq x y}.
   Parameter eqb : elt -> elt -> bool.
   Parameter eqb_eq : forall x y : elt, eqb x y = true <-> eq x y.
   Parameter eqb_refl : forall a : elt, eqb a a = true.
   Parameter eqb_sym : forall x y : elt, eqb x y = eqb y x.
   Parameter eqb_trans :
     forall x y z : elt, eqb x y = true -> eqb y z = true -> eqb x z = true.
   Parameter eq_trans : forall x y z : elt, eq x y -> eq y z -> eq x z.
   Parameter eqb_to_eq : forall a b : elt, eqb a b = true -> a = b.
   Parameter eqb_to_neq : forall a b : elt, eqb a b = false -> a <> b.
   Parameter eqb_iff_eq : forall a b : elt, eqb a b = true <-> a = b.
   Parameter eqb_iff_neq : forall a b : elt, eqb a b = false <-> a <> b.

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
End VariableEqualitySet.
