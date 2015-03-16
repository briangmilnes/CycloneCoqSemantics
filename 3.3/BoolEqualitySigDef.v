(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Boolean Equalities. 

*)
Set Implicit Arguments.
Require Import Coq.Structures.Equalities.
Require Export Coq.MSets.MSets.

(* Extend BooleanDecidableType a bit for easy use. *)
(* Definitions repeated so you don't have to troll through the Coq library.*)
Module Type BoolEqualitySig  <: BooleanDecidableType.
  Parameter t : Type.
  Parameter eq : t -> t -> Prop.
  Parameter eq_equiv : Equivalence eq.
  Parameter eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Parameter eqb : t -> t -> bool.
  Hint Resolve eqb.

  Parameter eqb_eq : forall x y : t, eqb x y = true <-> eq x y.
  
  Parameter eqb_refl:  forall a,     eqb a a = true.
  Hint Resolve eqb_refl.
  Hint Rewrite eqb_refl.
  
  Parameter eqb_sym:   forall x y,   eqb x y = eqb y x.
  Hint Immediate eqb_sym.
  
  Parameter eqb_trans: 
    forall x y z, 
      eqb x y = true -> eqb y z = true -> eqb x z = true.
  Hint Resolve eqb_trans.
  
  Parameter eq_trans: 
    forall x y z, eq x y -> eq y z -> eq x z.
  Hint Resolve eq_trans.

  Parameter eqb_to_eq:    forall a b, eqb a b = true -> a = b.
  Hint Resolve eqb_to_eq.

  Parameter eqb_to_neq:   forall a b, eqb a b = false -> a <> b.
  Hint Resolve eqb_to_neq.

  Parameter eqb_iff_eq:    forall a b, eqb a b = true <-> a = b.
  Hint Resolve eqb_iff_eq.

  Parameter eqb_iff_neq:   forall a b, eqb a b = false <-> a <> b.
  Hint Resolve eqb_iff_neq.

End BoolEqualitySig.
