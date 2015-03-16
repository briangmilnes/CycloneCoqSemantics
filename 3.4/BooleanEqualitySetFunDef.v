(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 
*)
Set Implicit Arguments.
Require Export BooleanEqualityDef.
Require Export BooleanEqualitySetDef.

Module BooleanEqualitySetFun(BE' : BooleanEquality) : BooleanEqualitySet.
  Module BE := BE'.
  Module BESet := Ops(BE).
  Include BESet.
  Definition eq := BE.eq.
  Definition eq_equiv := BE.eq_equiv.
  Definition eq_dec := BE.eq_dec.
  Definition eqb := BE.eqb.
  Definition eqb_eq := BE.eqb_eq.
  Definition eqb_refl := BE.eqb_refl.
  Definition eqb_sym := BE.eqb_sym.
  Definition eqb_trans := BE.eqb_trans.
  Definition eq_trans := BE.eq_trans.
  Definition eqb_to_eq := BE.eqb_to_eq.
  Definition eqb_to_neq := BE.eqb_to_neq.
  Definition eqb_iff_eq := BE.eqb_iff_eq.
  Definition eqb_iff_neq := BE.eqb_iff_neq.
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
End BooleanEqualitySetFun.
