(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  A set of signatures that we need to construct boolean equalities,
 variables and variable sets. Using the standard library.

 However, the weakness of Coq modules in combination with poor type
 inference does cause us to manhandle the signatures and functors
 a little bit.
*)
Set Implicit Arguments.
Require Export Coq.Structures.Equalities.

Module Type BooleanEquality.
  Include BooleanDecidableType.
  (* These exists in Boolean.v but are not in a module. *)
  Parameter eqb_refl:  forall a,     eqb a a = true.
  Parameter eqb_sym:   forall x y,   eqb x y = eqb y x.
  Parameter eqb_trans: 
    forall x y z, 
      eqb x y = true -> eqb y z = true -> eqb x z = true.
  Parameter eq_trans: 
    forall x y z, eq x y -> eq y z -> eq x z.
  Parameter eqb_to_eq:    forall a b, eqb a b = true -> a = b.
  Parameter eqb_to_neq:   forall a b, eqb a b = false -> a <> b.
  Parameter eqb_iff_eq:    forall a b, eqb a b = true <-> a = b.
  Parameter eqb_iff_neq:   forall a b, eqb a b = false <-> a <> b.

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
End BooleanEquality.