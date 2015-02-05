(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Boolean Equalities. 

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.
Require Import Coq.Init.Logic.

Set Implicit Arguments.

Module Type BoolEqualitySig.
  Parameter T : Type.
  Axiom beq_t : T -> T -> bool.
  Hint Resolve beq_t.
  
  Axiom beq_t_refl:  forall a,     beq_t a a = true.
  Hint Resolve beq_t_refl.
  Hint Rewrite beq_t_refl.
  
  Axiom beq_t_sym:   forall x y,   beq_t x y = beq_t y x.
  Hint Immediate beq_t_sym.
  
  Axiom beq_t_trans: forall x y z, beq_t x y = true -> beq_t y z = true -> beq_t x z = true.
  Hint Resolve beq_t_trans.
  
  Axiom beq_t_eq:    forall a b, beq_t a b = true -> a = b.
  Hint Resolve beq_t_eq.
  Axiom beq_t_neq:   forall a b, beq_t a b = false -> a <> b.
  Hint Resolve beq_t_neq.
  
End BoolEqualitySig.
