(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  An attempt at a variable module in a context. 

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.
Require Import Coq.Init.Logic.

Add LoadPath "/home/milnes/Desktop/Research/Cyclone/CycloneCoq/3".
Require Export BoolEqualitySigDef.

Set Implicit Arguments.

Module Type VariablesSig <: BoolEqualitySig.
  Inductive Var : Set :=
  | var   : nat -> Var.

 Axiom beq_var : Var -> Var -> bool.
 Hint Resolve beq_var.

 Axiom beq_var_refl:  forall a,     beq_var a a = true.
 Hint Resolve beq_var_refl.
 Hint Rewrite beq_var_refl.

 Axiom beq_var_sym:   forall a b,   beq_var a b = beq_var b a.
 Hint Immediate beq_var_sym.
 Axiom beq_var_trans: forall a b c, beq_var a b = true -> beq_var b c = true -> beq_var a c = true.
 Hint Resolve beq_var_trans.
 Axiom beq_var_eq:    forall a b, beq_var a b = true -> a = b.

 Hint Resolve beq_var_eq.
 Axiom beq_var_neq:   forall a b, beq_var a b = false -> a <> b.
 Hint Resolve beq_var_neq.

 Definition T := Var.
 Definition beq_t := beq_var.
 Definition beq_t_refl := beq_var_refl.
 Definition beq_t_sym := beq_var_sym.
 Definition beq_t_trans := beq_var_trans.

 Definition beq_t_eq := beq_var_eq.
 Definition beq_t_neq := beq_var_neq.

End VariablesSig.
