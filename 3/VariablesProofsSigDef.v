(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  The signature for the proofs required on variables.

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.
Require Import Coq.Init.Logic.

Require Export CpdtTactics.
Require Export Case.
Require Export TacticNotations.
Require Export VariablesDef.
Require Export VariablesSigDef.

Set Implicit Arguments.

Module Type VariablesProofsSig.
 Include VariablesSig.

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
End VariablesProofsSig.
