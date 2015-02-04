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

Require Export CpdtTactics.
Require Export Case.
Require Export TacticNotations.
Require Export TypingInfoSigDef.

Set Implicit Arguments.

Module Type TypingInfoProofsSig.
  Include TypingInfoSig.
 Axiom beq_t_refl:  forall a,     beq_t a a = true.
 Hint Resolve beq_t_refl.
 Axiom beq_t_sym:   forall a b,   beq_t a b = beq_t b a.
 Hint Immediate beq_t_sym.
 Axiom beq_t_trans: forall a b c, beq_t a b = true -> beq_t b c = true -> beq_t a c = true.
 Hint Resolve beq_t_trans.
 Axiom beq_t_eq:    forall a b, beq_t a b = true -> a = b.
 Hint Resolve beq_t_eq.
 Axiom beq_t_neq:   forall a b, beq_t a b = false -> a <> b.
 Hint Resolve beq_t_neq.
End TypingInfoProofsSig.
