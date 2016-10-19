(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

 This tests the static semantics of typing in the heap, pg 64.

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.

Require Export FormalSyntax.
Require Export DynamicSemanticsTypeSubstitution.
Require Export Tacticals.

Require Export TestUtilities.

Example gettype_empty_test2:
  gettype [] x [] tau [] = Some tau.
Proof.
  reflexivity.
Qed.

Definition u := ((p_e x nil), cint) :: [].

Example gettype_etype_test_failed:
  getU u x [] = Some cint.
Proof.
 eauto 10 with Chapter3.
Qed.

Example gettype_etype_test2:
  gettype u x [] (etype aliases alpha k cint) [u_pe] = Some cint.
Proof.
  reflexivity.
Qed.

Definition t0 := cint.
Definition t1 := cint.

Example gettype_left_test2:
  gettype [] x [] (cross t0 t1) [i_pe (i_i 0)] = Some tau.
Proof.   
  reflexivity.
Qed.

Example gettype_right_test2:
  gettype [] x [] (cross t0 t1) [i_pe (i_i 1)] = Some tau.
Proof.
  reflexivity.
Qed.
