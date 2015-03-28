(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

 This tests the static semantics of typing in the heap, pg 64.

*)

Set Implicit Arguments.
Require Export LanguageModuleDef.
Require Export DynamicSemanticsTypeSubstitution.
Require Export Tacticals.
Require Export TestUtilities.

Example gettype_empty_test2:
  gettype U.dot x [] tau [] tau.
Proof.
  eauto 20 with Chapter3.
Qed.

Definition pnil : Path := [].

Example getu_for_cint:
 U.map (U.ctxt (x, pnil) cint U.dot) (x,pnil) = Some cint.
Proof.
  eauto 20 with Chapter3.
Qed.

Example gettype_etype_test2:
  gettype (U.ctxt (x, pnil) cint U.dot) x pnil 
          (etype aliases alpha k cint) [u_pe] cint.
Proof.
  eapply gettype_etype;  eauto 20 with Chapter3.
  simpl.
  reflexivity.
Qed.

Definition t0 := cint.
Definition t1 := cint.

Example gettype_left_test2:
  gettype U.dot x [] (cross t0 t1) [i_pe zero_pe] cint.
Proof.   
  constructor; eauto 20 with Chapter3.
Qed.

Example gettype_right_test2:
  gettype U.dot x [] (cross cint cint) [i_pe one_pe] cint.
Proof.
  eauto 20 with Chapter3.
Qed.
