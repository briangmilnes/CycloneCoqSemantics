(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

 This tests the static semantics of typing in the heap, pg 64.

*)

Set Implicit Arguments.
Require Export Cyclone_Static_Semantics_Typing_Heap_Objects Cyclone_LN_Tactics.
Require Export Cyclone_Test_Utilities.
Import ListNotations.
Open Scope env_scope.
Import LVPE.LibVarPathEnvNotations.

Function tgti u v p t p' t' :=
  gettype u v p t p' t'.

Lemma test_gettype_induction:
  forall u v p t p' t',
    gettype u v p t p' t' ->
    tgti    u v p t p' t'.
Proof.
  introv GT.
  induction GT.
Abort.

Example gettype_empty_test2:
  gettype udot varx nil tau nil tau.
Proof.
  auto.
Qed.

Example binding:
  forall (E F : Upsilon) x t,
    E &p x ~p t &p F = E &p (x ~p t) &p F.
Abort.

Example gettype_etype_test2:
  gettype ((varx, pdot) ~p cint &p udot) varx pdot 
          (etype aliases k cint) (cons u_pe nil) cint.
Proof.
  applys~ gettype_etype;
  simpl_get.
  case_varpath*.
Qed.

Example gettype_left_test2:
  gettype udot varx nil (cross cint cint) (cons (i_pe zero_pe) nil) cint.
Proof.   
  apply gettype_pair_zero.
  auto.
Qed.

Example gettype_right_test2:
  gettype udot varx nil (cross cint cint) (cons (i_pe one_pe) nil) cint.
Proof.
  auto.
Qed.

