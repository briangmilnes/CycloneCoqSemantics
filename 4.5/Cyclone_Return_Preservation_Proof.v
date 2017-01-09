(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Return Preservation

*)

Set Implicit Arguments.
Require Export Cyclone_Formal_Syntax Cyclone_Static_Semantics_Kinding_And_Context_Well_Formedness.
Require Export Cyclone_Dynamic_Semantics.
Require Export Cyclone_Classes Cyclone_Inductions Cyclone_LN_Tactics Cyclone_LN_Extra_Lemmas_And_Automation.
Require Export Cyclone_WFC_Lemmas.
Require Export Cyclone_WFU_Lemmas.
Require Export Cyclone_Context_Weakening_Proof.
Require Export Cyclone_Substitutions_Proof.
Require Export Cyclone_LN_Types_Lemmas.
Require Export Cyclone_Get_Lemmas.
Require Export Cyclone_Admit_Environment.
Close Scope list_scope.
Import LibEnvNotations.
Import LVPE.LibVarPathEnvNotations.

Lemma open_term_preserves_ret:
  forall s x, 
    ret s ->
    forall n, 
      ret (TM.open_rec_st n x s).
Proof.
  introv Rd.
  induction Rd; simpl; auto.
Qed.

Lemma open_type_preserves_ret:
  forall s x, 
    ret s ->
    ret (TTM.open_rec_st 0 x s).
Proof.
  introv Rd.
  induction Rd; simpl; auto.
Qed.
  
Ltac inversion_complex_ret :=
 match goal with
  | H : ret (_ _) |- _ => inversions* H
  | H : ret (_ _ _) |- _ => inversions* H
  end.

Lemma A_8_Return_Preservation:
  forall s H H' s',
    ret s ->
    S H s H' s' ->
    ret s'.
Proof.
  introv Rs Sd.
  induction Sd; try solve[auto];
    try solve[inversion_complex_ret ; try inversion_complex_ret];
    try solve[inversion_complex_ret;
              try constructor;
              try applys* open_type_preserves_ret;
              try applys* open_term_preserves_ret].
Qed.
