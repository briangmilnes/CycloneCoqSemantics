(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Term Weakening 

*)

Set Implicit Arguments.
Require Export Cyclone_Formal_Syntax Cyclone_Static_Semantics_Kinding_And_Context_Well_Formedness.
Require Export Cyclone_Static_Semantics_Typing_Heap_Objects.
Require Export Cyclone_Classes Cyclone_Inductions Cyclone_LN_Tactics Cyclone_LN_Extra_Lemmas_And_Automation.
Require Export Cyclone_Context_Weakening_Proof.
Require Export Cyclone_LN_Types_Lemmas.
Require Export Cyclone_Term_Weakening_Proof_Admitted.
Require Export Cyclone_Fset_Lemmas.
Close Scope list_scope.
Import LibEnvNotations.
Import LVPE.LibVarPathEnvNotations.

Lemma A_3_Heap_Weakening_1:
  forall u g u' g',
    LVPE.extends u u' ->
    extends g g' ->
    WFC empty u' g' ->
    forall h g'', 
      htyp u g h g'' ->
      htyp u' g' h g''.
Proof.
  introv Euu' Egg' WFCd H.
  induction H; auto.
  specialize (IHhtyp Euu' Egg').
  constructor; try assumption.
  lets* T: A_2_Term_Weakening_3.
Qed.

Lemma A_3_Heap_Weakening_2:
  forall h u,
    refp h u ->
    forall h',
      extends h h' ->
      refp h' u.
Proof.
  introv R.
  induction R; intros; auto.
  apply refp_pack with (tau:=tau) (k:=k)(v:=v)(v':=v'); auto.
Qed.

