(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 
  
 Term Preservation Proof

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
Require Export Cyclone_Canonical_Forms_Proof.
Close Scope list_scope.
Import LibEnvNotations.
Import LVPE.LibVarPathEnvNotations.

(* Try and formulate these, due to the value cases it's a bit funny. *)
Lemma A_14_Term_Progress_1:
  forall u g h,
    htyp u g h g ->
    refp h u ->
    forall e t,
      ltyp empty u g e t ->
      (exists x p, e = (p_e x p)) \/
      (exists h' e', L h (e_s e) h' e').
Proof.
  (* try one with a bad induction to get a feel. *)
  introv htypd refpd ltypd.
  induction ltypd.
  left.
  exists* (fevar x) p.
  right.
  destruct(classicT(Value e)).
  (* apply A_9_Canonical_Forms_4. *)
  admit. (* canonical forms lemma *)
  
Admitted.

Lemma A_14_Term_Progress_2:
  forall u g h,
    htyp u g h g ->
    refp h u ->
    forall e t,
      rtyp empty u g e t ->
      Value e \/
      (exists h' e', R h (e_s e) h' e').
Admitted.

Lemma A_14_Term_Progress_3:
  forall u g h,
    htyp u g h g ->
    refp h u ->
    forall s t,
      styp empty u g s t ->
      (exists v, Value v /\ s = (retn v)) \/
      (exists v, Value v /\ s = (e_s v)) \/
      (exists h' s', S h s h' s').
Admitted.