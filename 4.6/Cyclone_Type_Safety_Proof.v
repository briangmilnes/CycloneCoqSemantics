(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 
  
 Type Safety

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

Definition stuck H s :=
  ~(exists v, s = retn v) /\
  ~(exists H' s', S H s H' s').
(* Need a reflexive transitive closure of S. *)

Theorem Preservation:
  forall h s,
    prog h s ->
    forall h' s',
      S h s h' s' ->
      prog h' s'.
Admitted.

Theorem Progress:
  forall h s,
    prog h s ->
    (exists v, s = retn v) \/
    (exists h' s', S h s h' s').
Admitted.
