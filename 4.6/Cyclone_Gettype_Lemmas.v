(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Gettype Lemmas.

*)


Set Implicit Arguments.
Require Export Cyclone_Formal_Syntax Cyclone_Static_Semantics_Kinding_And_Context_Well_Formedness.
Require Export Cyclone_Static_Semantics_Typing_Heap_Objects.
Require Export Cyclone_Classes Cyclone_Inductions Cyclone_LN_Tactics Cyclone_LN_Extra_Lemmas_And_Automation.
Require Export Cyclone_LN_Types_Lemmas.
Close Scope list_scope.
Import LibEnvNotations.
Import LVPE.LibVarPathEnvNotations.

Lemma gettype_weakening:
  forall u u' x tau' p tau,
  gettype u x nil tau' p tau ->
  LVPE.extends u u' ->
  gettype u' x nil tau' p tau.
Proof.
  intros.
  unfold LVPE.extends, LVPE.binds in *.
  induction H; auto.
  apply gettype_etype with (tau'':= tau'');auto.
Qed.
Ltac gettype_weakening :=
  match goal with 
    | H: gettype ?u' ?x' nil ?tau'' ?p' ?tau',
      I: LVPE.extends ?u' ?u''
    |- gettype ?u'' ?x' nil ?tau'' ?p' ?tau' =>
      apply gettype_weakening with (u:= u'); assumption
  end.
Hint Extern 1 (gettype _ _ nil _ _ _) => try gettype_weakening.
