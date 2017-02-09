(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

   Do substitutions commute? 

*)

Set Implicit Arguments.
Require Export Cyclone_Formal_Syntax Cyclone_Static_Semantics_Kinding_And_Context_Well_Formedness.
Require Export Cyclone_Static_Semantics_Typing_Heap_Objects.
Require Export Cyclone_Classes Cyclone_Inductions Cyclone_LN_Tactics Cyclone_LN_Extra_Lemmas_And_Automation.
Require Export Cyclone_Context_Weakening_Proof.
Require Export Cyclone_LN_Types_Lemmas.
Close Scope list_scope.
Import LibEnvNotations.
Import LVPE.LibVarPathEnvNotations.

(* Dan is assuming alpha <> beta! *)
Lemma A_5_Commuting_Substitutions:
  forall beta t2,
    beta \notin T.fv t2 ->
    forall t0 t1 alpha,
      alpha <> beta ->
      (T.subst t2 alpha (T.subst t1 beta t0)) =
      (T.subst (T.subst t2 alpha t1) beta (T.subst t2 alpha t0)).
Proof.
  induction t0; intros; try solve[auto]; try solve[simpl; try case_var*; fequals*].
  destruct(classicT(alpha = v)).
  subst.
  simpl.
  case_var.
  case_var.
  simpl.
  case_var.
  rewrite* TP.subst_fresh.
  simpl.
  case_var.
  case_var.
  simpl.
  case_var*.
  case_var.
  simpl.
  case_var.
  case_var*.
Qed.
