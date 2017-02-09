(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Subst Lemmas

*)

Set Implicit Arguments.
Require Export Cyclone_Formal_Syntax.
Require Export Cyclone_LN_Tactics.

Lemma fv_subst:
  forall alpha t t',
    alpha \notin T.fv t' ->
    T.subst t alpha t' = t'.
Proof.
  induction t'; auto; intros; simpl; fequals*. 
  apply notin_singleton in H.
  case_var*.
Qed.
