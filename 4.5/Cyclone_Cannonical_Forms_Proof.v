(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Cannonical Forms

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

Ltac induct_invert_values:=
  intros;
  subst;
  inversion H; subst; inversion H0.

Lemma A_9_Cannonical_Forms_1:
  forall u g v t,
    rtyp empty u g v t ->
    Value v ->
    t = cint ->
    exists i, 
      v = (i_e (i_i i)).
Proof.
  induct_invert_values.
  exists* n.
Qed.

Lemma A_9_Cannonical_Forms_2:
  forall u g v t,
    rtyp empty u g v t ->
    Value v ->
    forall t0 t1,
      t = (cross t0 t1) ->
      exists v0 v1, 
        v = (cpair v0 v1).
Proof.
  induct_invert_values.
  exists* e0 e1.
Qed.

Lemma A_9_Cannonical_Forms_3:
  forall u g v t,
    rtyp empty u g v t ->
    Value v ->
    forall t0 t1,
      t = (arrow t0 t1) ->
      exists s, 
        v = (f_e (dfun t0 t1 s)).
Proof.
  induct_invert_values.
  exists* s.
Qed.

Lemma A_9_Cannonical_Forms_4:
  forall u g v t,
    rtyp empty u g v t ->
    Value v ->
    forall t',
      t = (ptype t') ->
      exists x p, 
        v = (amp (p_e (fevar x) p)).
Proof.
  induct_invert_values.
  exists* v p.
Qed.

Lemma A_9_Cannonical_Forms_5:
  forall u g v t,
    rtyp empty u g v t ->
    Value v ->
    forall k t',
    t = (utype k t') ->
    exists f, 
      v = (f_e (ufun k f)).
Proof.
  induct_invert_values.
  exists* f.
Qed.

Lemma A_9_Cannonical_Forms_6:
  forall u g v t,
    rtyp empty u g v t ->
    Value v ->
    forall k t',
    t = (etype witnesschanges k t') ->
    exists t'' v', 
      v = (pack t'' v' (etype witnesschanges k t')).
Proof.
  induct_invert_values.
  exists* tau' e.
Qed.

Lemma A_9_Cannonical_Forms_7:
  forall u g v t,
    rtyp empty u g v t ->
    Value v ->
    forall k t',
    t = (etype aliases k t') ->
    exists t'' v', 
      v = (pack t'' v' (etype aliases k t')).
Proof.
  induct_invert_values.
  exists* tau' e.
Qed.
