(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 
  
 Heap Object Safety

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

Ltac invert_get_nil:=
  match goal with
  | H: get' ?v1 nil _ |- _ => inversions* H
  end.

(* Path induction is not strong enough. *)
Lemma A_11_Heap_Object_Safety_1:
  forall v1 p, 
    Value v1 ->
    forall v2, 
      get' v1 p v2 ->
      forall v3,
        get' v1 p v3 ->
        v2 = v3.
Proof.
  introv Vv1 getd.
  induction getd; intros; try invert_get_nil;
  try solve[inversions H2; applys* IHgetd];
  try solve[inversions H1; applys* IHgetd].
Qed.

Lemma A_11_Heap_Object_Safety_2:
  forall p1, 
  forall v0 v1,
    Value v0 ->
    Value v1 ->
    get' v0 p1 v1 ->
    forall p2 v2,
      Value v2 ->
      get' v0 (app p1 p2) v2 ->
      get' v1 p2 v2.
Proof.
  intros p1.
  induction p1; intros.
  simpl in H3; auto.
  inversions *H1.
  destruct a; try destruct i.
  inversions H1.
  inversions H3.
  applys* (IHp1 v3).
  inversion H1; subst.
  inversion H3; subst.
  applys* (IHp1 v4).
  inversion H1; subst.
  inversion H3; subst.
  applys (IHp1 v3); auto.
Qed.

Lemma A_11_Heap_Object_Safety_3_1:
  forall h u, 
    refp h u ->
    forall g,
      htyp u g h g ->
      forall x p1 v1, 
        get' h(x) p1 v1 ->
        forall t1, 
          rtype empty u g v1 t1 ->
          forall p2 t2, 
            gettype u x p1 t1 p2 t2 ->
  exists v2,
    get' h(x) (app p1 p2 v2) /\
    rtyp empty upsilon gamma v2 t2.