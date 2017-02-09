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
Require Export Case.
Close Scope list_scope.
Import LibEnvNotations.
Import LVPE.LibVarPathEnvNotations.

Function A_13_Term_Preservation_Prop (In : Type) (H : TypJudgement In) 
         (h : Heap) (s : In) (h': Heap) (s': In)
         (d : D' h s h' s') := 
  D' h s h' s' ->
  forall u g,
    htyp u g h g ->
    refp h u ->
    forall t, 
      typ' empty u g s t ->
      exists g' u',
        extends g g' ->
        LVPE.extends u u' ->
        htyp u' g' h' g' /\
        refp h' u' /\
        typ' empty u' g' s' t.
Hint Unfold A_13_Term_Preservation_Prop.

Ltac invert_styp :=
      match goal with
      | H: styp _ _ _ _ _ |- styp _ _ _ _ _ =>
        try solve[inversions* H]
      end.

(* If one does not modify the heap, then g and u remain the same. *)
Ltac use_g_and_u :=
  match goal with
  | H: htyp ?u ?g ?h ?g,
    I: refp ?h ?u
    |- context[htyp _ _ ?h _] 
    => exists g u; intros; try splits 3; auto
 end.

Lemma A_13_Term_Preservation_1:
  forall h (e : E) h' e' (d : D' h e h' e'),
    A_13_Term_Preservation_Prop LtypJudgement h e h' e' d.
Proof.
  Dyn_Induction L_ind_mutual A_13_Term_Preservation_Prop; intros; (* 43 *)
    try use_g_and_u.
  (* 41 given splits
     25 existentials 
     7 styp
     6 rtyp
    No guarantee that it's the right use of u'/g;. 
  *)
  admit.
  try invert_styp.
  try invert_styp.
  try invert_styp.
  try invert_styp.
  Case "DS2.6".
  inversions* H2.
  constructor*.
  constructor*.


  admit.
  admit.
  admit.
  admit.
  admit.
  inversions* H3.
  specialize (H r u g H1 H2 cint H10).
  inversions H.
  inversions H3.
  exists x x0.
  intros.
  specialize (H H3 H4).
  inversions H.
  inversions H6.
  splits 3; auto.
  constructor*.
  (* type extension and so on *)
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  inversions* H2.
(*
  inversions* H6.
  inversions* H11.
  admit.
  admit.
  (* Ouch how to automate this? *)
  inversions* H2.
  inversions* H9.
  admit.
  inversions* H2.
  inversions* H6.

  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  inversions* H2.
  inversions* H6.
*)
Admitted.

Lemma A_13_Term_Preservation_2:
  forall h (e : E) h' e' (d : D' h e h' e'),
    A_13_Term_Preservation_Prop RtypJudgement h e h' e' d.
Proof.
  Dyn_Induction R_ind_mutual A_13_Term_Preservation_Prop.
  intros.
Admitted.

Lemma A_13_Term_Preservation_3:
  forall h (s : St) h' s' (d : D' h s h' s'),
    A_13_Term_Preservation_Prop StypJudgement h s h' s' d.
Proof.
  Dyn_Induction S_ind_mutual A_13_Term_Preservation_Prop.
  intros.
Admitted.

    