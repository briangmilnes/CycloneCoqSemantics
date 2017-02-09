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

(* Due to the different conditions on the form of the expressions, three
 propositions functions must be constructed and then the typing mutual induction
 principle must be applied. *)
Function A_14_Term_Progress_Prop_ltyp 
         (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) (_ : ltyp d u g e t) := 
     d = empty ->
     forall h, 
       htyp u g h g ->
       refp h u ->
       (exists x p, e = (p_e x p)) \/
       (exists h' e', L h e h' e').
Hint Unfold A_14_Term_Progress_Prop_ltyp.

Function A_14_Term_Progress_Prop_rtyp 
         (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) (r : rtyp d u g e t) := 
     d = empty ->
     forall h,
       htyp u g h g ->
       refp h u ->
       Value e \/
       (exists h' e', R h e h' e').
Hint Unfold A_14_Term_Progress_Prop_rtyp.

Function A_14_Term_Progress_Prop_styp 
         (d : Delta) (u : Upsilon) (g : Gamma) (s : St) (t : Tau) (st : styp d u g s t) := 
     d = empty ->
     forall h, 
       htyp u g h g ->
       refp h u ->
       (* Value s \/ Can't represent this, is it needed ? *)
       (exists v, s = (e_s v) \/ s = (retn v) /\ Value v) \/
       (exists h' s', S h s h' s').
Hint Unfold A_14_Term_Progress_Prop_styp.

(* Need to specialize double and triple induction hypothesis and 
   can't cleanly choose side. *)
Ltac specialize_IH_choose_branch :=
  match goal with
  | EE: empty = empty, 
    HT: htyp ?u ?g ?h ?g,
    R : refp ?h ?u,
    IH: empty = empty ->
        forall a : Heap, htyp ?u ?g a ?g -> refp a ?u -> _
  |- _ => 
    specialize (IH EE h HT R) ; inversion IH
  end.

Ltac specialize_IH :=
  repeat 
  match goal with
  | EE: empty = empty, 
    HT: htyp ?u ?g ?h ?g,
    R : refp ?h ?u,
    IH: empty = empty ->
        forall a : Heap, htyp ?u ?g a ?g -> refp a ?u -> _
  |- _ => 
    specialize (IH EE h HT R)
  end.

(* Can generalize this and at least get the step side. *)
Ltac invert_Value_step :=
  match goal with
  | V: Value _ \/ (exists _ _,  _ _ _ _ _) |- _ => 
    inversion V
end.

Ltac solve_Value :=
  match goal with
  | V' : Value ?v' |- _ =>
    try solve[left; 
              exists v';
              auto]
  end.

Ltac invert_sub_step :=
  repeat 
    match goal with
      | H: exists _ _, _ _ _ _ _ |- _ => inversions H
      | H: exists _, _ _ _ _ _ |- _ => inversions H
    end.

Ltac solve_sub_step :=
  timeout 1
          (right;
          eexists;
          eexists;
          constructor*).

Ltac find_solve_sub_step := 
  match goal with 
  | H: R _ _ _ _ |- _ \/ (exists _ _, _ _ _ _) => solve_sub_step
  | H: L _ _ _ _ |- _ \/ (exists _ _, _ _ _ _) => solve_sub_step
  | H: S _ _ _ _ |- _ \/ (exists _ _, _ _ _ _) => solve_sub_step
end.

Lemma A_14_Term_Progress_1:
  forall (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) (l : ltyp d u g e t),
    A_14_Term_Progress_Prop_ltyp l.
Proof.
  autounfold.
  assert((@empty Kappa) = empty); auto.
  apply (ltyp_ind_mutual 
           A_14_Term_Progress_Prop_styp
           A_14_Term_Progress_Prop_ltyp
           A_14_Term_Progress_Prop_rtyp); autounfold; intros; subst; auto;
    try specialize_IH;
    try invert_Value_step;
    try solve_Value;
    try invert_sub_step.
  (* 10/35 for find solve sub step. Loop is the problem. Restart here. *)
  try find_solve_sub_step.
  try find_solve_sub_step.
  admit.


  admit.
  try find_solve_sub_step.  
  admit.
  try find_solve_sub_step.
  admit.
  admit. (* Loop *)
  admit.
  try find_solve_sub_step.
  admit.
  admit.
  admit.
  try find_solve_sub_step.
  admit.
  admit.
  admit.
  admit.
  try find_solve_sub_step.
  admit.
  try find_solve_sub_step.
  admit.
  try find_solve_sub_step.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  try find_solve_sub_step.  
  admit.

Admitted.

Lemma A_14_Term_Progress_2:
  forall (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) (r : rtyp d u g e t),
    A_14_Term_Progress_Prop_rtyp r.
Proof.
  autounfold.
  assert((@empty Kappa) = empty); auto.
  apply (rtyp_ind_mutual 
           A_14_Term_Progress_Prop_styp
           A_14_Term_Progress_Prop_ltyp
           A_14_Term_Progress_Prop_rtyp); autounfold; intros; subst; auto.
Admitted.

Lemma A_14_Term_Progress_3:
  forall (d : Delta) (u : Upsilon) (g : Gamma) (s : St) (t : Tau) (st : styp d u g s t),
    A_14_Term_Progress_Prop_styp st.
Proof.
  autounfold.
  assert((@empty Kappa) = empty); auto.
  apply (styp_ind_mutual 
           A_14_Term_Progress_Prop_styp
           A_14_Term_Progress_Prop_ltyp
           A_14_Term_Progress_Prop_rtyp); autounfold; intros; subst; auto.
Admitted.