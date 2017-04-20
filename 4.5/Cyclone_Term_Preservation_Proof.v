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
Close Scope list_scope.
Import LibEnvNotations.
Import LVPE.LibVarPathEnvNotations.

(* This has serious problems because dynamic semantics, D', is always in
terms of statements but typing relations are in terms of St, E, ... *)
Function A_13_Term_Preservation_prop (In : Type) (H : TypJudgement In) 
         (u : Upsilon) (g : Gamma) (s : In) (t : Tau)
         (st : typ' empty u g s t) := 
  forall u g h,
    htyp u g h g ->
    refp h u ->
      forall h', (* s',
         D' h s h' s' -> *)
        exists g' u',
          extends g g' ->
          LVPE.extends u u' ->
          htyp u' g' h' g' /\
          refp h' u' /\
          typ' empty u' g' s(*'*) t.
Hint Unfold A_13_Term_Preservation_prop.
Check A_13_Term_Preservation_prop.

Function PL (h : Heap) (s : St) (h' : Heap) (s' : St) (_ : L h s h' s') := 
  forall u g h,
    htyp u g h g ->
    refp h u ->
    forall t, 
      ltyp empty u g s t ->
    exists g' u',
      extends g g' ->
      LVPE.extends u u' ->
      htyp u' g' h' g' /\
      refp h' u' /\
      ltyp empty u' g' s' t.
Hint Unfold PL.

Function PR (d : Delta) (u: Upsilon) (g : Gamma) (e: E) (t : Tau) (_ : rtyp d u g e t) := 
  forall u g h,
    htyp u g h g ->
    refp h u ->
      forall h' e', 
        R h (e_s e) h' e' ->
        exists g' u',
          extends g g' ->
          LVPE.extends u u' ->
          htyp u' g' h' g' /\
          refp h' u' /\
          rtyp empty u' g' e t.
Hint Unfold PR.

Function PS (d : Delta) (u: Upsilon) (g : Gamma) (s: St) (t : Tau) (_ : styp d u g s t) := 
  forall u g h,
    htyp u g h g ->
    refp h u ->
      forall h' s', 
        S h s h' s' ->
        exists g' u',
          extends g g' ->
          LVPE.extends u u' ->
          htyp u' g' h' g' /\
          refp h' u' /\
          styp empty u' g' s t.
Hint Unfold PS.

Lemma A_13_Term_Preservation_1:
  forall (d : Delta) (u: Upsilon) (g : Gamma) (e: E) (t : Tau),
    d = empty ->
    forall (typ : ltyp d u g e t),
      PL typ.
Proof.
  introv DE.
  unfold PL.
  (* wrong! on S not ltyp! *)
  apply (ltyp_ind_mutual PS PL PR); autounfold in *; intros; subst.
  apply(SRL_ind_mutual
          (fun (h : Heap) (s : St) (h' : Heap) (s' : St) (_ : S h s h' s') =>
             f h s h' s')
          (fun (h : Heap) (s : St) (h' : Heap) (s' : St) (_ : R h s h' s') =>
             f h s h' s')
          (fun (h : Heap) (s : St) (h' : Heap) (s' : St) (_ : L h s h' s') =>
             f h s h' s')); intros.



Lemma A_13_Term_Preservation_2:
  forall u g h,
    htyp u g h g ->
    refp h u ->
    forall e t,
      rtyp empty u g e t ->
      forall h' e', 
        R h (e_s e) h' e' ->
        exists g' u',
          extends g g' ->
          LVPE.extends u u' ->
          htyp u' g' h' g' /\
          refp h' u' /\
          rtyp empty u' g' e t.
Admitted.

Lemma A_13_Term_Preservation_3:
  forall u g h,
    htyp u g h g ->
    refp h u ->
    forall e t,
      styp empty u g e t ->
      forall h' e', 
        S h e h' e' ->
        exists g' u',
          extends g g' ->
          LVPE.extends u u' ->
          htyp u' g' h' g' /\
          refp h' u' /\
          styp empty u' g' e t.
Admitted.              
    