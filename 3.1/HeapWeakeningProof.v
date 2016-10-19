(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Defining type safety, page 67.

*)

Set Implicit Arguments.
Require Export LanguageModuleDef.
Require Export StaticSemanticsKindingAndContextWellFormedness.
Require Export StaticSemanticsKindingAndContextWellFormednessLemmas.
Require Export TermWeakeningProof.
Require Export Tacticals.

(* May need some lemmas from the 3 case. *)

Lemma A_3_Heap_Weakening_1_strengthen_quantification:
  forall (u u' : Upsilon) (g g': Gamma),
    U.extends u u' = true ->
    G.extends g g' = true ->
    WFC ddot u' g' ->
    forall (h : Heap) (g'' : Gamma), 
      htyp u g h g'' ->
      htyp u' g' h g''.
Proof.
  intros u u' g g' uext gext WFCder h g'' htypder.
  htyp_ind_cases (induction htypder) Case; try solve[crush].
  Case "htyp u g h ([(x, tau)] ++ g')".
   apply htyp_xv with (h':= h') (v:= v); try assumption.
   apply IHhtypder in uext; try assumption.
   apply A_2_Term_Weakening_3 with (u:= u') (g:= g') ; try assumption.
   admit.
   apply U.extends_refl.
   admit.
   apply G.extends_refl.
   admit.
Admitted.

(* Correct. *)

Lemma A_3_Heap_Weakening_2:
  forall (u : Upsilon) (h : H),
    refp h u ->
    forall (h' : H),
      refp (h ++ h') u.
Proof.
  intros u h refpder.
  refp_ind_cases (induction refpder) Case.
  Case  "refp h []".
   intros.
   constructor.
  Case "refp h ([(x, p, tau')] ++ u)".
   intros.
   apply refp_pack 
   with (tau:= tau) (alpha:= alpha) (k:= k) (v:= v) (v':= v'); try assumption.
   apply getH_Some_weakening; try assumption.
   apply refp_weakening; try assumption.
Qed.
