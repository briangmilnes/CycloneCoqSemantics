(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

   Lemmas about static semantics of heap objects. 

*)

Require Export LanguageModuleDef.
Require Export DynamicSemanticsTypeSubstitution.
Require Export DynamicSemanticsHeapObjects.
Require Export DynamicSemantics.
Require Export DynamicSemanticsTypeSubstitution.
Require Export StaticSemanticsKindingAndContextWellFormedness.
Require Export StaticSemanticsKindingAndContextWellFormednessLemmas.
Require Export StaticSemantics.
Require Export TypeSafety.
Require Export CpdtTactics.
Require Export TacticNotations.
Require Export Tacticals.

Lemma gettype_weakening:
  forall (u : Upsilon) (x : EV.T) (tau' tau : Tau) (p : Path),
    WFU u ->
    gettype u x [] tau' p tau ->
    forall (u' : Upsilon), 
      U.extends u u' = true ->
      WFU u' ->
      gettype u' x [] tau' p tau.
Proof.
  intros u x tau' tau p WFUder gettypeder.
  gettype_ind_cases(induction gettypeder) Case.
  Case "gettype u x p tau [] tau".
   constructor.
  Case "gettype u x p (cross t0 t1) (i_pe zero_pe :: p') tau".
   intros.
   apply IHgettypeder with (u':=u') in WFUder; try assumption.
   constructor; try assumption.
  Case "gettype u x p (cross t0 t1) (i_pe one_pe :: p') tau".
   intros.
   apply IHgettypeder with (u':=u') in WFUder; try assumption.
   constructor; try assumption.
  Case "gettype u x p (etype aliases alpha k tau') (u_pe :: p') tau)".
   intros.
   pose proof WFUder as WFUder'.
   apply IHgettypeder with (u':=u') in WFUder; try assumption.
   apply gettype_etype with (tau'':= tau''); try assumption.
   apply U.map_extends_some_agreement with (c:= u); try assumption.
   apply WFU_implies_nodup; try assumption.
   apply WFU_implies_nodup; try assumption.   
Qed.

Lemma refp_weakening:
  forall (h : Heap) (u : Upsilon),
    H.nodup h = true ->
    refp h u ->
    forall (h' : Heap),
      H.nodup h' = true ->
      H.extends h h' = true ->
      refp h' u.
Proof.
  intros h u noduph refpder.
  (* h, h' or refp. *)
  induction refpder.
  Case "u = []".
   intros.
   constructor.
  Case "refp_pack".
   intros.
   apply refp_pack with (tau:= tau) (alpha:= alpha) (k:= k) (v:= v) (v':= v');
     try assumption.
   apply H.map_extends_some_agreement with (c:= h); try assumption.
   apply IHrefpder; try assumption.
   (* Scotch Whiskey society wierd but wonderful. *)
Qed.
