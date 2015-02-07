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
Require Export StaticSemantics.
Require Export TypeSafety.
Require Export CpdtTactics.
Require Export TacticNotations.
Require Export Tacticals.

Lemma WFU_implies_nodup:
  forall (u : Upsilon),
    WFU u ->
    UM.nodup u = true.
Proof.
  intros u.
  induction u.
  Crunch.
  intros.
  inversion H0.
  unfold UM.nodup.
  fold UM.nodup.
  rewrite H4.
  crush.
Qed.

Lemma gettype_weakening:
  forall (u : Upsilon) (x : EVar) (tau' tau : Tau) (p : Path),
    WFU u ->
    gettype u x [] tau' p tau ->
    forall (u' : Upsilon), 
      UM.extends u u' = true ->
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
   apply UM.map_extends_some_agreement with (c:= u); try assumption.
   apply WFU_implies_nodup; try assumption.
   apply WFU_implies_nodup; try assumption.   
Qed.

Lemma refp_weakening:
  forall (h : H) (u : Upsilon),
    HM.nodup h = true ->
    refp h u ->
    forall (h' : H),
      HM.nodup h' = true ->
      HM.extends h h' = true ->
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
   apply HM.map_extends_some_agreement with (c:= h); try assumption.
   apply IHrefpder; try assumption.
   (* Scotch Whiskey society wierd but wonderful. *)
Qed.
