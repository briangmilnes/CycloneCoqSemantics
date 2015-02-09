(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

   Lemmas about static semantics kinding.

*)

Set Implicit Arguments.
Require Export LanguageModuleDef.
Require Export AlphaConversion.
Require Export DynamicSemanticsTypeSubstitution.
Require Export DynamicSemanticsHeapObjects.
Require Export DynamicSemantics.
Require Export DynamicSemanticsTypeSubstitution.
Require Export StaticSemanticsKindingAndContextWellFormedness.
Require Export StaticSemanticsKindingAndContextWellFormednessLemmas.
Require Export StaticSemantics.
Require Export CpdtTactics.
Require Export TacticNotations.

Lemma K_weakening:
  forall (d : Delta) (tau : Tau) (k : K.T),
      WFD d ->
      K d tau k -> 
      forall (d' : Delta),
        WFD d' ->
        DM.extends d d' = true ->
        K d' tau k.
Proof.
 intros d tau k WFDder Kder.
 pose proof WFDder as WFDder'.
 apply WFD_implies_nodup in WFDder'.
 K_ind_cases (induction Kder) Case.
 Case "K d cint B".
  intros.
  constructor.
 Case "K d (tv_t alpha) B".
  intros.
  apply DM.map_extends_some_agreement with (c:= d) (c':= d') in H0; try assumption.
  apply K_B; try assumption.
  apply WFD_implies_nodup; try assumption.
 Case "K d (ptype (tv_t alpha)) B".
  intros.
  constructor.
  apply DM.map_extends_some_agreement with (c:= d) (c':= d') in H0; try assumption.
  apply WFD_implies_nodup; try assumption.
 Case "K d tau A".
  intros.
  apply IHKder with (d':= d') in WFDder; try assumption.
  constructor; try assumption.
 Case "K d (cross t0 t1) A".
  intros.
  pose proof WFDder as WFDder2.
  apply IHKder1 with (d':= d') in WFDder; try assumption.
  apply IHKder2 with (d':= d') in WFDder2; try assumption.
  apply K_cross; try assumption.
 Case "K d (arrow t0 t1) A".
  intros.
  pose proof WFDder as WFDder2.
  apply IHKder1 with (d':= d') in WFDder; try assumption.
  apply IHKder2 with (d':= d') in WFDder2; try assumption.
  apply K_arrow; try assumption.
 Case "K d (ptype tau) B".
  intros.
  apply IHKder with (d':= d') in WFDder; try assumption.
  constructor.
  assumption.
 Case "K d (utype alpha k tau) A".
  intros.
  assert (Z: DM.map d' alpha = None).
  AdmitAlphaConversion.
  apply IHKder with (d':= (dctxt alpha k d')) in H0; try assumption.
  apply K_utype; try assumption.
  constructor; try  assumption.
  apply WFD_implies_nodup; try assumption.
  constructor; try assumption.
  apply DM.extends_l_weaken_r_strengthen; try assumption.
  apply WFD_implies_nodup; try assumption.
 Case "K d (etype p alpha k tau) A)".
  intros.
  assert (Z: DM.map d' alpha = None).
  AdmitAlphaConversion.
  apply IHKder with (d':= (dctxt alpha k d')) in H0; try assumption.
  apply K_etype; try assumption.
  constructor; try  assumption.
  apply WFD_implies_nodup; try assumption.
  constructor; try assumption.
  apply DM.extends_l_weaken_r_strengthen; try assumption.
  apply WFD_implies_nodup; try assumption.  
Qed.

Lemma AK_weakening:
  forall (d : Delta) (tau : Tau) (k : K.T),
      WFD d ->
      AK d tau k -> 
      forall (d' : Delta),
        WFD d' ->
        DM.extends d d' = true ->
        AK d' tau k.
Proof.
 intros d tau k WFDder AKder.
 inversion AKder.
 intros.
 constructor.
 apply K_weakening with (d:= d); try assumption.
 intros.
 rewrite <- H2 in *.
 rewrite <- H1 in *.
 assert (Z: DM.map d' alpha = Some A).
 apply DM.map_extends_some_agreement with (c:= d0) (c':= d') in H0; try assumption;
 try apply WFD_implies_nodup; try assumption.  
 apply AK_A; try assumption.
Qed.
