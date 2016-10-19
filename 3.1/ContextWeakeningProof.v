(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Defining type safety, page 67.

*)
(* DONE *)

Set Implicit Arguments.
Require Export LanguageModuleDef.
Require Export AlphaConversion.
Require Export CpdtTactics.
Require Export Case.
Require Export TacticNotations.
Require Export StaticSemanticsKindingAndContextWellFormednessLemmas.
Require Export StaticSemanticsKindingLemmas.

Lemma A_1_Context_Weakening_1:
  forall (d : Delta) (tau : Tau) (k : Kappa),
    WFD d -> 
    K d tau k ->
    forall (d' : Delta), 
      D.extends d d' = true ->
      WFD d' ->
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
   apply K_B.
   apply D.map_extends_some_agreement with (c:= d); try assumption.
   apply WFD_implies_nodup in H1; try assumption.
  Case "K d (ptype (tv_t alpha)) B".
   intros.
   constructor.
   apply D.map_extends_some_agreement with (c:= d); try assumption.
   apply WFD_implies_nodup in H1; try assumption.
  Case "K d tau A".
   intros.
   constructor; try assumption.
   apply IHKder; try assumption.
  Case "K d (cross t0 t1) A".
   intros.
   apply K_cross; try assumption.
   apply IHKder1; try assumption.
   apply IHKder2; try assumption.
  Case "K d (arrow t0 t1) A".
   intros.
   apply K_arrow; try assumption.
   apply IHKder1; try assumption.
   apply IHKder2; try assumption.
  Case "K d (ptype tau) B".
   intros.
   apply K_ptype; try assumption.
   apply IHKder; try assumption.
  Case "K d (utype alpha k tau) A".
   intros.
   apply K_utype; try assumption. 
   constructor;  try assumption.
   AdmitAlphaConversion.
   AdmitAlphaConversion.
   apply IHKder with (d':= (D.ctxt alpha k d')) in H; try assumption.
   unfold D.nodup.
   fold D.nodup.
   rewrite H0.
   assumption.
   apply D.extends_l_weak_r_str; try assumption.
   AdmitAlphaConversion.
   apply WFD_implies_nodup; try assumption.
   constructor; try assumption.
   AdmitAlphaConversion.
  Case "K d (etype p alpha k tau) A)".
   intros.
   apply K_etype; try assumption. 
   constructor;  try assumption.
   AdmitAlphaConversion.
   AdmitAlphaConversion.
   apply IHKder with (d':= (D.ctxt alpha k d')) in H; try assumption.
   unfold D.nodup.
   fold D.nodup.
   rewrite H0.
   assumption.
   apply D.extends_l_weak_r_str; try assumption.
   AdmitAlphaConversion.
   apply WFD_implies_nodup; try assumption.
   constructor; try assumption.
   AdmitAlphaConversion.
Qed.

Lemma A_1_Context_Weakening_2:
  forall (u : Upsilon),
    WFU u ->
    forall (x : TM.EV.T) (p : Path) (tau : Tau), 
    U.map u (x,p) = Some tau ->
    forall (d : Delta),
      WFD d ->
      K d tau A.
Proof.
  intros u WFUder.
  induction WFUder.
 Case "WFU []".
   intros.
   inversion H.
 Case "WFU ([(x, p, tau)] ++ u)".
  intros.
  unfold uctxt in H1.
  unfold U.map in H1.
  fold U.map in H1.
  case_eq(U.K_eq (x0, p0) (x,p)); intros; rewrite H3 in H1.
  inversion H1.
  subst.
  apply K_weakening with (d:= ddot); try assumption.
  constructor.
  apply D.empty_extended_by_all.
  apply IHWFUder with (d:= d) in H1; try assumption.
Qed.
