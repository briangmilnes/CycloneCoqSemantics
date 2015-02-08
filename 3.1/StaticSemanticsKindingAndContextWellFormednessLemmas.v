(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Lemmas for these definitions. 

*)
Set Implicit Arguments.
Require Export LanguageModuleDef.
Require Export StaticSemanticsKindingAndContextWellFormedness.
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

Lemma WFD_implies_nodup:
  forall (d : Delta),
    WFD d ->
    DM.nodup d = true.
Proof.
  intros d.
  induction d.
  Crunch.
  intros.
  inversion H0.
  unfold DM.nodup.
  fold DM.nodup.
  rewrite H3.
  crush.
Qed.


