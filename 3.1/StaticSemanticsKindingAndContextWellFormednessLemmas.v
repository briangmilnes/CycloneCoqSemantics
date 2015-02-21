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
    U.nodup u = true.
Proof.
  intros u.
  induction u.
  Crunch.
  intros.
  inversion H.
  unfold U.nodup.
  fold U.nodup.
  rewrite H3.
  crush.
Qed.

Lemma WFD_implies_nodup:
  forall (d : Delta),
    WFD d ->
    D.nodup d = true.
Proof.
  intros d.
  induction d.
  Crunch.
  intros.
  inversion H.
  unfold D.nodup.
  fold D.nodup.
  rewrite H2.
  crush.
Qed.

(* Just ain't true but should be. Thesis bug or I must strengthen 
lots of theorems. *)

Lemma WFDG_implies_nodup:
  forall (d : Delta) (g : Gamma),
    WFDG d g ->
    G.nodup g = true.
Proof.
Admitted.


