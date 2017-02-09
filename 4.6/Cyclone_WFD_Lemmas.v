(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION".   Daniel Grossman, August 2003 *)
(* Brian Milnes 2016 *)

Set Implicit Arguments.
Require Export TLC.LibEnv.
Require Export Cyclone_Formal_Syntax Cyclone_Static_Semantics_Kinding_And_Context_Well_Formedness.
Close Scope list_scope.
Import LibEnvNotations.

Lemma WFD__ok:
  forall d,
    WFD d ->
    ok d.
Proof.
  introv WFDd.
  induction WFDd.
  constructor*.
  constructor*.
  apply get_none_inv in H; auto.
Qed.

Ltac WFD__ok :=
 match goal with
 | H: WFD ?d |- ok ?d => apply WFD__ok
end.
Hint Extern 1 (ok _) => WFD__ok.

Lemma ok__WFD:
  forall d,
    ok d ->
    WFD d.
Proof.
  introv OKd.
  induction OKd.
  constructor*.
  constructor*.
  apply get_none in H; auto.
Qed.

Ltac ok__WFD :=
 match goal with
 | H: ok ?d |- WFD ?d => apply ok__WFD
end.
Hint Extern 1 (WFD _) => ok__WFD.
