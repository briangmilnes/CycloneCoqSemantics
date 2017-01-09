(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION".   Daniel Grossman, August 2003 *)
(* Brian Milnes 2016 *)

Set Implicit Arguments.
Require Export TLC.LibEnv.
Require Export Cyclone_Formal_Syntax Cyclone_Static_Semantics_Kinding_And_Context_Well_Formedness.
Close Scope list_scope.
Import LibEnvNotations.

Lemma WFD_ok:
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

Ltac WFD_ok :=
 match goal with
 | H: WFD ?d |- ok ?d => apply WFD_ok
end.
Hint Extern 1 (ok _) => WFD_ok.
