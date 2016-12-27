Set Implicit Arguments.
Require Import Cyclone_Formal_Syntax.
Require Import LibValueType.
Require Import TLC.LibReflect TLC.LibFset.

Module KappaValue : ValueType.

Definition value := Kappa.

Lemma value_inhab : Inhab Kappa.
Proof using. apply (prove_Inhab A). Qed.

Lemma value_comp : Comparable Kappa.
Admitted.

Instance value_comparable : Comparable value := value_comp.

Definition values := fset Kappa.
(* How do I get var without too much ? 
Function fv (v : value) := VariablesType.vars.
*)
End KappaValue.
