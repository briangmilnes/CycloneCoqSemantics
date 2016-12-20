Set Implicit Arguments.
Require Import Cyclone_Formal_Syntax.
Require Import LibValueType.
Require Import TLC.LibReflect TLC.LibFset.

Module EValue : ValueType.

Definition value := E.

Lemma value_inhab : Inhab E.
Proof using. apply (prove_Inhab (i_e (i_i 0))). Qed.

Lemma value_comp : Comparable E.
Admitted.

Instance value_comparable : Comparable value := value_comp.

Definition values := fset E.
(* How do I get var without too much ? 
Function fv (v : value) := VariablesType.vars.
*)
End EValue.
