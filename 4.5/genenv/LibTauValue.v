Set Implicit Arguments.
Require Import Cyclone_Formal_Syntax.
Require Import LibValueType.
Require Import TLC.LibReflect TLC.LibFset.

Fixpoint tau_beq (t t' : Tau) {struct t} : bool :=
  match t, t' with 
    | btvar i, btvar j           => If (i = j) then true else false
    | ftvar alpha, ftvar beta    => If (alpha = beta) then true else false
    | cint, cint                 => false
    | cross t0 t1, cross t0' t1' => tau_beq t0 t0' && tau_beq t0 t0'
    | arrow t0 t1, arrow t0' t1' => tau_beq t0 t0' && tau_beq t0 t0'
    | ptype t0, ptype t0'        => tau_beq t0 t0'
    | utype k t0, utype k' t0'   => If (k = k') then tau_beq t0 t0' else false
    | etype p k t0, etype p' k' t0' => 
      (If (p = p') then (If (k = k') then tau_beq t0 t0' else false) else false)
    | _, _ => false
end.

Module TauValue : ValueType.

Definition value := Tau.

Lemma value_inhab : Inhab Tau.
Proof using. apply (prove_Inhab cint). Qed.

Lemma value_comp : Comparable Tau.
Admitted.

Instance value_comparable : Comparable value := value_comp.

Definition values := fset value.
(* How do I get var without too much ? 
Function fv (v : value) := VariablesType.vars.
*)
End TauValue.