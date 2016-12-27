(* An attempt at a value type for generalized environments. *)

(**************************************************************************
* TLC: A library for Coq                                                  *
* Keys for environment signature. 
**************************************************************************)

Set Implicit Arguments.
Require Import TLC.LibTactics TLC.LibList TLC.LibLogic TLC.LibNat TLC.LibEpsilon TLC.LibReflect TLC.LibFset.

(** * Abstract Definition of value for an environment. *)
Module Type ValueType.
Parameter value : Set.
Parameter value_inhab : Inhab value.
Parameter value_comp : Comparable value.
Instance  value_comparable : Comparable value := value_comp.
Definition values := fset value.

(* How do I get var without too much ? 
Function fv (v : value) := VariablesType.vars.
*)

End ValueType.