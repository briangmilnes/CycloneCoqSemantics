(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION".   Daniel Grossman, August 2003 *)
(* This is all of the LN infrastructure packed in a module for types. *)
(* Brian Milnes 2016 *)

Set Implicit Arguments.
Require Export Cyclone_LN_Env.
Require Export Cyclone_Test_Utilities.
Import ListNotations.
Import LibEnvNotations.
Import LVPE.LibVarPathEnvNotations.

(* Ensure that I can process and simplify fv calculations for envs. *)
(* TODO *)

Ltac rew_env_defs := autorewrite with env_defs in *.

Example fv_heap_test:
  fv_heap ((varx ~ (i_e (i_i 0))) & empty) = \{varx}.
Proof.
Admitted.