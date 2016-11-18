(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION".   Daniel Grossman, August 2003 *)
(* Test code for FV, env's operations are not
  evaluating. *)
(* Brian Milnes 2016 *)

Set Implicit Arguments.
Require Export Cyclone_Type_Substitution Cyclone_LN_FV Cyclone_LN_LC_Body Cyclone_LN_Open_Close Cyclone_LN_Tactics Cyclone_LN_FSET Cyclone_LN_Tactics.
Open Scope cyclone_scope.

Lemma fv_delta_test:
  forall alpha, 
    \{alpha} = 
    ftv_delta(single alpha A).
Proof.
  intros.
  unfold ftv_delta.
  rewrite dom_single.
