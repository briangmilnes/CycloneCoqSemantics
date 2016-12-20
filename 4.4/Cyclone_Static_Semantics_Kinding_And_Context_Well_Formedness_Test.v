(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

 This defines the static semantics of statements and expressions, pg. 63. 

*)

Set Implicit Arguments.
Set Implicit Arguments.
Require Export Cyclone_Formal_Syntax Cyclone_Static_Semantics_Kinding_And_Context_Well_Formedness.
Require Export Cyclone_Static_Semantics_Typing_Heap_Objects.
Require Export Cyclone_Test_Utilities.
Require Export Cyclone_LN_Tactics.
Close Scope list_scope.
Import LibEnvNotations.
Import LVPE.LibVarPathEnvNotations.

(* Test K *)

Example K_int_test:
  K ddot cint B.
Proof.
  auto.
Qed.


Example K_B_test:
  K (ddot & (alpha_ ~ B)) (ftvar alpha_) B.
Proof.
  auto.
Qed.

Example K_star_A_test:
  K  ((alpha_ ~ A) & ddot) (ptype (ftvar alpha_)) B.
Proof.
  auto.
Qed.

Example K_B_A_test:
  K ddot cint A.
Proof.
  constructor.
  auto.
Qed.

Example K_cross_test:
  K ddot (cross cint (cross cint cint)) A.
Proof.
  auto.
Qed.

Example K_arrow_test:
 K ddot (arrow cint (cross cint cint)) A.
Proof.
  auto.
Qed.

Example K_ptype_test:
  K ddot (ptype cint) B.
Proof.
  auto.
Qed.

Example K_utype_test:
  K ddot (utype A cint) A.
Proof.
  auto.
  (* apply_fresh_from* K_utype with fv_of_goal. *)
Qed.

(* Restart here on automation *)
Example K_utype_test_fresh:
  ok (ddot & (beta_ ~ B)) ->
  K (ddot & (beta_ ~ B)) (utype k (ftvar beta_)) A.
Proof.
  intros.
  auto.
  apply_fresh_from* K_utype with fv_of_kinding_goal.
  (* apply_fresh_from* K_utype with fv_of_goal. *)
Qed.

Example K_etype_test:
  K ddot (etype witnesschanges k cint) A.
Proof.
  auto.
  (* apply_fresh_from* K_etype with fv_of_goal. *)
Qed.

(* Test AK *)

Example AK_K_AK_test:
  AK ddot cint A.
Proof.
 auto.
Qed.

Example AK_A_test:
  AK ((alpha_ ~ B) & ddot) (ftvar alpha_) A.
Proof.
  auto.
Qed.

(* Test assgn *)

Example ASGN_cint_test:
  ASGN nil cint.
Proof.
  auto. 
Qed.


Example ASGN_B_test:
  ASGN ((alpha_ ~ B) & ddot) (ftvar alpha_).
Proof.
  auto.
Qed.

Example ASGN_ptype_test:
  ASGN nil (ptype cint).
Proof.
  constructor.
Qed.

Example ASGN_cross_test:
  ASGN nil (cross cint (cross cint cint)).
Proof.
  auto.
Qed.

Example ASGN_arrow_test:
  ASGN nil (arrow cint (cross cint cint)).
Proof.
 auto.
Qed.

Example ASGN_utype_test:
  ASGN ddot (utype k cint).
Proof.
  auto.
  (* apply_fresh_from* ASGN_utype with fv_of_goal. *)
Qed.

Example ASGN_etype_test:
  ASGN ddot (etype witnesschanges k cint).
Proof.
  auto.
  (* apply_fresh_from* ASGN_etype with fv_of_goal. *)
Qed.

(* Test WFDG *)

Example WFD_ddot_gdot_test:
  WFDG ddot gdot.
Proof.
  auto.
Qed.

Example WFD_Delta_nil_test:
  WFDG ddot (gdot & (varx ~ cint)).
Proof.
  auto.
Qed.

(* Test WFU. *)

Example WFU_nil_test:
  WFU udot.
Proof.
  auto.
Qed.

Example WFU_A_test:
  WFU (((varx, pdot) ~p cint) &p udot).
Proof.
  auto.
Qed.

Example WFC_DUG_test:
  WFC ddot udot gdot.
Proof.
  auto.
Qed.

Example WFC:
  varx <> vary ->
  WFC ddot udot (gdot & varx ~ cint & vary ~ cint).
Proof.
  auto.
Qed.