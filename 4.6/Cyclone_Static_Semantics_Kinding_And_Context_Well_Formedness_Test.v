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
Require Export Cyclone_LN_Extra_Lemmas_And_Automation.
Close Scope list_scope.
Import LibEnvNotations.
Import LVPE.LibVarPathEnvNotations.

(* Test K *)

Example K_int_test:
  K empty cint B.
Proof.
  auto.
Qed.

Example K_B_test:
  K (empty & (alpha_ ~ B)) (ftvar alpha_) B.
Proof.
  K_constructors.
  simpl_get.
Qed.

Example K_star_A_test:
  K  (empty & (alpha_ ~ A)) (ptype (ftvar alpha_)) B.
Proof.
  K_constructors.
  rewrite get_push.
  case_var*.
Qed.

Example K_B_A_test:
  K empty cint A.
Proof.
  constructor.
  auto.
Qed.

Example K_cross_test:
  K empty (cross cint (cross cint cint)) A.
Proof.
  auto.
Qed.

Example K_arrow_test:
 K empty (arrow cint (cross cint cint)) A.
Proof.
  auto.
Qed.

Example K_ptype_test:
  K empty (ptype cint) B.
Proof.
  auto.
Qed.

Example K_utype_test:
  K empty (utype A cint) A.
Proof.
  auto.
  (* apply_fresh_from* K_utype with fv_of_goal. *)
Qed.


Example K_utype_test_fresh:
  ok (empty & (beta_ ~ B)) ->
  K (empty & (beta_ ~ B)) (utype B (ftvar beta_)) A.
Proof.
  auto.
  (* apply_fresh_from* K_utype with fv_of_goal. *)
Qed.

Example K_etype_test:
  K empty (etype witnesschanges k cint) A.
Proof.
  auto.
  (* apply_fresh_from* K_etype with fv_of_goal. *)
Qed.

(* Test AK *)

Example AK_K_AK_test:
  AK empty cint A.
Proof.
 auto.
Qed.

Example AK_A_test:
  AK ((alpha_ ~ B) & empty) (ftvar alpha_) A.
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
  ASGN ((alpha_ ~ B) & empty) (ftvar alpha_).
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
  ASGN empty (utype k cint).
Proof.
  auto.
  (* apply_fresh_from* ASGN_utype with fv_of_goal. *)
Qed.

Example ASGN_etype_test:
  ASGN empty (etype witnesschanges k cint).
Proof.
  auto.
  (* apply_fresh_from* ASGN_etype with fv_of_goal. *)
Qed.

(* Test WFDG *)

Example WFD_empty_empty_test:
  WFDG empty empty.
Proof.
  auto.
Qed.

Example WFD_Delta_nil_test:
  WFDG empty (empty & (varx ~ cint)).
Proof.
  auto.
Qed.

(* Test WFU. *)

Example WFU_nil_test:
  WFU LVPE.V.empty.
Proof.
  auto.
Qed.

Example WFU_A_test:
  WFU (LVPE.V.empty &p ((varx, pdot) ~p cint)).
Proof.
  auto.
Qed.

Example WFC_DUG_test:
  WFC empty LVPE.V.empty empty.
Proof.
  auto.
Qed.

Lemma WFC_weakening_automation:
  forall d u g y tau, 
    y \notin (fv_delta d) \u (fv_upsilon u) \u (fv_gamma g) ->
    WFC d u g ->
    WFC d u (g & (y ~ tau)).
Proof.
  intros.
  inversion H0; subst.
  inversion H1; subst.
  auto.
  auto.
Admitted.

Lemma WFC_automation:
  forall d u g y tau,
  WFC d u g ->
  y \notin fv_gamma g ->
  WFC d u (g & y ~ tau).
Proof.
(*
  intros.
  solve_wf.
  apply WFDG_K with (u0:= u0) (g0:=g0) (y:= y).
  constructor*.
  inversion* H.
*)
 Admitted.

Lemma ok_empty:
  ok (@empty Tau).
Proof.
  auto.
Qed.

Example WFC_test:
  varx <> vary ->
  WFC empty LVPE.V.empty (empty & varx ~ cint & vary ~ cint).
Proof.
  intros.
  auto.
Qed.

Lemma test_auto: 
  forall (d : Delta) (u : Upsilon) g x tau, 
    WFC d u (g & x ~ tau).
Proof.
  intros.
Admitted. (* Wont solve, loops as it knows nothing. *)

