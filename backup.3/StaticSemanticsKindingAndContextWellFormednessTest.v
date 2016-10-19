(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

 This defines the static semantics of statements and expressions, pg. 63. 

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.

Require Export FormalSyntax.
Require Export StaticSemanticsKindingAndContextWellFormedness.
Require Import Tacticals.
Require Import TestUtilities.

(* Test K *)

(* TODO: am I really testing anything if I've got types that only
  go down to cint. I'd guess so. *)

Example K_int_test:
  K [] cint B.
Proof.
 apply K_int.
Qed.

Example K_B_test:
  K [(alpha, B)] (tv_t alpha) B.
Proof.
  (* eapply K_B. but it needs context adjustment. *)
  eauto 10 with Chapter3.
Qed.

Example K_star_A_test:
  K  [(alpha, A)] (ptype (tv_t alpha)) B.
Proof.
  (* apply K_star_A. *)
  eauto 10 with Chapter3.
Qed.

Example K_B_A_test:
  K [] tau A.
Proof.
 apply K_B_A.
 eauto 10 with Chapter3.
Qed.

Example K_cross_test:
  K [] (cross t0 t1) A.
Proof.
 apply K_cross;
 eauto 10 with Chapter3.
Qed.

Example K_arrow_test:
 K [] (arrow t0 t1) A.
Proof.
 apply K_arrow;
 eauto 10 with Chapter3.
Qed.

Example K_A_B_test:
  K [] (ptype tau) B.
Proof.
 apply K_A_B.
 eauto 10 with Chapter3.
Qed.

Example K_utype_test:
  K [] (utype alpha k tau) A.
Proof.
 apply K_utype;
 eauto 10 with Chapter3.
Qed.

Example K_etype_test:
  K [] (etype nowitnesschange alpha k tau) A.
Proof.
 apply K_etype.
 eauto 10 with Chapter3.
 eauto 10 with Chapter3.
Qed.

(* Test AK *)

Example AK_K_AK_test:
  AK [] tau k.
Proof.
 apply AK_K_AK.
 eauto 10 with Chapter3.
Qed.

Example AK_A_test:
  AK [] (tv_t alpha) A.
Proof.
 apply AK_A.
Qed.

(* Test assgn *)

Example ASGN_cint_test:
  ASGN [] cint.
Proof.
 apply ASGN_cint.
Qed.

Example ASGN_B_test:
  ASGN [(alpha, B)] (tv_t alpha).
Proof.
  (* apply ASGN_B. *)
  eauto 10 with Chapter3.
Qed.

Example ASGN_ptype_test:
  ASGN [] (ptype tau).
Proof.
 apply ASGN_ptype.
Qed.

Example ASGN_cross_test:
  ASGN [] (cross t0 t1).
Proof.
 apply ASGN_cross;
 eauto 10 with Chapter3.
Qed.

Example ASGN_arrow_test:
  ASGN [] (arrow t0 t1).
Proof.
 apply ASGN_arrow;
 eauto 10 with Chapter3.
Qed.

Example ASGN_utype_test:
  ASGN [] (utype alpha k tau).
Proof.
 apply ASGN_utype.
 eauto 10 with Chapter3.
Qed.

Example ASGN_etype_test:
  ASGN [] (etype nowitnesschange alpha k tau).
Proof.
 apply ASGN_etype.
 eauto 10 with Chapter3.
Qed.

(* Test WFDG *)

Example WFD_nil_nil_test:
  WFDG [] [].
Proof.
 apply WFDG_d_nil.
Qed.

(* Bug 14, wrong rule. *)
Example WFD_Delta_nil_test:
  WFDG [] [(x,tau)].
Proof.
  (* apply WFDG_xt;  *)
  eauto 10 with Chapter3.
Qed.

(* Test WFU. *)

Example WFU_nil_test:
  WFU [].
Proof.
 apply WFU_nil.
Qed.

Example WFU_A_test:
  WFU [(p_e x nil, tau)].
Proof.
  (* apply WFU_A; *)
 eauto 10 with Chapter3.
Qed.

Example WFC_DGU_test:
  WFC [] [] [].
Proof.
 apply WFC_DGU;
 eauto 10 with Chapter3.
Qed.
