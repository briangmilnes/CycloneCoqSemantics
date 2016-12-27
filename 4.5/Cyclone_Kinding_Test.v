(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION".   Daniel Grossman, August 2003 *)
(* Testing some aspects of Kinding. *)
(* Brian Milnes 2016 *)

Set Implicit Arguments.
Require Export Cyclone_Dynamic_Semantics Cyclone_Static_Semantics_Kinding_And_Context_Well_Formedness Cyclone_LN_Tactics.
Require Export Cyclone_Test_Utilities.
Close Scope list_scope.
Import LibEnvNotations.
Import LVPE.LibVarPathEnvNotations.

(* Dan says, pg 65, we cannot derive \Delta, \alpha : A |-k- \alpha : \Kappa we we
   can derive \Delta, \alpha : A |-k- \alpha *: B.  

   Let's prove this as I'm worried that he means Figure 3.6 
        \Delta |-k- \tau : B -> \Delta |-k- tau : A 
   is only to be applied to concrete types. 

  Or does he have a K for AK ? 

*)

Example alpha_star_B :
    K ((alpha_ ~ A) & empty) (ptype (ftvar alpha_)) B.
Proof.
  auto.
Qed.

(* Which invalidates the return progress theorem unless it's type is
  restricted. This explains a lot. *)

Lemma can_K_alpha :
  exists (d : Delta) (alpha : var) (k1 k2 : Kappa),
    K ((alpha ~ k1) & d) (ftvar alpha) k2.
Proof.
  apply ex_intro with (x:= empty).
  apply ex_intro with (x:= varx).
  apply ex_intro with (x:= B).
  apply ex_intro with (x:= B).
  auto.
Qed.

Lemma can_K_alpha_A :
  exists (d : Delta) (alpha : var) (k1 k2 : Kappa),
    K ((alpha ~ k1) & d) (ftvar alpha) k2.
Proof.
  apply ex_intro with (x:= empty).
  apply ex_intro with (x:= varx).
  apply ex_intro with (x:= B).
  apply ex_intro with (x:= A).
  auto.
Qed.

Lemma can_AK_alpha :
  ~ exists (k1 k2 : Kappa),
      AK ((alpha_ ~ k1) & empty) (ftvar alpha_) k2.
Proof.
  unfold not.
  intros.
  destruct H as [k1]; destruct H as [k2]; destruct k1; destruct k2; 
  try inversion H; try inversion H0.
  admit.
  inversion H.
  simpl in H3.
Admitted.

Lemma can_AK_alpha_A :
  exists (d : Delta) (alpha : var) (k1 k2 : Kappa),
    K ((alpha_ ~ k1) & empty) (ftvar alpha_) k2.
Proof.
  apply ex_intro with (x:= empty).
  apply ex_intro with (x:= varx).
  apply ex_intro with (x:= B).
  apply ex_intro with (x:= A).
  auto.
Qed.


   