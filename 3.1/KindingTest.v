Set Implicit Arguments.
Require Export LanguageModuleDef.
Require Export DynamicSemanticsTypeSubstitution.
Require Export DynamicSemanticsHeapObjects.
Require Export DynamicSemantics.
Require Export DynamicSemanticsTypeSubstitution.
Require Export StaticSemanticsKindingAndContextWellFormedness.
Require Export StaticSemantics.
Require Export TypeSafety.
Require Export CpdtTactics.
Require Export Case.

(* Dan says, pg 65, we cannot derive \Delta, \alpha : A |-k- \alpha : \Kappa we we
   can derive \Delta, \alpha : A |-k- \alpha *: B.  

   Let's prove this as I'm worried that he means Figure 3.6 
        \Delta |-k- \tau : B -> \Delta |-k- tau : A 
   is only to be applied to concrete types. 

  Or does he have a K for AK ? 

*)

Example alpha_star_B :
    K (dctxt (TV.var 0) A ddot) (ptype (tv_t (TV.var 0))) B.
Proof.
  apply K_star_A. 
  eauto 20 with Chapter3.
Qed.

(* Which invalidates the return progress theorem unless it's type is
  restricted. This explains a lot. *)

Lemma can_K_alpha :
  exists (d : Delta) (alpha : TV.T) (k1 k2 : Kappa),
    K (dctxt alpha k1 d) (tv_t alpha) k2.
Proof.
  apply ex_intro with (x:= ddot).
  apply ex_intro with (x:= (TV.var 0)).
  apply ex_intro with (x:= B).
  apply ex_intro with (x:= B).
  constructor.
  reflexivity.
Qed.

Lemma can_K_alpha_A :
  exists (d : Delta) (alpha : TV.T) (k1 k2 : Kappa),
    K (dctxt alpha k1 d) (tv_t alpha) k2.
Proof.
  apply ex_intro with (x:= ddot).
  apply ex_intro with (x:= (TV.var 0)).
  apply ex_intro with (x:= B).
  apply ex_intro with (x:= A).
  constructor.
  constructor.
  reflexivity.
Qed.

Lemma can_AK_alpha :
  ~ exists (k1 k2 : Kappa),
      AK (dctxt (TV.var 0) k1 ddot) (tv_t (TV.var 0)) k2.
Proof.
  unfold not.
  intros.
  destruct H as [k1]; destruct H as [k2]; destruct k1; destruct k2; 
  try inversion H; try inversion H0; crush.
  admit.
  inversion H.
  simpl in H3.
Admitted.

Lemma can_AK_alpha_A :
  exists (d : Delta) (alpha : TV.T) (k1 k2 : Kappa),
    K (dctxt alpha k1 ddot) (tv_t alpha) k2.
Proof.
  apply ex_intro with (x:= ddot).
  apply ex_intro with (x:= (TV.var 0)).
  apply ex_intro with (x:= B).
  apply ex_intro with (x:= A).
  constructor.
  constructor.
  reflexivity.
Qed.


   