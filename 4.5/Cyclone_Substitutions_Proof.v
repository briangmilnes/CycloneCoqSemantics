(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Substitutions 

*)

Set Implicit Arguments.
Require Export Cyclone_Formal_Syntax Cyclone_Static_Semantics_Kinding_And_Context_Well_Formedness.
Require Export Cyclone_Static_Semantics_Typing_Heap_Objects.
Require Export Cyclone_Classes Cyclone_Inductions Cyclone_LN_Tactics Cyclone_LN_Extra_Lemmas_And_Automation.
Require Export Cyclone_Context_Weakening_Proof.
Require Export Cyclone_LN_Types_Lemmas.
Require Export Cyclone_Get_Lemmas.
Require Export Cyclone_Admit_Environment.
Close Scope list_scope.
Import LibEnvNotations.
Import LVPE.LibVarPathEnvNotations.

Lemma A_6_Subsititution_1:
  forall d d' t k,
      ok (d & d') ->
      K (d & d') t k ->
      forall alpha t' k',
        ok (d & alpha ~ k & d') ->
        K (d & alpha ~ k & d') t' k' ->
        K (d & d')  (T.subst t alpha t') k'.
Proof.
  introv okdd' Kd okdakd' Kdakd'.
  gen_eq G: (d & alpha ~ k & d'). gen d'.
  induction Kdakd'; intros; subst; auto.
  simpl.
  case_var.
  apply get_middle_eq_inv in H; subst; auto.
  apply get_subst in H; subst; auto.

  simpl.
  case_var.
  apply K_ptype.
  (* yes k is A! *) 
  admit.
  apply K_star_A.
  admit.

  simpl.
  apply_fresh K_utype.
  intros.
  assert(NI: y \notin L). admit.
  assert(OKB: ok (d & alpha ~ k & d' & y ~ k0)). admit.
  specialize (H y NI OKB).
  specialize (H0 y NI OKB OKB (d' & y ~ k0)).
(*
  rewrite <- ok_commutes in H0.
  rewrite <- K_context_commutes in H0.
  rewrite <- K_context_commutes in H0.
  assert(KW: K (d & d' & y ~ k0) t k). admit. (* k weakening *)
  assert(CC: d & alpha ~ k & d' & y ~ k0 = d & alpha ~ k & (d' & y ~ k0)). admit.
  (* contexts commute, meta theorem I must accept. *)
  specialize (H0 H1 KW CC).
  rewrite* <- TP.subst_open_var.

  apply K__lc with (d:= (d&d')) (k:=k); auto.
  admit.

  apply K_B_A.
  apply* IHKdakd'.
*)
Admitted.

Lemma A_6_Subsititution_2:
  forall d d' t k,
      ok (d & d') ->
      AK (d & d') t k ->
      forall alpha t' k',
        ok (d & alpha ~ k & d') ->
        AK (d & alpha ~ k & d') t' k' ->
        AK (d & d') (T.subst t alpha t') k'.
Proof.
  introv okdd' AKd okdakd' AKdakd'.
  inversions* AKdakd'.
  inversions* AKd.
  constructor.
  apply A_6_Subsititution_1 with (k:=k); auto.
  constructor.
  apply A_6_Subsititution_1 with (k:=A); auto.
  (* bug ? A/B *)
  admit.
  simpl.
  case_var*.
  apply get_middle_eq_inv in H; subst*.
  apply AK_A.
  admit. (* get strengthening. *)
Admitted.

Lemma A_6_Subsititution_3:
  forall d d' t,
      ok (d & d') ->
      ASGN (d & d') t ->
      forall alpha t' k,
        ok (d & alpha ~ k & d') ->
        ASGN (d & alpha ~ k & d') t' ->
        ASGN (d & d') (T.subst t alpha t').
Proof.
  introv okdd' ASGNdd' OKdakd' ASGNdakd'.
  gen_eq G: (d & alpha ~ k & d'). gen d'.
  induction ASGNdakd'; intros; subst; auto; simpl; try solve[constructor; auto];
    try solve[case_var*;
              apply ASGN_B;
              apply get_subst in H; subst; auto].

  apply_fresh ASGN_utype.
  assert(NI: y \notin L). auto.
  specialize (H y NI).
  assert(OKB: ok (d & alpha ~ k & d' & y ~ k0)). admit.
  assert(OKL : ok (d & d' & y ~ k0)); auto.
  specialize (H0 y NI OKB (d' & y ~ k0)).
(*
  rewrite <- ok_commutes in H0.
  assert(ASGNB: ASGN (d & (d' & y ~ k0)) t). admit. (* asgn commutes, commits *)
  assert(H1: d & alpha ~ k & d' & y ~ k0 = d & alpha ~ k & (d' & y ~ k0)). admit.
  specialize (H0 OKL ASGNB H1).
  rewrite <- TP.subst_open_var.
*)
Admitted.