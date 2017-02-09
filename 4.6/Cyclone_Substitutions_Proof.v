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
Require Export Cyclone_K_Lemmas.
Close Scope list_scope.
Import LibEnvNotations.
Import LVPE.LibVarPathEnvNotations.

Lemma get_middle_B:
  forall d alpha0 d' (k : Kappa),
    get alpha0 (d & alpha0 ~ k & d') = Some B ->
    k = B.
Admitted.

Lemma get_middle_A:
  forall d alpha0 d' (k : Kappa),
    get alpha0 (d & alpha0 ~ k & d') = Some A ->
    k = A.
Admitted.

Lemma A_6_Substitution_1:
  forall d d' t k,
    ok (d & d') ->
    AK (d & d') t k ->
    forall alpha t' k',
      ok (d & alpha ~ k & d') ->
      K (d & alpha ~ k & d') t' k' ->
      K (d & d') (T.subst t alpha t') k'.
Proof.
  introv OKd AKd OKda Kd.
  gen_eq G: (d & alpha ~ k & d'). gen d'.
  induction Kd; try solve[simpl; constructor*]; intros; subst.
  simpl.
  case_var.
  apply get_middle_B in H; subst.
  inversions* AKd.
  constructor.
  apply get_subst in H; auto.
  constructor.
  case_var.
  apply get_middle_A in H; subst.
  admit. (* A/B on ftvar. *)
  admit.
  simpl.
  try apply_fresh K_utype; intros.
  assert(NI: y \notin L); auto.
  assert(BU: ok (d & alpha ~ k & d' & y ~ k0)); auto.
  specialize (H0 y NI BU BU (d' & y ~ k0)).
  rewrite <- env_assoc in H0.
  rewrite* <- TP.subst_open_var.
  applys* H0.
  apply* AK_weakening_var.
  rewrite* env_assoc.
  inversions AKd.
  apply K__lc in H2; auto.
  constructor.

  simpl.
  try apply_fresh K_etype; intros.
  assert(NI: y \notin L); auto.
  assert(BU: ok (d & alpha ~ k & d' & y ~ k0)); auto.
  specialize (H0 y NI BU BU (d' & y ~ k0)).
  rewrite <- env_assoc in H0.
  rewrite* <- TP.subst_open_var.
  applys* H0.
  apply* AK_weakening_var.
  rewrite* env_assoc.
  inversions AKd.
  apply K__lc in H2; auto.
  constructor.
Qed.  


(* In order to drive backwards chaining and in general to allow 
  simpler proof, I need an open rec lemma that matches subsitutions. *)

Lemma A_6_Open_1:
  forall d d' t k,
    ok (d & d') ->
    AK (d & d') t k ->
    forall alpha t' k',
      alpha \notin T.fv t' ->
      ok (d & alpha ~ k & d') ->
      K (d & alpha ~ k & d') (T.open_rec 0 (ftvar alpha) t') k' ->
      K (d & d') (T.open_rec 0 t t') k'.
Proof.
  intros.
  rewrite TP.subst_intro with (alpha:= alpha); auto.
  apply  A_6_Substitution_1 with (k:= k); auto.
  inversion* H0.
  apply K__lc with (d:= d&d') (k:=k); auto.
Qed.

Lemma A_6_Substitution_2:
  forall d d' t k,
    ok (d & d') ->
    AK (d & d') t k ->
    forall alpha t' k',
      ok (d & alpha ~ k & d') ->
      AK (d & alpha ~ k & d') t' k' ->
      AK (d & d') (T.subst t alpha t') k'.
Proof.
  introv okd AKd okda AKda.
  inversions *AKda.
  constructor.
  apply A_6_Substitution_1 with (k:=k); auto.
  destruct(classicT(alpha0 = alpha)).
  simpl.
  case_var*.
  assert(k = A).
  apply get_middle_k with (d:=d) (alpha:=alpha0)(d':=d'); auto.
  subst*.
  simpl.
  case_var.
  apply AK_A.
  apply get_middle_strength with (alpha:=alpha) (k:=k); auto.
Qed.

Lemma get_middle_strength:
  forall A alpha0 (d : env A) alpha k d' k', 
    alpha0 <> alpha ->
    get alpha0 (d & alpha ~ k & d') = Some k' ->
    get alpha0 (d & d') = Some k'.
Admitted.
Ltac get_middle_strength:=
match goal with 
  | H: get ?alpha0 (?d & ?alpha' ~ ?k' & ?d') = Some _ |- 
    get ?alpha0 (?d & ?d') = Some _
    => apply get_middle_strength with (alpha:=alpha') (k:=k'); auto
end.
Hint Extern 2 (get _ (_ & _) = Some _) => try get_middle_strength.

Lemma A_6_Substitution_3:
  forall d d' t k,
    ok (d & d') ->
    AK (d & d') t k ->
    forall alpha t',
      ok (d & alpha ~ k & d') ->
      ASGN (d & alpha ~ k & d') t' ->
      ASGN (d & d') (T.subst t alpha t').
Proof.
  introv OKd AKd OKda ASGNd.
  gen_eq G: (d & alpha ~ k & d'). gen d'.
  induction ASGNd; try solve[simpl; try constructor*]; intros; subst.
  destruct(classicT(alpha = alpha0)); try solve[simpl; case_var*].
  subst; simpl; case_var.
  apply get_middle_k in H; subst; auto.
  admit.

  simpl.
  apply_fresh ASGN_utype.
  assert(NI: y \notin L); auto.
  assert(BOK: ok (d & alpha ~ k & d' & y ~ k0));auto.
  specialize (H0 y NI BOK d' OKd AKd).
(* Bad inductive hypothesis! d & alpha ~ k & d' & y ~ k0 = d & alpha ~ k & d' *)  
  admit.
Admitted.

Lemma A_6_Substitution_4:
  forall d d' t k,
    ok (d & d') ->
    AK (d & d') t k ->
    forall alpha g,
      ok (d & alpha ~ k & d') ->
      WFDG (d & alpha ~ k & d') g.
  (*->      WFDG (d & d') (T.subst t alpha g). *)
Admitted.

Lemma A_6_Substitution_5:
  forall d d' t k,
    ok (d & d') ->
    AK (d & d') t k ->
    forall alpha u g,
      ok (d & alpha ~ k & d') ->
      WFC (d & alpha ~ k & d') u g.
(*->    WFC (d & d') u (T.subst t alpha g). *)  
Admitted.

Lemma A_6_Substitution_6:
  forall d d' t k,
    ok (d & d') ->
    AK (d & d') t k ->
    forall alpha s,
      ret s ->
      ret (TTM.subst_st t alpha s).
Proof.
  introv OKd AKd retd.
  induction retd; try solve[simpl; constructor*].
  (* But why does the try solve make it work? *)
Qed.
  
Lemma A_6_Substitution_7:
  forall d d' t k,
    ok (d & d') ->
    AK (d & d') t k ->
    forall u,
      WFU u ->
      forall x p t1 p' t2, 
        gettype u x p t1 p' t2 ->
        forall alpha, 
          gettype u x p (T.subst t alpha t1) p' (T.subst t alpha t2).
Proof.
  introv OKd AKd WFUd gettyped.
  induction gettyped; intros.
  constructor.
Admitted.
  
  
Lemma A_6_Substitution_8_ltyp:
  forall d d' t k,
    ok (d & d') ->
    AK (d & d') t k ->
    forall alpha u g e t',
      ltyp (d & alpha ~ k & d') u g e t' ->
      ltyp (d & d') u g (TTM.subst_e t alpha e) (T.subst t alpha t').
  (* G must be substituted. *)
Admitted.

Lemma A_6_Substitution_8_rtyp:
  forall d d' t k,
    ok (d & d') ->
    AK (d & d') t k ->
    forall alpha u g e t',
      rtyp (d & alpha ~ k & d') u g e t' ->
      rtyp (d & d') u g (TTM.subst_e t alpha e) (T.subst t alpha t').
  (* G must be substituted. *)
Admitted.

Lemma A_6_Substitution_8_styp:
  forall d d' t k,
    ok (d & d') ->
    AK (d & d') t k ->
    forall alpha u g e t',
      styp (d & alpha ~ k & d') u g e t' ->
      styp (d & d') u g (TTM.subst_st t alpha e) (T.subst t alpha t').
  (* G must be substituted. *)    
Admitted.

(*  Old attempts *)
(*
Lemma A_6_Subsititution_1:
  forall d d' t k,
      ok (d & d') ->
      K (d & d') t k ->
      forall alpha t' k',
        ok (d & alpha ~ k & d') ->
        K (d & alpha ~ k & d') t' k' ->
        K (d & d') (T.subst t alpha t') k'.
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


Lemma A_6_Subsititution_1':
  forall d d' t k,
      ok (d & d') ->
      AK (d & d') t k ->
      forall alpha t' k',
        ok (d & alpha ~ k & d') ->
        K (d & alpha ~ k & d') t' k' ->
        K (d & d') (T.subst t alpha t') k'.

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
  forall d d' t k,
      ok (d & d') ->
      AK (d & d') t k ->
      forall alpha t' k,
        ok (d & alpha ~ k & d') ->
        ASGN (d & alpha ~ k & d') t' ->
        ASGN (d & d') (T.subst t alpha t').
Proof.
  introv okdd' ASGNdd' OKdakd' ASGNdakd'.
  gen_eq G: (d & alpha ~ k & d'). gen d'.
(*
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
*)
(*
  rewrite <- ok_commutes in H0.
  assert(ASGNB: ASGN (d & (d' & y ~ k0)) t). admit. (* asgn commutes, commits *)
  assert(H1: d & alpha ~ k & d' & y ~ k0 = d & alpha ~ k & (d' & y ~ k0)). admit.
  specialize (H0 OKL ASGNB H1).
  rewrite <- TP.subst_open_var.
*)
Admitted.
*)