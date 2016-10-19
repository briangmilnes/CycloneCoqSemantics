(* Then try with extends1 step. *)
(* This is going to work but it requires new lemmas, can I use
  the more general extends more simply? *)
(*
Inductive Extends1D : TV.T -> Kappa -> Delta -> Delta -> Prop := 
  | Extends1D_alpha_kappa : 
      forall (alpha : TV.T) (k : Kappa) (d : Delta) (d' : Delta), 
      d' = ([(alpha,k)] ++ d) ->
      WFD d' ->
      Extends1D alpha k d d'.
*)        

Lemma A_6_Substitution_1:
  forall (d : Delta) (tau : Tau) (k : Kappa),
      D.nodup d = true ->
      AK d tau k ->
      forall (d' : Delta) (k' : Kappa) (tau' : Tau), 
        D.nodup d' = true ->
        K d' tau' k' ->
        forall (alpha : TV.T),
          D.extends1 d alpha k d' = true ->
          K d (subst_Tau tau' tau alpha) k'.
Proof.
  intros d tau k nodupd AKder d' k' tau' nodupd' Kder.
  K_ind_cases(induction Kder) Case; intros.
 Case "K d cint B".
  simpl.
  constructor.
 Case "K d (tv_t alpha) B".
  unfold D.extends1 in H0.
  case_eq(D.map d0 alpha0); intros; rewrite H1 in H0; try solve[inversion H0];
  case_eq(D.map d alpha0); intros; rewrite H2 in H0; try solve[inversion H0];
  unfold subst_Tau.
  case_eq(TV.beq_t alpha0 alpha); intros.
  apply TV.beq_t_eq in H3.
  subst.
  rewrite H1 in H.
  inversion H.
  constructor; try assumption.
  rewrite D.equal_sym in H0.
  inversion AKder; subst.
  apply D.equal_eq in H0.
  subst.
  simpl in H1.
  unfold D.K_eq in H1.
  rewrite D.K.beq_t_refl in H1.
  inversion H1.

  apply D.equal_eq in H0.
  subst.
  simpl in H1.
  unfold D.K_eq in H1.
  rewrite D.K.beq_t_refl in H1.
  inversion H1.
(* Suspicious.
  admit.

  apply D.equal_if_map_some with (c:= d0) (c':= d) (k:= alpha) (t:= B) in nodupd; 
    try assumption.
  apply D.equal_if_map_some with (c:= d0) (c':= d) (k:= alpha) (t:= B) in nodupd; 
    try assumption.
*)

 Case "K d (ptype (tv_t alpha)) B".
(* 
  unfold D.extends1 in H0.
  case_eq(D.map d0 alpha0); intros; rewrite H1 in H0; try solve[inversion H0];
  case_eq(D.map d alpha0); intros; rewrite H2 in H0; try solve[inversion H0].
  unfold subst_Tau.
  case_eq(TV.beq_t alpha0 alpha); intros.
  apply TV.beq_t_eq in H3.
  subst.
  rewrite H1 in H.
  inversion H.
  constructor; try assumption.
  rewrite D.equal_sym in H0.
  apply D.equal_if_map_some with (c:= d0) (c':= d) (k:= alpha) (t:= A) in nodupd; 
    try assumption.
*) 
 admit.
 Case "K d tau A".
  apply IHKder with (alpha:= alpha) in nodupd'; try assumption.
  constructor; try assumption.
 Case "K d (cross t0 t1) A".
  unfold subst_Tau.
  fold subst_Tau.
  pose proof H as H'.
  apply IHKder1 in H; try assumption.
  apply IHKder2 in H'; try assumption.
  apply K_cross; try assumption.
 Case "K d (arrow t0 t1) A".
  unfold subst_Tau.
  fold subst_Tau.
  pose proof H as H'.
  apply IHKder1 in H; try assumption.
  apply IHKder2 in H'; try assumption.
  apply K_arrow; try assumption.
 Case "K d (ptype tau) B".
  apply IHKder in H; try assumption.
  unfold subst_Tau.
  fold subst_Tau.
  constructor.
  assumption.
 Case "K d (utype alpha k tau) A".
  unfold subst_Tau.
  fold subst_Tau.
  case_eq(TV.beq_t alpha0 alpha); intros.
  apply TV.beq_t_eq in H2.
  subst.
  unfold D.extends1 in H1.
  subst.
  rewrite H0 in H1.
  case_eq(D.map d alpha); intros; rewrite H2 in H1; try solve[inversion H1].
  apply D.equal_eq in H1.
  subst.
  apply K_utype; try assumption.
  admit. (* d = d0 *)
  admit. (* equal map agreement *)
  (* Even with equal_eq IHK contradicts H1. *)
  admit.
 Case "K d (etype p alpha k tau) A)".
  admit.
Admitted.

(* Try with extends, not equal in extends1. *)
Lemma A_6_Substitution_1':
  forall (d : Delta) (tau : Tau) (k : Kappa),
      WFD d ->
      AK d tau k ->
      forall (d' : Delta) (k' : Kappa) (tau' : Tau) (alpha : TV.T),
        K d' tau' k' ->
        WFD (dctxt alpha k d') ->
        D.extends1' d alpha k d' = true ->
        K d (subst_Tau tau' tau alpha) k'.
Proof.
  intros d tau k WFd AKder d' k' tau' alpha Kder.
  K_ind_cases(induction Kder) Case; intros.
 Case "K d cint B".
  simpl.
  constructor.
 Case "K d (tv_t alpha) B".
  admit.
 Case "K d (ptype (tv_t alpha)) B".
  admit.
 Case "K d tau A".
  apply IHKder in H; try assumption.
  constructor.
  assumption.
 Case "K d (cross t0 t1) A".
  unfold subst_Tau.
  fold subst_Tau.
  pose proof H as H'.
  apply IHKder1 in H; try assumption.
  apply IHKder2 in H'; try assumption.
  apply K_cross; try assumption.
 Case "K d (arrow t0 t1) A".
  unfold subst_Tau.
  fold subst_Tau.
  pose proof H as H'.
  apply IHKder1 in H; try assumption.
  apply IHKder2 in H'; try assumption.
  apply K_arrow; try assumption.
 Case "K d (ptype tau) B".
  apply IHKder in H; try assumption.
  unfold subst_Tau.
  fold subst_Tau.
  constructor; try assumption.
 Case "K d (utype alpha k tau) A".
  unfold subst_Tau.
  fold subst_Tau. 
  case_eq(TV.beq_t alpha alpha0); intros; try rewrite H3.
  apply TV.beq_t_eq in H3.
  subst.
  (* Must invert, can't invert. *)
  admit.
  unfold D.extends1' in H2.
  case_eq(D.map d0 alpha); intros; rewrite H4 in H2; try solve[inversion H2].  
  case_eq(D.map d alpha); intros; rewrite H5 in H2; try solve[inversion H2].
  apply K_utype; try assumption.
  admit.
  admit.
  admit.
 Case "K d (etype p alpha k tau) A)".
  admit.
Admitted.


Lemma A_6_Substitution_1_clean:
  forall (d : Delta) (tau : Tau) (k : Kappa),
      AK d tau k ->
      forall (k' : Kappa) (tau' : Tau) (alpha : TV.T),
        K (dctxt alpha k d) tau' k' ->
        K d (subst_Tau tau' tau alpha) k'.
Admitted.

