(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Typing Well Formedness

*)

Set Implicit Arguments.
Require Export Cyclone_Formal_Syntax Cyclone_Static_Semantics_Kinding_And_Context_Well_Formedness.
Require Export Cyclone_Static_Semantics_Typing_Heap_Objects.
Require Export Cyclone_Classes Cyclone_Inductions Cyclone_LN_Tactics Cyclone_LN_Extra_Lemmas_And_Automation.
Require Export Cyclone_WFC_Lemmas.
Require Export Cyclone_WFU_Lemmas.
Require Export Cyclone_Context_Weakening_Proof.
Require Export Cyclone_Substitutions_Proof.
Require Export Cyclone_LN_Types_Lemmas.
Require Export Cyclone_Get_Lemmas.
Require Export Cyclone_Return_Preservation_Proof.
Require Export Cyclone_Admit_Environment.
Require Export Case.
Close Scope list_scope.
Import LibEnvNotations.
Import LVPE.LibVarPathEnvNotations.

Ltac invert_bad_B_K_goal:=
  match goal with
  | H: K _ (etype _ _ _) B |- _ =>
    try solve[inversions* H]
  | H: K _ (cross _ _) B |- _ =>
    try solve[inversions* H]
  end.
Hint Extern 1 (K _ _ _) => try invert_bad_B_K_goal.

Ltac ok_d_empty :=
  match goal with
  | H: ok ?d |- ok (?d & empty) =>
    rewrite* drop_empty
  end.
Hint Extern 1 (ok (_ & empty)) => ok_d_empty.

Ltac ok_d_alpha_k_empty :=
  match goal with
  | H: ok ?d |- ok (?d & ?alpha ~ ?k & empty) =>
    rewrite* drop_empty
  end.
Hint Extern 2 (ok (_ & _ ~ _ & empty)) => ok_d_alpha_k_empty.

Lemma show_dan:
 forall d tau'', 
   WFD d -> 
   K d tau'' A ->
  forall d', 
    WFD d' ->
    extends d d' ->
    K d' tau'' B.
Proof.
  introv WFDd Kd.
  induction Kd; intros; auto.
  admit.
  admit.
  apply K_ptype.
  apply K_weakening with (d:=d); auto.
  admit.
  admit.
Admitted.

Lemma A_7_Typing_Well_Formedness_1:
  forall u,
    WFU u ->
    forall x p t p' t',
      gettype u x p t p' t' ->
      forall d,
        ok d  ->
        K d t A ->
        K d t' A.
Proof.
    introv WFUd gettyped.
    induction gettyped; auto; intros.
    Case "zero_pe".
     apply* IHgettyped.
     inversions* H0.
    Case "one_pe".
     apply* IHgettyped.
     inversions* H0.
    Case "etype".
     apply* IHgettyped.
     inversions* H1; subst.
     assert(K empty tau'' A); auto. 
     (* t0 from thesis is tau'. *)
     apply A_1_Context_Weakening_2 with (x:=x) (p:=p) (d:=d) (tau:= tau'') in WFUd; auto.
     rewrite (add_empty_delta d).
     pick_fresh alpha.
     apply A_6_Open_1 with (alpha:= alpha) (k:= k); try rewrite* drop_empty; auto.
     constructor*.
     destruct k.
     admit.
     auto.
Admitted.

Ltac inversion_K_B :=
  match goal with
    | H : K _ (cross _ _) B |- _ => try solve[inversion H]
    | H : K _ (arrow _ _) B |- _ => try solve[inversion H]
  end.

Ltac forwards_ih :=
  match goal with
  | A: ?x, H: ?x -> WFC _ _ _ /\ K _ _ _ |- _ =>
    forwards*: H
  end.

Ltac invert_and :=
  match goal with
  | H : _ /\ _ |- _ => inversions* H
  end.

Ltac invert_complex_K :=
  match goal with
  | H : K _ (_ _ _) _ |- _ => inversions* H
  end.

(* Restart Here: This is fundamentally just K automation. K_constructors is a failure, 
need a case per K constructor that is guaranteed. *)

Ltac WFC_in_goal_and_context_conjuction :=
  match goal with
  | H : WFC ?d ?u ?g /\ _ |- WFC ?d ?u ?g /\ _ =>
    inversions* H; split*
  | H : WFC ?d ?u ?g |- WFC ?d ?u ?g /\ _ =>
    split*
  end.

Ltac invert_bad_B :=
  match goal with
  | H: K ?d (cross ?t0 ?t1) B |- _ =>  inversion H
  | H: K ?d (arrow ?t0 ?t1) B |- _ =>  inversion H
  end.

Ltac K_cross :=
  match goal with
  | H: K ?d (cross ?t0 ?t1) A |- K ?d ?t0 A =>
   inversions* H; try solve[invert_bad_B]
  | H: K ?d (cross ?t0 ?t1) A |- K ?d ?t1 A =>
   inversions* H; try solve[invert_bad_B]
 end.

Ltac K_ptype :=
  match goal with
  | H: K ?d ?t0 A |- K ?d (ptype ?t0) A =>
    apply K_B_A; apply* K_ptype
  end.

Ltac inversions_on_complex_ret :=
  match goal with
    | H: ret (_ _ _ _) |- _ => inversions* H
    | H: ret (_ _ _)   |- _ => inversions* H
    | H: ret (_ _)     |- _ => inversions* H
  end.

Function A_7_Typing_Well_Formedness_Prop_ltyp 
         (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau)
         (st : ltyp d u g e t) := 
    (WFC d u g /\ K d t A).
Hint Unfold A_7_Typing_Well_Formedness_Prop_ltyp.

Function A_7_Typing_Well_Formedness_Prop_rtyp 
         (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau)
         (st : rtyp d u g e t) := 
  (WFC d u g /\ K d t A).
Hint Unfold A_7_Typing_Well_Formedness_Prop_rtyp.

Function A_7_Typing_Well_Formedness_Prop_styp 
         (d : Delta) (u : Upsilon) (g : Gamma) (s : St) (t : Tau)
         (st : styp d u g s t) := 
   WFC d u g /\
   (ret s -> K d t A).
Hint Unfold A_7_Typing_Well_Formedness_Prop_styp.

Lemma env_comm_3:
  forall A (E : env A) F G,
    E & F & G = E & G & F.
Admitted.

Lemma WFDG__K_A:
  forall g d alpha tau,
    WFDG d (g & alpha ~ tau) ->
    K d tau A.
Proof.
  intros g.
  induction g using env_ind; intros.
  inversions *H.
  apply empty_not_constructed in H0.
  inversion H0.
  apply eq_inversion_env in H0.
  inversion H0.
  inversion H5.
  subst*.
  apply IHg with (alpha:=x).
Admitted.

Lemma WFC_types_in_g_K_A:
  forall d u g alpha tau,
      WFC d u (g & alpha ~ tau) -> 
      K d tau A.
Proof.
  introv WFCd.
  inversions* WFCd.
  induction g using env_ind.
  inversions* H.
  apply empty_not_constructed in H1.
  contradiction.
  apply eq_inversion_env in H1.
  inversion H1.
  inversion H6.
  subst*.
  apply IHg.
  assert(x <> alpha). admit.
  assert(x # g). admit.
  assert(alpha # g). admit.
  rewrite env_comm_3 in H.
  apply WFDG_strength with (alpha:=x) (tau:=v); auto.
  admit. (* bug? *)
  unfolds.
  unfolds in H3.
  unfold fv_gamma.
  (* not so easy *)
Admitted.

(* This is a problem, will not Ltac and apply right. *)
(*
Ltac A_7_Typing_Well_Formedness_proof u x p tau' H H0 H1 H2 H3 alpha:=
    autounfold; intros; subst; try solve[auto];
      try solve[intuition];
      try WFC_in_goal_and_context_conjuction; intros;
      try solve[K_cross];
      try solve[K_ptype];
      try solve[inversions_on_complex_ret];
      try solve[apply A_7_Typing_Well_Formedness_1 with (u:=u)(x:=x)(p:=nil)(p':=p)(t:=tau'); auto];
  Case "let";
   inversions* H0;
   pick_fresh alpha;
   assert(NI: alpha \notin L); auto;
   specialize (H alpha NI);
   inversion H;
   apply* H3.

  Case "arrow".
   inversion H.
   inversions* H3.
   inversion H4.
  Case "utype SR 3.11".
   inversions* H1; try solve[inversion H].
   pick_fresh alpha.
   rewrite (add_empty_delta d).
   apply A_6_Open_1 with (k:= k) (alpha:= alpha); try rewrite drop_empty; auto.
  Case "etype".
   split*.
   pick_fresh alpha.
   assert(NI: alpha \notin L); auto.
   apply* H.
  Case "arrow SR3.13".
   pick_fresh alpha.
   assert(NI: alpha \notin L); auto.
   specialize (H alpha NI).
   inversion H.
   split*.
   apply WFC_strength with (alpha:=alpha) (tau:=tau); auto.
   apply K_arrow.
   apply WFC_types_in_g_K_A with (u:=u) (g:=g) (alpha:=alpha); auto.
   apply* H1.
  Case "utype".
   apply_fresh K_utype; intros.
   apply* H.
*)

Lemma A_7_Typing_Well_Formedness_2_ltyp:
  forall (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) (ty : ltyp d u g e t),
   A_7_Typing_Well_Formedness_Prop_ltyp ty.
Proof.
  autounfold in *.
  apply (ltyp_ind_mutual 
           A_7_Typing_Well_Formedness_Prop_styp
           A_7_Typing_Well_Formedness_Prop_ltyp
           A_7_Typing_Well_Formedness_Prop_rtyp);
    autounfold; intros; subst; try solve[auto];
      try solve[intuition];
      try WFC_in_goal_and_context_conjuction; intros;
      try solve[K_cross];
      try solve[K_ptype];
      try solve[inversions_on_complex_ret];
      try solve[apply A_7_Typing_Well_Formedness_1 with (u:=u)(x:=x)(p:=nil)(p':=p)(t:=tau'); auto].
  Case "let".
   inversions* H0.
   pick_fresh alpha.
   assert(NI: alpha \notin L); auto.
   specialize (H alpha NI).
   inversion H.
   apply* H3.
  Case "arrow".
   inversion H.
   inversions* H3.
   inversion H4.
  Case "utype SR 3.11".
   inversions* H1; try solve[inversion H].
   pick_fresh alpha.
   rewrite (add_empty_delta d).
   apply A_6_Open_1 with (k:= k) (alpha:= alpha); try rewrite drop_empty; auto.
  Case "etype".
   split*.
   pick_fresh alpha.
   assert(NI: alpha \notin L); auto.
   apply* H.
  Case "arrow SR3.13".
   pick_fresh alpha.
   assert(NI: alpha \notin L); auto.
   specialize (H alpha NI).
   inversion H.
   split*.
   apply WFC_strength with (alpha:=alpha) (tau:=tau); auto.
   apply K_arrow.

   apply WFC_types_in_g_K_A with (u:=u) (g:=g) (alpha:=alpha); auto.
   apply* H1.
  Case "utype".
   apply_fresh K_utype; intros.
   apply* H.
Qed.

Lemma A_7_Typing_Well_Formedness_2_rtyp:
  forall (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) (ty : rtyp d u g e t),
   A_7_Typing_Well_Formedness_Prop_rtyp ty.
Proof.
  autounfold in *.
  apply (rtyp_ind_mutual 
           A_7_Typing_Well_Formedness_Prop_styp
           A_7_Typing_Well_Formedness_Prop_ltyp
           A_7_Typing_Well_Formedness_Prop_rtyp);
    autounfold; intros; subst; try solve[auto];
      try solve[intuition];
      try WFC_in_goal_and_context_conjuction; intros;
      try solve[K_cross];
      try solve[K_ptype];
      try solve[inversions_on_complex_ret];
      try solve[apply A_7_Typing_Well_Formedness_1 with (u:=u)(x:=x)(p:=nil)(p':=p)(t:=tau'); auto].
  Case "let".
   inversions* H0.
   pick_fresh alpha.
   assert(NI: alpha \notin L); auto.
   specialize (H alpha NI).
   inversion H.
   apply* H3.
  Case "arrow".
   inversion H.
   inversions* H3.
   inversion H4.
  Case "utype SR 3.11".
   inversions* H1; try solve[inversion H].
   pick_fresh alpha.
   rewrite (add_empty_delta d).
   apply A_6_Open_1 with (k:= k) (alpha:= alpha); try rewrite drop_empty; auto.
  Case "etype".
   split*.
   pick_fresh alpha.
   assert(NI: alpha \notin L); auto.
   apply* H.
  Case "arrow SR3.13".
   pick_fresh alpha.
   assert(NI: alpha \notin L); auto.
   specialize (H alpha NI).
   inversion H.
   split*.
   apply WFC_strength with (alpha:=alpha) (tau:=tau); auto.
   apply K_arrow.
   apply WFC_types_in_g_K_A with (u:=u) (g:=g) (alpha:=alpha); auto.
   apply* H1.
  Case "utype".
   apply_fresh K_utype; intros.
   apply* H.
Qed.

Lemma A_7_Typing_Well_Formedness_2_styp:
  forall (d : Delta) (u : Upsilon) (g : Gamma) (s : St) (t : Tau) (ty : styp d u g s t),
   A_7_Typing_Well_Formedness_Prop_styp ty.
Proof.
  autounfold in *.
  apply (styp_ind_mutual 
           A_7_Typing_Well_Formedness_Prop_styp
           A_7_Typing_Well_Formedness_Prop_ltyp
           A_7_Typing_Well_Formedness_Prop_rtyp);
    autounfold; intros; subst; try solve[auto];
      try solve[intuition];
      try WFC_in_goal_and_context_conjuction; intros;
      try solve[K_cross];
      try solve[K_ptype];
      try solve[inversions_on_complex_ret];
      try solve[apply A_7_Typing_Well_Formedness_1 with (u:=u)(x:=x)(p:=nil)(p':=p)(t:=tau'); auto].
  Case "let".
   inversions* H0.
   pick_fresh alpha.
   assert(NI: alpha \notin L); auto.
   specialize (H alpha NI).
   inversion H.
   apply* H3.
  Case "arrow".
   inversion H.
   inversions* H3.
   inversion H4.
  Case "utype SR 3.11".
   inversions* H1; try solve[inversion H].
   pick_fresh alpha.
   rewrite (add_empty_delta d).
   apply A_6_Open_1 with (k:= k) (alpha:= alpha); try rewrite drop_empty; auto.
  Case "etype".
   split*.
   pick_fresh alpha.
   assert(NI: alpha \notin L); auto.
   apply* H.
  Case "arrow SR3.13".
   pick_fresh alpha.
   assert(NI: alpha \notin L); auto.
   specialize (H alpha NI).
   inversion H.
   split*.
   apply WFC_strength with (alpha:=alpha) (tau:=tau); auto.
   apply K_arrow.
   apply WFC_types_in_g_K_A with (u:=u) (g:=g) (alpha:=alpha); auto.
   apply* H1.
  Case "utype".
   apply_fresh K_utype; intros.
   apply* H.
Qed.