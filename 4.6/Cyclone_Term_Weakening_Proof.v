(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Term Weakening 

*)

Set Implicit Arguments.
Require Export Cyclone_Formal_Syntax Cyclone_Static_Semantics_Kinding_And_Context_Well_Formedness.
Require Export Cyclone_Static_Semantics_Typing_Heap_Objects.
Require Export Cyclone_Classes Cyclone_Inductions Cyclone_LN_Tactics Cyclone_LN_Extra_Lemmas_And_Automation.
Require Export Cyclone_Context_Weakening_Proof.
Require Export Cyclone_LN_Types_Lemmas.
Require Export Cyclone_Gettype_Lemmas.
Require Export Cyclone_WFC_Lemmas.
Close Scope list_scope.
Import LibEnvNotations.
Import LVPE.LibVarPathEnvNotations.

Lemma A_2_Term_Weakening_1 :
  forall (d: Delta) (u u' : Upsilon) (g g' : Gamma)
         (x : var) (p p' : Path) (tau tau' : Tau),
    LVPE.extends u u' ->
    extends g g' ->
    WFC d u g -> 
    WFC d u' g' ->
    gettype u  x p tau p' tau' ->
    gettype u' x p tau p' tau'.
Proof.
  intros.
  unfold LVPE.extends, LVPE.binds in H.
  induction H3; auto.
  apply gettype_etype with (tau'':= tau''); auto.
Qed.

Ltac solve_styp :=
  match goal with
  | H : get ?x _ = Some ?t, I: gettype _ ?x nil ?t _ _  |-  ltyp _ _ _ (p_e (fevar ?x) _) _ =>
   apply SL_3_1 with (tau':= t); auto

  | H : ltyp _ _ _ ?e (cross ?t ?t') |-  ltyp _ _ _ (dot ?e zero_pe) ?t =>
   apply SL_3_3 with (t1:= t'); auto; idtac "t" t

  | H : ltyp _ _ _ ?e (cross ?t ?t') |-  ltyp _ _ _ (dot ?e one_pe) ?t' =>
   apply SL_3_4 with (t0:= t); auto

  | H: context[rtyp ?d0 _ _ ?e ?tau']
  |- styp ?d0 _ _ (letx ?e _) _ =>
    apply_fresh styp_let_3_6  with type tau'; auto

  | H: context[styp (_ & _ ~ ?k) _ _ (TTM.open_rec_st _ _ (TM.open_rec_st _ _ ?s0)) _],
    I: context[rtyp ?d0 _ _ ?e ?tau'] 
  |- styp ?d0 _ _ (openx ?e ?s0) ?tau => 
    apply_fresh styp_open_3_7 with type tau' kind k; intros; auto

  | H: context[styp (_ & _ ~ ?k) _ _ (TTM.open_rec_st _ _ (TM.open_rec_st _ _ ?s0)) _],
    I: context[ltyp ?d0 _ _ ?e ?tau'] 
  |- styp ?d0 _ _ (openstar ?e ?s0) ?tau => 
    apply_fresh styp_openstar_3_8 with type tau' kind k; intros; auto

  | H: context[styp ?d0 _ _ (TM.open_rec_st _ _ ?s0) ?tau']
  |- styp ?d0 _ _ (TM.open_rec_st _ _ ?s0) ?tau' =>
    applys* H
  end.

Ltac solve_rtyp :=
  match goal with
  | H : get ?x _ = Some ?t, I: gettype _ ?x nil ?t _ _  |-  rtyp _ _ _ (p_e (fevar ?x) _) _ =>
    apply SR_3_1 with (tau':= t); auto

  | H : rtyp _ _ _ ?e (cross ?t ?t') |-  rtyp _ _ _ (dot ?e zero_pe) ?t =>
    apply SR_3_3 with (t1:= t'); auto; idtac "t" t

  | H : rtyp _ _ _ ?e (cross ?t ?t') |-  rtyp _ _ _ (dot ?e one_pe) ?t' =>
    apply SR_3_4 with (t0:= t); auto

  | H : rtyp _ _ _ ?e1 (arrow ?t' ?tau) |- rtyp _ _ _ (appl ?e1 ?e2) ?tau =>
    apply SR_3_9 with (tau':= t'); auto

  | H:  rtyp _ _ _ ?e (utype ?k' ?t') |- rtyp _ _ _ (inst ?e _) _ =>
    apply SR_3_11 with (k:=k') (tau':= t'); auto

  | |- rtyp _ _ _ (pack _ _ (etype ?p ?k ?tau)) (etype ?p ?k ?tau) =>
   apply_fresh SR_3_12; auto

  | |- rtyp _ _ _ (f_e (dfun ?tau ?tau' _)) (arrow ?tau ?tau') =>
    apply_fresh SR_3_13; auto

 | |- rtyp _ _ _ (f_e (ufun ?k _)) (utype ?k _) =>
    apply_fresh SR_3_14; auto

 |  H : context[rtyp ?d0 _ _ ?e (T.open_rec _ ?tau' ?tau)] 
 |- rtyp ?d0 _ _ ?e (T.open_rec _ ?tau' ?tau) =>
    applys* H
end.

Ltac solve_ltyp :=
  match goal with
  | H : get ?x _ = Some ?t, I: gettype _ ?x nil ?t _ _  |- ltyp _ _ _ (p_e (fevar ?x) _) _ =>
    apply SL_3_1 with (tau':= t); auto
  | H : ltyp _ _ _ ?e (cross ?t ?t') |-  ltyp _ _ _ (dot ?e zero_pe) ?t =>
    apply SL_3_3 with (t1:= t'); auto; idtac "t" t
  | H : ltyp _ _ _ ?e (cross ?t ?t') |-  ltyp _ _ _ (dot ?e one_pe) ?t' =>
    apply SL_3_4 with (t0:= t); auto
end.

Ltac solve_typ := repeat (try solve_styp; try solve_rtyp; try solve_ltyp).
(* Not ready for prime time. 
Hint Extern 3 (rtyp _ _ _ _ _) => try solve_rtyp.
Hint Extern 3 (ltyp _ _ _ _ _) => try solve_ltyp.
Hint Extern 3 (styp _ _ _ _ _) => try solve_styp.
*)

Function A_2_Term_Weakening_prop (In : Type) (H : TypJudgement In) 
         (d : Delta) (u : Upsilon) (g : Gamma) (s : In) (t : Tau)
         (st : typ' d u g s t) := 
    typ' d u g s t ->
    (* WFC d u g ->  *)
      forall (u' : Upsilon) (g' : Gamma),
        WFC d u' g' ->
        LVPE.extends u u' ->
        extends g g' ->
        typ' d u' g' s t.
Hint Unfold A_2_Term_Weakening_prop.

Lemma A_2_Term_Weakening_2_ltyp:
  forall (d : Delta) (u : Upsilon) (g : Gamma) (s : E) (t : Tau) (ty : typ' d u g s t),
   A_2_Term_Weakening_prop LtypJudgement d u g s t ty.
Proof.
  intros.
  Typ_Induction ltyp_ind_mutual A_2_Term_Weakening_prop;
  intros; try solve[auto].
  admit. (* let *)

  apply_fresh styp_open_3_7 with type tau' kind k; try assumption.
  intros.
  eapply H; try assumption; try solve[notin_solve].
  assert(alpha  \notin L); auto.
  assert(x \notin L); auto.
  apply* WFC_delta_gamma_weakening.
  (* restart here *)
  admit.
  apply* extends_push_both.
  auto.

  apply_fresh styp_openstar_3_8 with type tau' kind k; try assumption.
  intros.
  eapply H; try assumption; try solve[notin_solve].
  assert(alpha  \notin L); auto.
  assert(x \notin L); admit. (* This shows an automation bug, working wfc from notin*)
  apply* extends_push_both.
  auto.

  admit.
  admit.
  admit.

  try solve[solve_typ].
  try solve[solve_typ].
  try solve[solve_typ].
  try solve[solve_typ].
  try solve[solve_typ].
  try solve[solve_typ].
(*  try solve[solve_typ].
  try solve[solve_typ].
  try solve[solve_typ].
*)
(*
  apply_fresh SR_3_13.
  eapply H; try assumption; try solve[notin_solve].
  assert(y \notin L); auto.
  apply WFC_gamma_weakening; try assumption; try solve[notin_solve].
  admit. (* magic k *)
  apply* extends_push_both.
  auto.

  apply_fresh SR_3_14; try assumption.
  eapply H; try assumption; try solve[notin_solve].
  assert(y \notin L); auto.
  apply WFC_delta_weakening; try assumption; try solve[notin_solve].
Qed.
*)
Admitted.

(* Just to test that the screwed up K is not different for rtyp or styp. *)
Lemma A_2_Term_Weakening_3:
  forall (d : Delta) (u : Upsilon) (g : Gamma) (s : E) (t : Tau) (ty : typ' d u g s t),
   A_2_Term_Weakening_prop RtypJudgement d u g s t ty.
Proof.
  intros.
  Typ_Induction rtyp_ind_mutual A_2_Term_Weakening_prop;
  intros; try solve[auto].
Admitted.

Lemma A_2_Term_Weakening_4:
  forall (d : Delta) (u : Upsilon) (g : Gamma) (s : St) (t : Tau) (ty : typ' d u g s t),
   A_2_Term_Weakening_prop StypJudgement d u g s t ty.
Proof.
  intros.
  Typ_Induction styp_ind_mutual A_2_Term_Weakening_prop;
  intros; try solve[auto].
Admitted.


(* Old perhaps of some use. 
Lemma needed:
  forall d u g,
    WFC d u g ->
    forall x tau',
      get x g = Some tau' ->
      forall tau p,
        gettype u x nil tau' p tau ->
        K d tau' A ->
        LVPE.V.get (x, p) u = Some tau.
Admitted.

(* Will I need this for other typings? *)
Lemma ltyp_K_A:
  forall d u g, 
    WFC d u g ->
    forall e tau,
      ltyp d u g e tau ->
      K d tau A.
Proof.
  introv WFCd ltypd.
  induction ltypd; auto.
  apply A_1_Context_Weakening_2 with (u:= u) (x:=x) (p:=p).
  inversions* WFCd.
  inversions* WFCd.
Admitted.
(*
  apply needed with (d:= d) (g:=g) (tau':=tau'); auto.

  apply IHltypd in WFCd.
  inversion WFCd; subst.
  assumption.
  inversion WFCd; subst.
  assumption.
  inversion H.

  apply IHltypd in WFCd.
  inversion WFCd; subst.
  assumption.
  inversion WFCd; subst.
  assumption.
  inversion H.
Qed.
*)
(* Hint Immediate ltyp_K_A. *)

(* Perhaps. *)
Lemma store_types_are_K_empty_A:
  forall d u g,
    WFC d u g ->
    forall x tau',
     get x g = Some tau' ->
     forall p tau, 
       gettype u x nil tau' p tau ->
       K empty tau A.
Proof.
  introv WFCd getd gettyped.
  induction gettyped.
Admitted.
  

Lemma rtyp_K_empty_ptr_A:
  forall d u g, 
    WFC d u g ->
    forall e tau,
      rtyp d u g e (ptype tau) ->
      K empty tau A.
Proof.
  introv WFCd rtypd.
  inversions* rtypd.
  apply store_types_are_K_empty_A
   with (d:=d) (u:=u) (g:=g) (x:=x)(tau':= tau') (p:= p); try assumption.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  (* mutual induction required! *)
Admitted.

Lemma ltyp_K_empty_A:
  forall d u g, 
    WFC d u g ->
    forall e tau,
      ltyp d u g e tau ->
      K empty tau A.
Proof.
  introv WFCd ltypd.
  induction ltypd; try solve[auto].
  apply store_types_are_K_empty_A
   with (d:=d)(u:=u)(g:=g)(x:=x)(tau':=tau')(p:=p); auto.
Admitted.
(*
  apply rtyp_K_empty_ptr_A with (d:=d) (u:=u) (g:=g)(e:= e).

  apply IHltypd in WFCd.
  inversions* WFCd.
  inversion H.
  apply IHltypd in WFCd.
  inversions* WFCd.
  inversion H.
Qed.
*)
(* Hint Immediate ltyp_K_A. *)
*)