(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Defining type safety, page 67.

*)

Set Implicit Arguments.
Require Export Cyclone_Formal_Syntax Cyclone_Static_Semantics_Kinding_And_Context_Well_Formedness.
Require Export Cyclone_Static_Semantics_Typing_Heap_Objects.
Require Export Cyclone_Classes Cyclone_Inductions Cyclone_LN_Tactics Cyclone_LN_Extra_Lemmas_And_Automation.
Require Export Cyclone_Well_Formedness_Lemmas.
Require Export ContextWeakeningProof.
Require Export Cyclone_LN_Types_Lemmas.
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

Lemma gettype_weakening:
  forall u u' x tau' p tau,
  gettype u x nil tau' p tau ->
  LVPE.extends u u' ->
  gettype u' x nil tau' p tau.
Proof.
  intros.
  unfold LVPE.extends, LVPE.binds in *.
  induction H; auto.
  apply gettype_etype with (tau'':= tau'');auto.
Qed.
Ltac gettype_weakening :=
  match goal with 
    | H: gettype ?u' ?x' nil ?tau'' ?p' ?tau',
      I: LVPE.extends ?u' ?u''
    |- gettype ?u'' ?x' nil ?tau'' ?p' ?tau' =>
      apply gettype_weakening with (u:= u'); assumption
  end.
Hint Extern 1 (gettype _ _ nil _ _ _) => try gettype_weakening.

Lemma WFDG_gamma_K:
  forall d g, 
    WFDG d g ->
    forall x tau, 
      get x g = Some tau ->
      K d tau A.
Proof.
  introv WFDGd.
  induction WFDGd; intros.
  apply binds_empty_inv in H0.
  inversion H0.
  specialize (IHWFDGd x0 tau0).
  unfold binds in *.
  destruct(classicT(x0 = x)); subst.
  rewrite get_push in H3.
  case_var.
  inversion H3; subst; assumption.
  rewrite get_push in H3.
  case_var.
  auto.
Qed.
Ltac WFDG_gamma_K :=
  match goal with 
   | H:  WFDG ?d' ?g', 
     I: get ?x' ?g' = Some ?tau'
   |- K ?d' ?tau' A =>
    apply WFDG_gamma_K with (d:=d') (g:=g') (x:=x') (tau:=tau')
end.
Hint Extern 1 (K _ _ A) => WFDG_gamma_K.
  
Lemma WFC_gamma_K:
  forall d u g, 
    WFC d u g ->
    forall x tau, 
      get x g = Some tau ->
      K d tau A.
Proof.
  intros.
  inversion H; subst.
  apply WFDG_gamma_K with (g:= g) (x:=x); try assumption.
Qed.
Ltac WFC_gamma_K :=
  match goal with 
    | H: WFC ?d' ?u' ?g',
      I: get ?x' ?g' = Some ?tau'
    |- K ?d' ?tau' A =>
    apply WFDG_gamma_K with (d:=d') (u:=u') (g:=g') (x:=x') (tau:=tau')
  end.
Hint Extern 1 (K _ _ A) => WFC_gamma_K.

Ltac simpl_get ::=
  idtac "simpl_get";
  trace_goal;
  timeout 2
  repeat
    match goal with
  | |- context [get ?a empty]           => trace_goal; rewrite~ get_empty
  | |- context [get ?a empty]           => trace_goal; rewrite~ get_empty  
  | |- context [get ?a empty]           => trace_goal; rewrite~ get_empty
  | |- context [get ?a (_ & (_ ~ _)) ]      => trace_goal;
    rewrite~ get_push; try repeat case_var~

  | |- context [get ?a ((?b ~ _) & _)] => trace_goal;
    rewrite~ get_concat; try repeat case_var~

  | |- context [get ?a _ = None] => trace_goal;
   apply* get_none

  | H: context[get _ empty = Some _] |- _ => 
    rewrite get_empty in H; inversion H
end.

Ltac simpl_lvpe_get ::=
  trace_goal;
  timeout 2
  repeat
    match goal with 
    | |- context [LVPE.V.get ?a LVPE.V.empty]    => trace_goal;
      rewrite~ LVPE.get_empty

  | |- context [LVPE.V.get ?a (?a ~p _) ]      => trace_goal;
    rewrite~ LVPE.get_single; try repeat case_var~
  | |- context [get ?a (?a ~ _) ]      => trace_goal;
    rewrite~ get_single; try repeat case_var~

  | |- context [LVPE.V.get ?a (_ &p (?a ~p _)) ]      => trace_goal;
    rewrite~ LVPE.get_push; try repeat case_var~
  | |- context [get ?a (_ & (?a ~ _)) ]      => trace_goal;
    rewrite~ get_push; try repeat case_var~

  | |- context [LVPE.V.get ?a (_ &p (_ ~p _)) ]      => trace_goal;
    rewrite~ LVPE.get_push; try repeat case_var~
  | |- context [LVPE.V.get ?a ((?b ~ _) & _)] => trace_goal;
    rewrite~ LVPE.get_concat; try repeat case_var~

  | H: context[LVPE.V.get _ empty = Some _] |- _ => 
    rewrite LVPE.get_empty in H; inversion H

  | H: context[LVPE.V.get _ LVPE.V.empty = Some _] |- _ => 
    rewrite LVPE.get_empty in H; inversion H
end.

Lemma WFU_upsilon_K:
  forall u, 
    WFU u ->
    forall x p tau, 
      LVPE.V.get (x,p) u = Some tau ->
      K empty tau A.
Proof.
  introv WFUd.
  induction WFUd.
  intros.
  auto.
  simpl_lvpe_get.
  intros.
  destruct(classicT((x0,p0) = (x,p))).
  rewrite LVPE.get_push in H2.
  rewrite If_l in H2.
  inversion H2.
  subst.
  assumption.
  rewrite If_l in H2; try assumption.
  rewrite LVPE.get_push in H2.
  rewrite If_r in H2; try assumption.
  apply IHWFUd with (x:=x0) (p:=p0); try assumption.
Qed.
Ltac WFU_upsilon_K :=
  match goal with 
    | H: WFU ?u',
      I: LVPE.V.get (?x',?p') ?u' = Some ?tau'
      |-  K empty ?tau' A =>
      apply WFU_upsilon_K
end.
Hint Extern 1 (K empty _ A) => WFU_upsilon_K.
      
Lemma WFC_upsilon_K:
  forall d u g, 
    WFC d u g ->
    forall x p tau, 
      LVPE.V.get (x,p) u = Some tau ->
      K empty tau A.
Proof.
 introv WFCd.
 inversion WFCd; subst.
 apply WFU_upsilon_K; assumption.
Qed.
Ltac WFC_upsilon_K :=
  match goal with 
    | H: WFC ?d' ?u' ?g',
      I: LVPE.V.get (?x',?p') ?u' = Some ?tau'
      |-  K empty ?tau' A =>
      apply WFU_upsilon_K
end.
Hint Extern 1 (K empty _ A) => WFC_upsilon_K.

Lemma WFDG_gamma_weakening:
  forall d g y tau, 
    y \notin (fv_gamma g) ->
    K d tau A ->
    WFDG d g ->
    WFDG d (g & (y ~ tau)).
Proof.
  introv NI WFd.
  auto.
Qed.
Ltac WFDG_gamma_weakening :=
  match goal with
    | H: K ?d' ?tau' A, 
      I: WFDG ?d' ?g' 
    |-  WFDG ?d' (?g' & (?y' ~ ?tau')) =>
      apply WFDG_gamma_weakening with (tau:=tau');
      notin_solve
  end.
Hint Extern 1 (WFDG _ (_ & (_ ~ _))) => WFDG_gamma_weakening.

Lemma WFDG_delta_weakening:
  forall alpha d g k, 
    alpha \notin fv_delta d ->
    WFDG d g ->
    WFDG (d & alpha ~ k) g.
Proof.
  lets: WFDG_gamma_weakening.
  introv ANI WFDGd.
  induction WFDGd; auto.
  assert(alpha \notin fv_delta d).
  auto.
  apply IHWFDGd in H4.
  constructor; try assumption.
  constructor; try assumption.
  apply A_1_Context_Weakening_1 with (d:= d); try assumption.
  auto.
  auto.
Qed.
Ltac WFDG_delta_weakening :=
  match goal with
    | H: ?alpha \notin _,
      I: WFDG ?d' ?g'
    |- WFDG (?d' & ?alpha ~ ?k) ?g' =>
      apply WFDG_delta_weakening; notin_solve
  end.
Hint Extern 1 (WFDG (_ & _ ~ _) _) => WFDG_delta_weakening.

Lemma get_fv_delta:
  forall v d k,
    get v d = Some k ->
    \{v} \c fv_delta d.
Proof.
  intros.
  unfold fv_delta.
  induction d using env_ind.
  rewrite get_empty in H.
  inversion H.
  rewrite get_push in H.
  case_var.
  inversion H.
  subst.
  rewrite dom_push.
  fset.
  apply IHd in H.
  rewrite dom_push.
  (* need some trivial set theory *)
Admitted.
Ltac get_fv_delta :=
  match goal with 
  | H: get ?v ?d = Some ?k' |- \{?v} \c fv_delta ?d =>
    apply get_fv_delta with (k:= k'); assumption; auto with fset
end.                                                
Hint Extern 1 (\{_} \c fv_delta _) => get_fv_delta.
Hint Extern 1 (T.fv _ \c fv_delta _) => simpl; get_fv_delta.

Lemma K_fv:
  forall tau d k,
    WFD d ->
    K d tau k ->
    T.fv tau \c fv_delta d.
Proof.
  intros tau.
  induction tau; intros; simpl; fset;
   try solve[try inversion H; subst; try inversion H0; subst; 
             auto with fset].
  inversion H; subst.
Admitted.

Lemma K_empty_closed:
  forall tau k,
    K empty tau k ->
    T.fv tau = \{}.
Proof.
  intros.
  lets: K_fv tau (@empty Kappa).
  apply H0 in H.
  unfold fv_delta in H.
  rewrite dom_empty in H.
  admit. (* trivial set theory *)
  auto.
Qed.
Lemma ok_strengthing:
  forall (d' : Delta) y k, 
    ok(d' & y ~ k) ->
    forall d, 
      extends d d' ->                
      ok(d & y ~ k).
Proof.
  intros.
  induction d using env_ind.
  apply* ok_push.
  apply ok_push.
  apply ok_push.
  inversion H.
Admitted.

Lemma K_weakening:
  forall tau d,
    K d tau A ->
    forall d',
      WFD d ->
      extends d d' ->
      K d'     tau A.
Proof.
  introv Kempty.
  induction Kempty; try solve[auto].
  intros.
  apply_fresh K_utype; intros.
  assert(I: y \notin L); auto.
  specialize (H y I ).
  apply ok_strengthing with (d:=d) in H3; auto.
  intros.
  apply_fresh K_etype; intros.
  assert(I: y \notin L); auto.
  specialize (H y I ).
  apply ok_strengthing with (d:=d) in H3; auto.
Qed.  
  
(* The heart of the magic K.
 So either rtyp/ltyp/styp when they bind (write the store) or read (p_e (fevar x) p)
that type has to K empty ? A. 

  So either Dan has failed to check this or its provable from type typing derivations.

  WFU checks this but nothing in the typing rules do.

  Assuming the thesis needs addition, rules that should check this are:
  SS 3.6 (or all rtyp)
  SS 3.7
  SS 3.8
  SL3.1
  SR 3.1
  SR 3.8 - has asgn.
  SR 3.11 - has ak 
  SR 3.12 - has ak
*)

Lemma WFC_gamma_weakening:
  forall d u g,
    WFC d u g ->
    forall tau, 
      K empty tau A ->  (* Magic K *)
      forall y, 
        y \notin (fv_gamma g) ->
        WFC d u (g & (y ~ tau)).
Proof.
SearchAbout(_ -> K _ _ A).
  lets: WFDG_gamma_weakening.
  introv WFCd.
  inversion WFCd; subst.
  constructor; try assumption.
  constructor; auto.
  apply K_weakening with (d:= empty); auto.
Qed.
Ltac WFC_gamma_weakening :=
  match goal with
    | H: K ?d' ?tau' A,
      I: WFC ?d' ?u' ?g' 
    |-  WFC ?d' ?u' (?g' & (?y' ~ ?tau')) =>
      apply WFC_gamma_weakening with (tau:=tau');
      notin_solve
  end.
Hint Extern 1 (WFC _ _ (_ & (_ ~ _))) => WFC_gamma_weakening.

Lemma WFDG_delta_gamma_weakening:
  forall alpha d g x k tau, 
    alpha \notin fv_delta d ->
    x \notin  fv_gamma g ->
    K d tau A ->
    WFDG d g ->
    WFDG (d & alpha ~ k) (g & x ~ tau).
Proof.
  introv ANI XNI Kd WFCd.
  apply WFDG_delta_weakening; try assumption.
  apply WFDG_gamma_weakening; try assumption.
Qed.  

Ltac WFDG_delta_gamma_weakening :=
  match goal with
    | H: ?alpha \notin _,
      I: ?x \notin _,
      J: WFDG ?d' ?g'
    |- WFDG (?d' & ?alpha ~ ?k) (?g' & ?x ~ ?tau)  =>
      apply WFDG_delta_gamma_weakening; notin_solve
  end.
Hint Extern 1 (WFDG (_ & _ ~ _) (_ & _ ~ _)) => WFDG_delta_gamma_weakening.

Lemma WFC_delta_weakening:
  forall alpha d u g k,  
    alpha \notin fv_delta d ->
    WFC d u g ->
    WFC (d & alpha ~ k) u g.
Proof.
  lets: WFDG_delta_weakening.
  introv ANI WFCd.
  inversion WFCd; subst.
  auto.
Qed.
Ltac WFC_delta_weakening :=
  match goal with
    | H: ?alpha \notin _,
      J: WFC ?d' ?u ?g'
    |- WFC (?d' & ?alpha ~ ?k) _ ?g' =>
      apply WFC_delta_weakening; notin_solve; try assumption
  end.

Hint Extern 1 (WFC (_ & _ ~ _) _ _) => WFDG_delta_gamma_weakening.

Lemma WFC_delta_gamma_weakening:
  forall alpha d u g x k tau, 
    alpha \notin fv_delta d ->
    x \notin fv_gamma g ->
    K d tau A ->
    WFC d u g ->
    WFC (d & alpha ~ k) u (g & x ~ tau).
Proof.
  lets: WFDG_delta_gamma_weakening.
  introv ANI XNI Kd WFCd.
  inversion WFCd; subst.
  auto.
Qed.
Ltac WFC_delta_gamma_weakening :=
  match goal with
    | H: ?alpha \notin _,
      I: ?x \notin _,
      J: WFC ?d' ?g' _
    |- WFC (?d' & ?alpha ~ ?k) _ (?g' & ?x ~ ?tau)  =>
      apply WFC_delta_gamma_weakening; notin_solve
  end.
Hint Extern 1 (WFC (_ & _ ~ _) _ (_ & _ ~ _)) => WFDG_delta_gamma_weakening.


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
(* Hint Immediate ltyp_K_A. *)

Lemma WFC_WFU:
  forall d u g, 
    WFC d u g ->
    WFU u.
Proof.
  introv WFCd.
  inversion WFCd; auto.
Qed.
Hint Immediate WFC_WFU.

Lemma WFC_WFDG:
  forall d u g, 
    WFC d u g ->
    WFDG d g.
Proof.
  introv WFCd.
  inversion WFCd; auto.
Qed.
Hint Immediate WFC_WFDG.

Lemma wfc_ok_delta:
  forall d u g, 
    WFC d u g ->
    ok d.
Proof.
  introv WFCd.
  inversion WFCd; auto.
Qed.
Hint Immediate wfc_ok_delta.

Lemma wfc_ok_upsilon:
  forall d u g, 
    WFC d u g ->
    LVPE.okp u.
Proof.
  introv WFCd.
  inversion WFCd; auto.
Qed.
Hint Immediate wfc_ok_upsilon.

Lemma wfc_ok_gamma:
  forall d u g, 
    WFC d u g ->
    ok g.
Proof.
  introv WFCd.
  inversion WFCd; auto.
Qed.
Hint Immediate wfc_ok_gamma.

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
  SearchAbout(K empty _ A).
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
Hint Immediate ltyp_K_A.

(* WFC d u g is not in the thesis theorem which drops the magic Ks down to 1.
   As we an extension to d' u g' and it's valid, WFC d u g is derivable. So
  the theorem statement is valid. *)

(* Dan assumes this in the theorem statements. *)
Lemma WFU_extension_WFU:
  forall u',
    WFU u' ->
    forall u,
      LVPE.extends u u' ->
      WFU u.
Proof.        
  introv WFUd.
  induction u.
  intros.
  rewrite <- LVPE.V.empty_def.
  auto.
  unfold LVPE.extends.
  intros.
  destruct a.
  (* have to learn to rewrite lists and flip them into envs. *)
  (* should prove. *)
Admitted.

Lemma WFC_extension_WFC:
  forall d' u' g',
    WFC d' u' g' ->
    forall d u g,
      extends d d' ->
      LVPE.extends u u'->
      extends g g' ->
      WFC d u g.
Proof.
  introv WFCd.
  induction WFCd.
  intros.
  auto.
Admitted.

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

  try solve[solve_typ].
  apply_fresh styp_open_3_7 with type tau' kind k; try assumption.
  intros.
  eapply H; try assumption; try solve[notin_solve].
  assert(alpha  \notin L); auto.
  assert(x \notin L); admit. (* This shows an automation bug, working wfc from notin*)
  apply* extends_push_both.
  auto.

  apply_fresh styp_openstar_3_8 with type tau' kind k; try assumption.
  intros.
  eapply H; try assumption; try solve[notin_solve].
  assert(alpha  \notin L); auto.
  assert(x \notin L); admit. (* This shows an automation bug, working wfc from notin*)
  apply* extends_push_both.
  auto.

  try solve[solve_typ].
  try solve[solve_typ].
  try solve[solve_typ].
  try solve[solve_typ].
  try solve[solve_typ].
  try solve[solve_typ].
  try solve[solve_typ].
  try solve[solve_typ].
  try solve[solve_typ].
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
(* And they are. *)

Lemma A_3_Heap_Weakening_1:
  forall u g u' g',
    LVPE.extends u u' ->
    extends g g' ->
    WFC empty u' g' ->
    forall h g'', 
      htyp u g h g'' ->
      htyp u' g' h g''.
Proof.
  introv Euu' Egg' WFCd H.
  induction H; auto.
  specialize (IHhtyp Euu' Egg').
  constructor; try assumption.
  lets* T: A_2_Term_Weakening_3.
Qed.

Lemma A_3_Heap_Weakening_2:
  forall h u,
    refp h u ->
    forall h',
      extends h h' ->
      refp h' u.
Proof.
  introv R.
  induction R; intros; auto.
  apply refp_pack with (tau:=tau) (k:=k)(v:=v)(v':=v'); auto.
Qed.

Lemma subset_weakening:
  forall A (a : fset A) b c,
    a \c c ->
    a \c b \u c.
Admitted.

Lemma get_dom:
  forall A alpha (d : env A)  k,
    get alpha d = Some k ->
    \{alpha} \c dom d.
Proof.
  intros.
  induction d using env_ind.
  rewrite get_empty in H.
  inversion H.
  destruct (classicT(alpha = x)).
  subst.
  rewrite dom_push.
  fset.
  rewrite get_push in H.
  rewrite* If_r in H.
  apply IHd in H.
  rewrite dom_push.
  apply* subset_weakening.
Qed.
Ltac get_dom :=
  match goal with
  | H: get ?a ?d = Some ?k' 
  |- \{?a} \c dom ?d =>
    apply get_dom with (k:= k')
  end.
Hint Extern 1 (\{_} \c dom _) => get_dom.

Lemma singleton_empty:
  forall A (v :A),
    \{v} = \{} -> False.
Admitted.

Lemma fv_subst:
  forall tau alpha tau',
    T.fv tau' = \{} ->
    T.subst tau alpha tau' = tau'.
Proof.
  intros.
  induction tau'; auto;
    try solve[simpl in H; simpl; fequals*].
  simpl in H.
  apply singleton_empty in H.
  inversion H.

  simpl in H.
  simpl.
  assert(T.fv tau'1 = \{}). admit.
  assert(T.fv tau'2 = \{}). admit.
  fequals*.

  simpl in H.
  simpl.
  assert(T.fv tau'1 = \{}). admit.
  assert(T.fv tau'2 = \{}). admit.
  fequals*.  
Qed.

Lemma open_rec_fv:
  forall alpha tau n, 
    T.fv (T.open_rec n (ftvar alpha) tau) = T.fv tau \u \{alpha} \/
    T.fv (T.open_rec n (ftvar alpha) tau) = T.fv tau.
Proof.
  intros.
  induction tau; simpl; auto.
  case_nat.
  simpl.
  left.
  rewrite* union_empty_l.

  simpl.
  right*.
  admit.
  admit.
Admitted.

Lemma K_fv_delta:
  forall tau d k,
    ok d ->
    K d tau k ->
    T.fv tau \c dom d.
Proof.
  introv OKd Kd.
  induction Kd; simpl; auto with fset.
  admit.
  admit.
  pick_fresh alpha.
  lets I: open_rec_fv alpha tau 0.
  assert(ANI: alpha \notin L); auto.
  assert(KO: ok( d & alpha ~ k)); auto.
  specialize (H0 alpha ANI KO KO).
  inversion I.
  rewrite H1 in H0.
  rewrite dom_push in H0.
  admit. (* set *)
Admitted. (* should work *)

Lemma punt:
  forall d alpha alpha' k k' tau tau0,  
    alpha' \notin T.fv tau -> 
    K (d & alpha' ~ k) (T.open_rec 0 (ftvar alpha') tau) k' -> (* perhaps exists k' *)
    T.subst tau0 alpha (T.open_rec 0 (ftvar alpha') tau) =
                        T.open_rec 0 (ftvar alpha') tau -> 
    T.subst tau0 alpha tau = tau.
Proof.
  intros.
  induction tau; auto; simpl; fequals;
  try solve[simpl in H1;
  inversion H1;
  inversion H0; subst;
  try apply IHtau1; auto;
  try apply IHtau1; auto;
  try apply IHtau2; auto;
  try apply IHtau2; auto;
  inversion H2].

  simpl in H0.
  inversion H0; subst.
  apply IHtau; auto.
  inversion H2; subst.
Admitted.

Lemma A_4_Useless_Substitutions_1':
  forall alpha d,
    alpha \notin dom d ->
    ok d ->
    forall tau',
     (exists k, K d tau' k) ->
      forall tau, 
        T.subst tau alpha tau' = tau'.
Proof.
  intros.
  induction tau'; auto.
  intros.
  simpl.
  case_var*.
  inversion H1; subst.
(*
  rewrite get_none in H4; auto.
  inversion H4.
  inversion H2; subst.
  rewrite get_none in H5; auto.
  inversion H5.

  admit.
  admit.
  simpl; fequals.
  inversion H1; subst.
  admit. (* exists k problem ?*)
  admit.
  admit.
  simpl; fequals.
  apply IHtau'.
  inversion H1; subst.
  Admitted.
*)
  (* Stuck here too. *)
Admitted.

Lemma A_4_Useless_Substitutions_1:
  forall alpha d,
    alpha \notin dom d ->
    ok d ->
    forall tau' k, 
      K d tau' k ->
      forall tau, 
        T.subst tau alpha tau' = tau'.
Proof.
  introv NI OKd Kd.
  induction Kd; intros;
  try solve[simpl; auto; try case_var*; 
            try solve[rewrite* get_none in H; inversion H]; fequals*].
  (* is this an induction problem with L needing to be d ? *)
  simpl.
  fequals.
  pick_fresh alpha'.
  assert(N: alpha' \notin L); auto.
  assert(O: alpha' # d); auto.
  assert(P: ok (d & alpha' ~ k)); auto.
  assert(Q: alpha # d & alpha' ~ k); auto.
  specialize (H alpha' N P).
  specialize (H0 alpha' N P Q P tau0).
  assert(R: alpha' \notin (T.fv tau)).
  auto.

  apply punt with (d:= d) (alpha':=alpha') (k:= k) (k':= A); try assumption.
Admitted.

Lemma A_4_Useless_Substitutions_2:
  forall alpha d g,
    alpha \notin dom d ->
    WFDG d g ->
    forall tau, 
      EnvOps.map (fun tau' =>  (T.subst tau alpha tau')) g = g.
Proof.  
  introv NI WFDGd.
  induction WFDGd.
  intros.
  rewrite* map_empty.
  intros.
  rewrite map_push.
  rewrite* IHWFDGd.
  rewrite A_4_Useless_Substitutions_1 with (d:=d) (k:=A); auto.
Qed.

(* This formulation builds a useless induction principle. *)
(* A formulation of the theorem as above is necessary. *)
Lemma A_4_Useless_Substitutions_3:
  forall u,
    WFU u ->
    forall tau alpha, 
      LVPE.V.map (fun tau' => (T.subst tau alpha tau')) u = u.
Proof.  
  introv WFUd.
  induction WFUd; intros.
  rewrite* LVPE.map_empty.

  rewrite LVPE.map_push.
  rewrite IHWFUd.
  rewrite A_4_Useless_Substitutions_1 with (d:= empty) (k:=A); auto.
Qed.

Lemma subst_var:
  forall t1 v,
    T.subst t1 v (ftvar v) = t1.
Proof.
  intros; simpl; case_var*.
Qed.

Lemma A_5_Commuting_Substitutions:
  forall beta t2,
    beta \notin T.fv t2 ->
    forall t0 t1 alpha,
      (T.subst t2 alpha (T.subst t1 beta t0)) =
      (T.subst (T.subst t2 alpha t1) beta (T.subst t2 alpha t0)).
Proof.
  induction t0; intros; try solve[auto]; try solve[simpl;try case_var*; fequals*].
  admit. (* Var case wrong? Theorem wrong? *)
Qed.

Require Export Coq.Program.Equality.

(* Dependent induction does OK but it puts me into JMeq which I'd rather avoid,
 and has to have functional equivalence of environments. *)
Lemma A_6_Subsititution_JMeq:
  forall d t k,
    AK d t k ->
    forall alpha t' k', 
      K (d & alpha ~ k) t' k' ->
      K d (T.subst t alpha t') k'.
Proof.
  introv AKd Kd.
  dependent induction Kd;
    try solve[simpl; auto; try apply K_cross; try apply K_arrow; 
              try applys* IHKd1;
              try applys* IHKd2].
  simpl.
  case_var.
  rewrite get_push in H.
  case_var.
  inversion H.
  inversions* AKd.
  inversion H4.
  apply K_B.
  (* What's my automation?*)
  rewrite get_push in H.
  case_var*.

  admit.
  admit.

  simpl.
  apply_fresh K_utype; intros.
  assert(NI: y \notin L); auto.
  assert(D: ok (d & alpha ~ k & y ~ k0)).
  admit.
  assert(AK': AK (d & y ~ k0) t k).
  admit.
  assert(Q:  d & alpha ~ k & y ~ k0 ~= d & y ~ k0 & y ~ k).
  admit. (* doubtful *)
  lets SOV: TP.subst_open_var alpha y.
  rewrite <- SOV.
  specialize (H0 y NI D (d & y ~ k0) k AK' alpha).
  apply H0.
  (* Works but modulo JMeq on misordered d, which is functionally equivalent. *)
Admitted.

(* Trying specialized induction schema, but going to prove the general one first. *)

Lemma K_ind_proven:
  forall P : Delta -> Tau -> Kappa -> Prop,
    (forall d : Delta, P d cint B) ->
    (forall (d : Delta) (alpha : var), get alpha d = Some B -> P d (ftvar alpha) B) ->
    (forall (d : Delta) (alpha : var),
        get alpha d = Some A -> P d (ptype (ftvar alpha)) B) ->
    (forall (d : Delta) (t0 t1 : Tau),
        K d t0 A -> P d t0 A -> K d t1 A -> P d t1 A -> P d (cross t0 t1) A) ->
    (forall (d : Delta) (t0 t1 : Tau),
        K d t0 A -> P d t0 A -> K d t1 A -> P d t1 A -> P d (arrow t0 t1) A) ->
    (forall (d : Delta) (tau : Tau), K d tau A -> P d tau A -> P d (ptype tau) B) ->
    (forall (L : vars) (d : Delta) (k : Kappa) (tau : Tau),
        (forall alpha : var,
            alpha \notin L ->
            ok (d & alpha ~ k) -> K (d & alpha ~ k) (T.open_rec 0 (ftvar alpha) tau) A) ->
        (forall alpha : var,
            alpha \notin L ->
            ok (d & alpha ~ k) -> P (d & alpha ~ k) (T.open_rec 0 (ftvar alpha) tau) A) ->
        P d (utype k tau) A) ->
    (forall (L : vars) (d : Delta) (k : Kappa) (tau : Tau) (p : Phi),
        (forall alpha : var,
            alpha \notin L ->
            ok (d & alpha ~ k) -> K (d & alpha ~ k) (T.open_rec 0 (ftvar alpha) tau) A) ->
        (forall alpha : var,
            alpha \notin L ->
            ok (d & alpha ~ k) -> P (d & alpha ~ k) (T.open_rec 0 (ftvar alpha) tau) A) ->
        P d (etype p k tau) A) ->
    (forall (d : Delta) (tau : Tau), K d tau B -> P d tau B -> P d tau A) ->
    forall (d : Delta) (t : Tau) (k : Kappa), K d t k -> P d t k.
Proof.  
  intros.
  induction H8; auto.
  pick_fresh alpha.
  applys* H5.
  pick_fresh alpha.
  applys* H6.
Qed.

Lemma K_dep_ind:
  forall P : Delta -> Tau -> Kappa -> var -> Kappa -> Prop,
    (forall (d : Delta) beta k',
         P d cint B beta k') ->
    forall (d : Delta) (t : Tau) (k : Kappa),
      AK d t k ->
      forall beta k',
        K (d & beta ~ k) t k' -> P d t k' beta k.
Proof.  
Admitted.

(* Does not work inside the induction hypotheses. *)
Lemma tst:
  forall d' d t alpha k,
    AK d t k ->
    d' = (d & alpha ~ k) ->
    forall t',
      K d' t' k ->
      K d t' k.
Proof.
  introv AKd d'd Kd.
  induction Kd.
  Focus 7.
Admitted.

Check K_ind.

(* I'm just not buying that this should be so hard. *)
Lemma K_dep_ind2:
  forall P : Delta -> Tau -> Kappa -> var -> Kappa -> Prop,
    (forall (d : Delta) t t' k beta k',
      AK d t k ->
      K (d & beta ~ k) t' k' -> 
      P d cint B beta k') ->
    (forall (d : Delta) (alpha : var) beta k',  
        get alpha d = Some B ->
        P d (ftvar alpha) B beta k') ->
    forall (d : Delta) (t : Tau) (k : Kappa),
      AK d t k ->
      forall beta k',
        K (d & beta ~ k) t k' ->
        P d t k' beta k.
Proof.  
Admitted.

(* Also failing as d' is larger because I am not
  substituting everything in. 
Lemma A_6_Subsititution_ind3:
  forall d t k,
      AK d t k ->
      forall d',
        extends d d' ->
        forall t' k',
          K d' t' k' ->
          forall alpha, 
          K d (T.subst t alpha t') k'.
Proof.
  introv AKd Ed Kd.
  induction Kd; intros; auto.
  simpl; case_var.
Admitted.
*)

Function P d t (k : Kappa) alpha k':=
  forall t', 
    K d (T.subst t alpha t') k'.

Lemma A_6_Subsititution_ind2:
  forall d t k alpha k',
      AK d t k ->
        forall t',
          K (d & alpha ~ k) t' k' ->
          K d (T.subst t alpha t') k'.
Proof.
  introv AKd Kd.
(*  apply (K_dep_ind2  P). *)
Admitted.
  
Lemma K_dep_ind3:
  forall P : Delta -> Tau -> Kappa -> var -> Tau -> Kappa -> Prop,
    (forall d beta t' k',
         P d cint B beta t' k') ->
    (forall d alpha beta t' k',
        get alpha d = Some A -> P d (ptype (ftvar alpha)) B beta t' k') ->
    (forall (d : Delta) beta t' k' (alpha : var),
        get alpha d = Some B ->
        P d (ftvar alpha) B beta t' k') ->
    (forall d t0 t1 beta t' k', 
        K d t0 A -> P d t0 A beta t' k'->
        K d t1 A -> P d t1 A beta t' k'-> P d (cross t0 t1) A beta t' k') ->
    (forall d t0 t1 beta t' k', 
        K d t0 A -> P d t0 A beta t' k'->
        K d t1 A -> P d t1 A beta t' k'-> P d (arrow t0 t1) A beta t' k') ->
    (forall d tau beta t' k',
        K d tau A -> P d tau A beta t' k' -> P d (ptype tau) B beta t' k') ->
    (forall (L : vars) (d : Delta) (k : Kappa) (tau : Tau) beta t' k',
        (forall alpha : var,
            alpha \notin L ->
            ok (d & alpha ~ k) ->
            K (d & alpha ~ k) (T.open_rec 0 (ftvar alpha) tau) A) ->
        (forall alpha : var,
            alpha \notin L ->
            ok (d & alpha ~ k) ->
            P (d & alpha ~ k) (T.open_rec 0 (ftvar alpha) tau) A beta t' k') ->
        P d (utype k tau) A beta t' k') ->
    (forall (L : vars) (d : Delta) (k : Kappa) (tau : Tau) (p : Phi) beta t' k',
        (forall alpha : var,
            alpha \notin L ->
            ok (d & alpha ~ k) -> 
            K (d & alpha ~ k) (T.open_rec 0 (ftvar alpha) tau) A) ->
        (forall alpha : var,
            alpha \notin L ->
            ok (d & alpha ~ k) -> 
            P (d & alpha ~ k) (T.open_rec 0 (ftvar alpha) tau) A beta t' k') ->
        P d (etype p k tau) A beta t' k') ->
    (forall d tau beta t' k', K d tau B -> P d tau B beta t' k' -> P d tau A beta t' k') ->
    forall (d : Delta) (t : Tau) (k : Kappa),
       K d t k ->
       forall t' k' k'' beta,
        K (d & beta ~ k) t' k' ->
        P d t k'' beta t' k'.
Proof.
  introv P H0 H1 H2 H3 H4 H5 H6 H7.
  intros d t k Kd.
  induction Kd; intros.
  admit.
  admit.
  admit.
  admit.
  admit.
  (* case ptype tau *)
  assert(FOO: P0 d (ptype tau) B beta t' k').
  apply* H4.
  apply* IHKd.
  (* but beta B vs beta A in the context issue. *)
(*
(* can solve binding cases. *)
  pick_fresh alpha.
  applys H5; intros.
  assert(NI: alpha \notin L); auto.
  apply* H8.
  apply* H10.
  admit. (* K weakening. *)

  skip.

  apply* H7.
  apply* IHK.
  admit. (* B_A conversion of some type. *)

  apply H7.
*)
Admitted.  

(* Works bug fugly, custom induction keeping AK around.  *)
Lemma A_6_Subsititution_ind3:
  forall d t k,
      AK d t k ->
      forall alpha t' k',
        K (d & alpha ~ k) t' k' ->
        K d (T.subst t alpha t') k'.
Proof.
  Function P3 d t (k : Kappa):=
      AK d t k ->
      forall alpha t' k',
        K (d & alpha ~ k) t' k' ->
        K d (T.subst t alpha t') k'.
(* Works
  lets I: K_dep_ind3.
  specialize (I P3).
  apply I.
  unfold P3.
*)
(*
  apply (K_dep_ind3 P3); unfold P3 in *; auto; intros.
  Focus 3.
  (* non-axiom case = non simple, done by induction on t' *)
  induction t'0; auto.

  assert(NIE: alpha \notin L). admit.
  assert(OK: ok (d0 & alpha ~k0)). admit.
  specialize (H alpha NIE OK).
  apply AK_AK_K in H.
  assert(KWeakend: K (d0 & alpha ~ k0 & beta ~ A) (btvar n) k'0). admit.
  (* from H2 and alpha # *)
  specialize (H0 alpha NIE OK H KWeakend).
  simpl.
  simpl in H0.

  SearchAbout(_ -> K _ _ _).
  admit. (* K strengthening *)
  (* not sure I can prove things but its interesting. *)
  assert(NIE: alpha \notin L). admit.
  assert(OK: ok (d0 & alpha ~k0)). admit.
  specialize (H alpha NIE OK).
  apply AK_AK_K in H.
  assert(KWeakend: K (d0 & alpha ~ k0 & beta ~ A) (ftvar v) k'0). admit.
  (* from H2 and alpha # *)
  specialize (H0 alpha NIE OK H KWeakend).
  simpl.
  case_var.
  simpl in H0.
  case_var.
  admit. (* not sure *)
  simpl in H0.
  case_var.
  admit. (* From H0 strengthend free. *)
  
*)

(*
 Is this really nested induction AK -> K ? NO. 

Lemma A_6_Subsititution_nested_induction:
  forall d t k,
      AK d t k ->
      forall alpha t' k',
        K (d & alpha ~ k) t' k' ->
        K d (T.subst t alpha t') k'.
Proof.
  introv AKd.
  induction AKd; introv Kd.
induction Kd; intros.
  admit.
  (* No loss of K d/d0 again. *)
*)
Admitted.


Check K_ind.

(* This remembers the d connection but one of the IH requires a false assumption. *)
Lemma A_6_Subsititution_4:
  forall d t k,
      AK d t k ->
      forall alpha t' k',
        K (d & alpha ~ k) t' k' ->
        K d (T.subst t alpha t') k'.
Proof.
  introv AKd Kd.
  inversions AKd.
  remember (d & alpha ~ k) as d'.
  induction Kd; subst; auto.
  admit.
  admit.
  simpl.
  apply_fresh K_utype; intros.
  assert(NI: y \notin L); auto.
  assert(OK: ok (d & alpha ~ k & y ~ k0)). admit.
  specialize (H0 y NI OK).
  SearchAbout (T.open_rec _ _ (T.subst _ _ _)).
  rewrite <- TP.subst_open_var.
Admitted.

(* No, alpha ~ k lost. *)

Lemma A_6_Subsititution_5:
  forall d t k,
      AK d t k ->
      forall alpha t' k',
        extends d (d & alpha ~k) ->
        K (d & alpha ~ k) t' k' ->
        K d (T.subst t alpha t') k'.
Proof.
  introv AKd E Kd.
  remember (d & alpha ~ k) as d'.  
  inversions AKd.
  induction Kd; subst; auto.
Admitted.

Inductive extends1 : Delta -> var -> Kappa -> Delta -> Prop :=
  | extends_1:
      forall alpha k d d', 
        d = d' ->
        extends1 d alpha k (d' & alpha ~ k).

Lemma A_6_Subsititution_6:
  forall d t k,
      AK d t k ->
      forall alpha d',  
        extends1 d alpha k d' ->
        forall  t' k',
          K d' t' k' ->
          K d (T.subst t alpha t') k'.
Proof.
  introv AKd Ed Kd.
  induction Kd; auto.
  admit.
  admit.
  inversions Ed.
  (* Where is extends1 d' alpha k (d' & alpha ~ k & alpha1 ~ k0)  in utype/etype
   coming from? It's not in the K definition so it's in K_ind.*)
Admitted.



Section GetProperties.
Variable A B' : Type.
Implicit Types E F : env A.
Implicit Types x : var.
Implicit Types v : A.

(** Constructor forms *)

Lemma get_empty_inv : forall x v,
  get x empty = Some v -> False.
Proof using.
  introv H. rewrite get_empty in H. false.
Qed.

Lemma get_single_eq : forall x v,
  get x (x ~ v) = Some v.
Proof using.
  intros.  rewrite get_single. case_if~.
Qed.

Lemma get_single_inv : forall x1 x2 v1 v2,
  get x1 (x2 ~ v2) = Some v1 ->
  x1 = x2 /\ v1 = v2.
Proof using.
   introv H. rewrite get_single in H.
  case_if; inversions~ H.
Qed.

Lemma get_push_inv : forall x1 v1 x2 v2 E,
  get x1 (E & x2 ~ v2) = Some v1 ->
     (x1 = x2 /\ v1 = v2)
  \/ (x1 <> x2 /\ get x1 E = Some v1).
Proof using.
  introv H.  rewrite get_push in H. case_if.
  inverts~ H. auto.
Qed.

Lemma get_push_eq : forall x v E,
  get x (E & x ~ v) = Some v.
Proof using. intros.  rewrite get_push. case_if~. Qed.

Lemma get_push_eq_inv : forall x v1 v2 E,
  get x (E & x ~ v2) = Some v1 -> v1 = v2.
Proof using.
  introv H. forwards [|]: get_push_inv H. autos*. intros [? _]. false.
Qed.

Lemma get_push_neq_inv : forall x1 x2 v1 v2 E,
  get x1 (E & x2 ~ v2) = Some v1 -> x1 <> x2 -> get x1 E = Some v1.
Proof using.
  introv H. forwards [|]: get_push_inv H.
  intros [? ?] ?. false. autos*.
Qed.

Lemma get_tail : forall x v E,
  get x (E & x ~ v) = Some v.
Proof using. intros. rewrite get_push. cases_if~. Qed.

Lemma get_push_neq : forall x1 x2 v1 v2 E,
  get x1 E = Some v1 -> x1 <> x2 -> get x1 (E & x2 ~ v2) = Some v1.
Proof using.
  introv H N.  rewrite get_push. case_if~.
Qed.

Lemma get_concat_inv : forall x v E1 E2,
  get x (E1 & E2) = Some v ->
     (get x E2 = Some v)
  \/ (x # E2 /\ get x E1 = Some v).
Proof using.
  introv H. induction E2 using env_ind.
  rewrite~ concat_empty_r in H.
  rewrite concat_assoc in H.
   forwards [[? ?]|[? M]]: get_push_inv H.
     subst. left. apply get_tail.
     forwards [?|[? ?]]: IHE2 M.
       left. applys~ get_push_neq.
       right.
       auto.
Qed.

(* Typing env vs list issues. 
Lemma get_map : forall x v (f : A -> B) E,
  get x E = Some v -> get x (map f E) = Some (f v).
Proof using.
  introv H.  rew_env_defs.
  induction E as [|[x' v'] E']; simpls.
  false.
  cases_if~. inverts~ H.
Qed.
*)

Lemma get_func : forall x v1 v2 E,
  get x E = Some v1 -> get x E = Some v2 -> v1 = v2.
Proof using.
  introv H1 H2.
  induction E as [|E' x' v'] using env_ind.
  rewrite get_empty in H1. false.
  rewrite get_push in H1,H2. case_if~.
   inverts H1. inverts~ H2.
Qed.

Lemma get_fresh_inv : forall x v E,
  get x E = Some v -> x # E -> False.
Proof using.
  introv H F.
  induction E as [|E' x' v'] using env_ind.
  rewrite get_empty in H. false.
  rewrite get_push in H. case_if~. subst.
   simpl_dom; notin_false.
Qed.

(** Derived forms *)

Lemma get_single_eq_inv : forall x v1 v2,
  get x (x ~ v2) = Some v1 ->
  v1 = v2.
Proof using.
  introv H. rewrite get_single in H.
  case_if. inverts~ H.
Qed.

Lemma get_concat_left : forall x v E1 E2,
  get x E1 = Some v ->
  x # E2 ->
  get x (E1 & E2) = Some v.
Proof using.
  introv H F. induction E2 using env_ind.
  rewrite~ concat_empty_r.
  rewrite concat_assoc.
  applys~ get_push_neq.
  subst.
  simpl_dom.
  apply notin_union in F.
  inversion F.
  apply notin_same in H0.
  inversion H0.
Qed.

Lemma get_concat_left_ok : forall x v E1 E2,
  ok (E1 & E2) ->
  get x E1 = Some v ->
  get x (E1 & E2) = Some v.
Proof using.
  introv O H. induction E2 using env_ind.
  rewrite~ concat_empty_r.
  rewrite concat_assoc in O|-*. lets [_ ?]: ok_push_inv O.
  applys~ get_push_neq. subst. applys~ get_fresh_inv H.
Qed.

Lemma get_concat_left_inv : forall x v E1 E2,
  get x (E1 & E2) = Some v ->
  x # E2 ->
  get x E1 = Some v.
Proof using.
  introv H F. lets~ [M|[? ?]]: get_concat_inv H.
    false. applys~ get_fresh_inv M.
Qed.

Lemma get_concat_right : forall x v E1 E2,
  get x E2 = Some v ->
  get x (E1 & E2) = Some v.
Proof using.
  introv H. induction E2 using env_ind.
  Check get_empty_inv.
  false. apply get_empty_inv with (x:=x) (v:=v); auto.
  rewrite concat_assoc. lets [[? ?]|[? ?]]: get_push_inv H.
    subst. applys get_tail.
    applys* get_push_neq.
Qed.

Lemma get_concat_right_inv : forall x v E1 E2,
  get x (E1 & E2) = Some v ->
  x # E1 ->
  get x E2 = Some v.
Proof using.
  introv H F. lets~ [?|[? M]]: get_concat_inv H.
    false. applys~ get_fresh_inv M.
Qed.

Lemma get_middle_eq : forall x E1 E2 v,
  x # E2 ->
  get x (E1 & x ~ v & E2) = Some v.
Proof using.
  introv F. applys~ get_concat_left.
Qed.

(** Metatheory proof forms *)

(** Interaction between binds and the insertion of bindings.
  In theory we don't need this lemma since it would suffice
  to use the get_cases tactics, but since weakening is a
  very common operation we provide a lemma for it. *)

Lemma get_weaken : forall x a E F G,
  get x (E & G) = Some a -> ok (E & F & G) ->
  get x (E & F & G) = Some a.
Proof using.
  introv H O. lets [?|[? ?]]: get_concat_inv H.
    applys~ get_concat_right.
    applys~ get_concat_left. applys~ get_concat_left_ok.
Qed.

Lemma get_remove : forall E2 E1 E3 x v,
  get x (E1 & E2 & E3) = Some v ->
  x # E2 ->
  get x (E1 & E3) = Some v.
Proof using.
  introv H F. lets [?|[? M]]: get_concat_inv H.
    applys~ get_concat_right.
    forwards: get_concat_left_inv M; auto.
    applys~ get_concat_left.
Qed.

Lemma get_subst : forall x2 v2 x1 v1 E1 E2,
  get x1 (E1 & x2 ~ v2 & E2) = Some v1 ->
  x1 <> x2 ->
  get x1 (E1 & E2) = Some v1.
Proof using.
  introv H N.
  applys~ get_remove H. 
  unfolds.
  rewrite dom_single.
  rewrite in_singleton.
  assumption.
Qed.

Lemma get_middle_eq_inv : forall x E1 E2 v1 v2,
  get x (E1 & x ~ v2 & E2) = Some v1 ->
  ok (E1 & x ~ v2 & E2) ->
  v1 = v2.
Proof using.
  introv H O. lets [? ?]: ok_middle_inv O.
  forwards~ M: get_concat_left_inv H.
  applys~ get_push_eq_inv M.
Qed.

Lemma get_middle_inv : forall x1 v1 x2 v2 E1 E2,
  get x1 (E1 & x2 ~ v2 & E2) = Some v1 ->
     (get x1 E2 = Some v1)
  \/ (x1 # E2 /\ x1 = x2 /\ v1 = v2)
  \/ (x1 # E2 /\ x1 <> x2 /\ get x1 E1 = Some v1).
Proof using.
  introv H. lets [?|[? M]]: (get_concat_inv H).
    left~.
    right. lets [N|[? N]]: (get_concat_inv M).
      lets [? ?]: (get_single_inv N). subst~.
      right. simpl_dom. split~.
      apply notin_singleton in H1.
      contradiction.
Qed.

Lemma get_not_middle_inv : forall x v E1 E2 E3,
  get x (E1 & E2 & E3) = Some v ->
  x # E2 ->
     (get x E3 = Some v)
  \/ (x # E3 /\ get x E1 = Some v).
Proof using.
  introv H F. lets [?|[? M]]: (get_concat_inv H).
    left~.
    right. forwards~ N: (get_concat_left_inv M).
Qed.

Lemma fv_in_values_binds : forall y fv x v E,
  get x E = Some v -> y \notin fv_in_values fv E -> y \notin fv v.
Proof using.
  unfold fv_in_values. introv H.
  induction E using env_ind; introv M.
  false. apply get_empty_inv with (x:= x) (v:= v); auto.
  rewrite values_def in M,IHE.
  rewrite concat_def, single_def in M. rew_list in M. simpl in M.
  lets [[? ?]|[? ?]]: (get_push_inv H); subst~.
Qed.

End GetProperties.

Lemma ok_commutes: 
forall A (E : env A) F G, 
  ok (E & F & G) = ok (E & (F & G)).
Admitted.

Lemma K_context_commutes:
forall E F G tau k, 
  K (E & F & G) tau k = K (E & (F & G)) tau k.
Admitted.

Lemma K__lc:
  forall d t k,
    K d t k ->
    T.lc t.
Admitted.

Lemma A_6_Subsititution_7:
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

  apply get_middle_eq_inv in H; subst; auto.
  apply get_subst in H; subst; auto.

  simpl.
  apply_fresh K_utype.
  intros.
  assert(NI: y \notin L). admit.
  assert(OKB: ok (d & alpha ~ k & d' & y ~ k0)). admit.
  specialize (H y NI OKB).
  specialize (H0 y NI OKB OKB (d' & y ~ k0)).
  rewrite <- ok_commutes in H0.
  rewrite <- K_context_commutes in H0.
  rewrite <- K_context_commutes in H0.
  assert(KW: K (d & d' & y ~ k0) t k). admit. (* k weakening *)
  assert(CC: d & alpha ~ k & d' & y ~ k0 = d & alpha ~ k & (d' & y ~ k0)). admit.
  (* contexts commute, meta theorem I must accept. *)
  specialize (H0 H1 KW CC).
  rewrite* <- TP.subst_open_var.
  apply K__lc with (d:= (d&d')) (k:=k); auto.
  apply K_B_A.
  apply* IHKdakd'.
Qed.