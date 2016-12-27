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
  induction d.
  rewrite <- empty_def in H.
  rewrite get_empty in H.
  inversion H.
  (* working, list vs env issues. *)
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
  forall tau,
    K empty tau A ->
    T.fv tau = \{}.
Proof.
  intros.
  lets: K_fv tau (@empty Kappa).
  apply H0 in H.
  unfold fv_delta in H.
  rewrite dom_empty in H.
  (* where is X \c \{} -> x = \{} *)
Admitted.

Lemma ok_strengthing:
  forall (d' : Delta) y k, 
    ok(d' & y ~ k) ->
    forall d, 
      extends d d' ->                
      ok(d & y ~ k).
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


Lemma K_fv_delta:
  forall tau d k,
    ok d ->
    K d tau k ->
    T.fv tau \c dom d.
Proof.
  introv OKd Kd.
  induction Kd; simpl; auto; auto with fset.
  admit.
  admit.
  (* We definitely want a strong subset prover. *)
  admit.
  admit.
  (* We definitely want some LN lemmas on FV of the base set. *)
  pick_fresh alpha.
  assert(NI: alpha \notin L); auto.
  assert(NId: alpha \notin dom d); auto.
  assert(OK: ok (d & alpha ~ k)); auto.
  specialize (H0 alpha NI OK).
  specializes* H0.
  (* Just not strong enough, one must be able to parameterize about judgments. *)
  apply TP.open_var_fv in H0.


  

Lemma A_4_Useless_Substitution_1:
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
  SearchAbout(_ -> T.open_rec _ _ _ = _).