(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Term Weakening  - DEAD CODE 


*)

Set Implicit Arguments.
Require Export Cyclone_Formal_Syntax Cyclone_Static_Semantics_Kinding_And_Context_Well_Formedness.
Require Export Cyclone_Static_Semantics_Typing_Heap_Objects.
Require Export Cyclone_Classes Cyclone_Inductions Cyclone_LN_Tactics Cyclone_LN_Extra_Lemmas_And_Automation.
Require Export Cyclone_Well_Formedness_Lemmas.
Require Export Cyclone_Context_Weakening_Proof.
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

(* Finish *)
