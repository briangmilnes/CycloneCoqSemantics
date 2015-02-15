(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Defining type safety, page 67.

*)

Set Implicit Arguments.
Require Export LanguageModuleDef.

Require Export DynamicSemanticsTypeSubstitution.
Require Export DynamicSemanticsHeapObjects.
Require Export DynamicSemantics.
Require Export DynamicSemanticsTypeSubstitution.
Require Export StaticSemanticsKindingAndContextWellFormedness.
Require Export StaticSemanticsKindingLemmas.
Require Export StaticSemanticsWellFormednessLemmas.

Require Export StaticSemantics.
Require Export TypeSafety.
Require Export CpdtTactics.
Require Export Case.
Require Export TacticNotations.
Require Export MoreTacticals.

Require Export AlphaConversion.

Lemma substitution_with_different_type_variables:
  forall (alpha beta: TV.T),
    TV.beq_t beta alpha = false ->
    forall (tau : Tau),
      subst_Tau (tv_t alpha) tau beta = tv_t alpha.
Proof.
  intros alpha beta neqalphabeta tau.
  unfold subst_Tau.
  rewrite neqalphabeta.
  reflexivity.
Qed.

Lemma substitution_with_different_type_variables_ptype:
  forall (alpha beta: TV.T),
    TV.beq_t beta alpha = false ->
    forall (tau : Tau),
      subst_Tau (ptype (tv_t alpha)) tau beta = (ptype (tv_t alpha)).
Proof.
  intros alpha beta neqalphabeta tau.
  unfold subst_Tau.
  rewrite neqalphabeta.
  reflexivity.
Qed.

Lemma A_4_Useless_Substitutions_1:
  forall (d : Delta) (tau' : Tau) (k : Kappa),
    K d tau' k ->
    forall(alpha : TV.T),
      D.map d alpha = None ->
      forall (tau : Tau),
        subst_Tau tau' tau alpha = tau'.
Proof.
  intros d tau' k kder.
  K_ind_cases (induction kder) Case.

  Case  "K d cint B".
   intros alpha AlphaNotInDomd tau.
   reflexivity.
  Case  "K d (tv_t alpha) B".
    intros alpha0 AlphaNotInDomd tau.
    apply D.map_some_none_beq_t_false with (k':= alpha) (t:= B) in AlphaNotInDomd;
      try assumption.
    apply substitution_with_different_type_variables; try assumption.
  Case  "K d (ptype (tv_t alpha)) B".
    intros alpha0 AlphaNotInDomd tau.
    apply D.map_some_none_beq_t_false with (k':= alpha) (t:= A) in AlphaNotInDomd;
      try assumption.
    apply substitution_with_different_type_variables_ptype; try assumption.
  Case  "K d tau A".
   intros alpha AlphaNotInDomd tau0.   
   apply IHkder with (tau0 := tau0) in AlphaNotInDomd.
   assumption.
  Case  "K d (cross t0 t1) A".
   crush.
  Case  "K d (arrow t0 t1) A".
   crush.
  Case  "K d (ptype tau) B".
   intros. (* crush does this but why not look at a case. *)
   apply IHkder with (tau0:= tau0) in H.
   unfold subst_Tau.
   fold subst_Tau.
   rewrite H.
   reflexivity.
  Case  "K d (utype alpha k tau) A".
   intros alpha0 AlphaNotInDomd tau0.
   (* Am I unfolding too soon ?  No same stuck point. *)
   case_eq (TV.beq_t alpha0 alpha).
   SCase "alpha0 = alpha".
    intros.
    simpl.
    rewrite H1.
    reflexivity.
   SCase "alpha0 <> alpha".
    intros.
    unfold subst_Tau.
    fold subst_Tau.
    rewrite H1.
    specialize (IHkder alpha0).
    assert (Z: D.map (dctxt alpha k d) alpha0 = None).
    apply D.map_none_r_str; try assumption.
    apply IHkder with (tau0:= tau0) in Z.
    rewrite Z.
    reflexivity.
  Case  "K d (etype p alpha k tau) A)".
   intros alpha0 AlphaNotInDomd tau0.
   unfold subst_Tau.
   fold subst_Tau.
   case_eq (TV.beq_t alpha0 alpha).
   SCase "alpha0 = alpha".
    intros.
    (* The induction hypothesis is false, to tau0 must be connected by? *)
    apply TV.beq_t_eq in H1.
    (* Is this now AlphaConversion? *)
    reflexivity.
   SCase "alpha0 <> alpha".
    intros.
    specialize (IHkder alpha0).
    assert (Z: D.map (dctxt alpha k d) alpha0 = None).
    apply D.map_none_r_str; try assumption.
    apply IHkder with (tau0:= tau0) in Z.
    rewrite Z.
    reflexivity.
Qed.

Lemma A_4_Useless_Substitutions_2:
  forall (d : Delta) (alpha : TV.T),
    D.map d alpha = None ->
    forall (g : Gamma), 
      WFDG d g ->
      forall (tau : Tau),
        subst_Gamma g tau alpha = g.
Proof.
  intros d alpha getd g WFDGder.
  WFDG_ind_cases (induction WFDGder) Case.
  Case "WFDG d []".
   intros.
   reflexivity.
  Case "WFDG d ([(x, tau)] ++ g)".
   intros.
   assert (Z: D.map d alpha = None). 
   assumption.
   apply IHWFDGder with (tau:= tau0) in getd.
   unfold subst_Gamma.
   simpl.
   fold subst_Gamma.
   rewrite getd.
   rewrite A_4_Useless_Substitutions_1 with (d:=d) (k:=A); try assumption.
   reflexivity.
  Case "WFDG ([(alpha, k)] ++ d) g".
   intros tau.
   inversion getd.
   destruct (D.K_eq alpha alpha0).
   inversion H1.
   apply IHWFDGder with (tau:= tau) in H1.
   assumption.
Qed.  

Lemma A_4_Useless_Substitutions_3:
  forall (d : Delta) (alpha : TV.T),
    D.map d alpha = None ->
    forall (u: Upsilon) (x : EV.T) (p : Path) (tau': Tau),
        WFU u ->
        U.map u (x,p) = Some tau' ->
        forall (tau : Tau),
          subst_Tau tau' tau alpha = tau'.
Proof.
  intros d alpha mapder u x p tau' WFUder.
  WFU_ind_cases (induction WFUder) Case.
  Case "WFU []".
   intros.
   inversion H.
  Case "WFU ([(x, p, tau)] ++ u)".
   intros.
   unfold uctxt in H1.
   unfold U.map in H1.
   fold U.map in H1.
   case_eq(U.K_eq (x,p) (x0,p0)); intros; rewrite H2 in *.
   inversion H1.
   subst.
   apply A_4_Useless_Substitutions_1 with (alpha:= alpha) (tau:= tau0) in H0;
      try assumption.
    reflexivity.
    crush.
Qed.

Lemma NotFreeIn_Tau_subst_useless:
  forall (beta : TV.T) (tau : Tau),
    NotFreeInTau beta tau ->
     forall (tau' : Tau),
       subst_Tau tau tau' beta = tau.
Proof.
  intros.
  Tau_ind_cases(induction tau) Case.
  Case "(tv_t t)".
   case_eq (D.K_eq beta v).
   SCase "beta = v".
    intros.
    unfold NotFreeInTau in H.
    unfold D.K_eq in H0.
    unfold TV.beq_t in H.
    unfold TV.beq_t in H0.
    rewrite H0 in H.
    inversion H.
   SCase "beta <> t".
    intros.
    unfold subst_Tau.
    (* uneccesary unfolding! *)
    unfold D.K_eq in H0.
    rewrite H0.
    reflexivity.
  Case "cint".
   crush.
  Case "(cross t t0)".
   crush.
  Case "(arrow t t0)".
   crush.
  Case "(ptype t)".
   crush.
  Case "(utype t k t0)".
   case_eq (D.K_eq beta v).
   SCase "beta = v".
    intros.
    unfold subst_Tau.
    fold subst_Tau.
    unfold D.K_eq in H0.
    rewrite H0.
    reflexivity.
   SCase "beta <> t".
    intros.
    unfold subst_Tau.
    fold subst_Tau.
    unfold D.K_eq in H0.
    rewrite H0.
    unfold NotFreeInTau in H.
    fold NotFreeInTau in H.
    rewrite H0 in H.
    apply IHtau in H.
    rewrite H.
    reflexivity.
  Case "(etype p t k t0)".
   case_eq (D.K_eq beta v).
   SCase "beta = v".
    intros.
    unfold subst_Tau.
    fold subst_Tau.
    unfold D.K_eq in H0.
    rewrite H0.
    reflexivity.
   SCase "beta <> v".
    intros.
    unfold subst_Tau.
    fold subst_Tau.
    unfold D.K_eq in H0.
    rewrite H0.
    unfold NotFreeInTau in H.
    fold NotFreeInTau in H.
    rewrite H0 in H.
    apply IHtau in H.
    rewrite H.
    reflexivity.
Qed.    

Lemma A_5_Commuting_Substitutions:
  forall (beta : TV.T) (t2 : Tau),
    NotFreeInTau beta t2 ->
    forall (alpha : TV.T) (t0 t1 : Tau),
      (subst_Tau (subst_Tau t0 t1 beta) t2 alpha) =
      (subst_Tau (subst_Tau t0 t2 alpha)
                 (subst_Tau t1 t2 alpha)
                 beta).
Proof.
(*
  intros beta t2 notfreeder alpha t0.
  (Tau_ind_cases (induction t0) Case).
  (* crush leaves 3/7. *)
  Case "(tv_t t)".
    intros.
    case_eq (D.K_eq alpha beta); case_eq (D.K_eq alpha t); case_eq (D.K_eq beta t); crush.
    SCase "alpha = beta = t".
     apply NotFreeIn_Tau_subst_useless with (tau':= (subst_Tau t1 t2 alpha)) in notfreeder.
     rewrite notfreeder.
     admit.
     admit.
     admit.
     admit.
   Case "cint".
    crush.
   Case "(cross t t0)".
    crush.
   Case "(arrow t t0)".
    crush.
   Case "(ptype t)".
    crush.
   Case "(utype t k t0)".
    intros.
    unfold subst_Tau.
    fold subst_Tau.
    admit.
   Case "(etype p t k t0)".
    admit. 
*)
Admitted.

Lemma A_6_Substitution_1:
  forall (d : Delta) (tau : Tau) (k : Kappa),
      WFD d ->
      AK d tau k ->
      forall (alpha : TV.T) (k' : Kappa) (tau' : Tau), 
        WFD (dctxt alpha k d) ->
        K (dctxt alpha k d) tau' k' ->
        K d (subst_Tau tau' tau alpha) k'.
Proof.
  intros d tau k WFDder AKderd alpha k' tau' WFDder' Kderctxt.
  apply (K_context_dependent_induction
           (fun (alpha : TV.T) (k : Kappa) (d : Delta) (tau' : Tau) (k' : Kappa) =>
              AK d tau k ->
              WFD (dctxt alpha k d) ->
              K (dctxt alpha k d) tau' k' ->
              K d (subst_Tau tau' tau alpha) k'))
        with (k:= k); try assumption; intros; clear AKderd; clear Kderctxt.
 Case "K d cint B".
   simpl.
   apply K_int.
 Case "K d (tv_t alpha) B".
   unfold dctxt in H1.
   unfold D.map in H.
   fold D.map in H.
   case_eq(D.K_eq a' alpha0); intros; rewrite H3 in H; inversion H; subst.
   unfold D.K_eq in H3.
   apply D.K.beq_t_eq in H3.
   subst.
   simpl.
   rewrite TV.beq_t_refl.
   inversion H0.
   subst.
   assumption.
   unfold subst_Tau.
   unfold D.K_eq in H3.
   rewrite D.K.beq_t_sym in H3.
   rewrite H3.
   constructor; try assumption.
 Case "K d (ptype (tv_t alpha)) B".
  unfold subst_Tau.
  rewrite TV.beq_t_refl.
  simpl in H.
  unfold D.K_eq in H.
  rewrite D.K.beq_t_refl in H.
  inversion H.
  subst.
  inversion H0;  subst.
  constructor; try assumption.
  constructor; try assumption.
 Case "K d tau A".
  unfold dctxt in H0.
  apply H0 in H1; try assumption.
  constructor; try assumption.
 Case "K d (cross t0 t1) A".
   unfold subst_Tau.
   fold subst_Tau.
   pose proof H3 as H3'.
   apply H0 in H3; try assumption.
   apply H2 in H3'; try assumption.
   apply K_cross; try assumption.   
 Case "K d (arrow t0 t1) A".
   unfold subst_Tau.
   fold subst_Tau.
   pose proof H3 as H3'.
   apply H0 in H3; try assumption.
   apply H2 in H3'; try assumption.
   apply K_arrow; try assumption.   
 Case "K d (ptype tau) B".
  apply H0 in H1; try assumption.
  unfold subst_Tau.
  fold subst_Tau.
  constructor.
  assumption.
 Case "K d (utype alpha k tau) A".
   apply H1 in H2; try assumption.
   unfold subst_Tau.
   fold subst_Tau.
   case_eq(TV.beq_t alpha0 a'); intros.
   apply TV.beq_t_eq in H5.
   subst.
   apply K_utype; try assumption.
   apply K_utype; try assumption.
   AdmitAlphaConversion.
   AdmitAlphaConversion.
   inversion H3; subst.
   assert(Z: D.extends d0 (dctxt a' k0 d0) = true); try assumption.
   apply D.extends_r_str; try assumption.
   apply D.extends_refl.
   apply WFD_implies_nodup; assumption.
   unfold D.nodup.
   fold D.nodup.
   case_eq(D.map d0 a'); intros.
   AdmitAlphaConversion.
   apply WFD_implies_nodup; try assumption.
   apply K_weakening with 
    (d:= d0) (d':= (dctxt a' k0 d0))
    (tau:=(subst_Tau tau0 tau alpha0)) (k:= A) in H10;
     try assumption.
   constructor; try assumption.
   AdmitAlphaConversion; try assumption.
 Case "K d (etype p alpha k tau) A)"  .
   apply H2 in H3; try assumption.
   unfold subst_Tau.
   fold subst_Tau.
   case_eq(TV.beq_t alpha0 a'); intros.
   apply TV.beq_t_eq in H6.
   subst.
   apply K_etype; try assumption.
   apply K_etype; try assumption.
   AdmitAlphaConversion.
   AdmitAlphaConversion.
   inversion H4; subst.
   assert(Z: D.extends d0 (dctxt a' k0 d0) = true); try assumption.
   apply D.extends_r_str; try assumption.
   apply D.extends_refl.
   apply WFD_implies_nodup; assumption.
   unfold D.nodup.
   fold D.nodup.
   case_eq(D.map d0 a'); intros.
   AdmitAlphaConversion.
   apply WFD_implies_nodup; try assumption.
   apply K_weakening with 
    (d:= d0) (d':= (dctxt a' k0 d0))
    (tau:=(subst_Tau tau0 tau alpha0)) (k:= A) in H11;
     try assumption.
   constructor; try assumption.
   AdmitAlphaConversion; try assumption.
Qed.
(* Caol Islay 13 Signatory. *)

Lemma A_6_Substitution_2:
  forall (d : Delta) (tau : Tau) (k : Kappa),
       WFD d ->
       AK d tau k -> 
       forall  (alpha : TV.T)  (tau' : Tau)  (k' : Kappa),
         WFD (dctxt alpha k d) ->
         AK (dctxt alpha k d) tau' k' ->
         AK d (subst_Tau tau' tau alpha) k'.
Proof.
  intros d tau k AKderd alpha tau' k' AKdctextder.
  apply (AK_context_induction_dependent
           (fun (alpha : TV.T) (k : Kappa) (d : Delta) (tau' : Tau) (k' : Kappa) =>
              AK d tau k -> 
              WFD (dctxt alpha k d) ->
              AK (dctxt alpha k d) tau' k' ->
              AK d (subst_Tau tau' tau alpha) k'))
        with (k:= k); try assumption; intros; clear AKderd; clear AKdctextder.
 Case "AK d (tv_t alpha) A".
  constructor; try assumption.
  inversion H1; subst; try assumption.
  inversion H2; subst; try assumption.
  apply A_6_Substitution_1 with (k:= k'0); try assumption.

  unfold subst_Tau.
  unfold dctxt in H3.
  unfold D.map in H3.
  fold D.map in H3.
  unfold D.K_eq in H3.
  case_eq(TV.beq_t alpha0 alpha1); intros; rewrite TV.beq_t_sym in H4;   rewrite H4 in H3.
  admit.
  inversion H3.
  admit.
 Case "AK d (subst_Tau (tv_t alpha0) alpha k) A"  .
  unfold subst_Tau.
  case_eq(TV.beq_t alpha0 a'); intros.
  unfold D.map in H.
  fold D.map in H.
  unfold D.K_eq in H.
  rewrite TV.beq_t_sym in H3.
  rewrite H3 in H.
  inversion H; subst.
  assumption.
  unfold D.map in H.
  fold D.map in H.
  unfold D.K_eq in H.
  rewrite TV.beq_t_sym in H3.
  rewrite H3 in H.
  apply AK_A; try assumption.
Admitted.

Lemma A_6_Substitution_3:
  forall (tau : Tau) (d : Delta)  (k : Kappa),
    WFD d ->
    AK d tau k -> 
    forall (alpha : TV.T) (tau' : Tau),
      WFD (D.ctxt alpha k d) -> 
      ASGN (D.ctxt alpha k d) tau' ->
      ASGN d (subst_Tau tau' tau alpha).
Proof.
  intros tau d k WFDd AKder alpha tau' WFDalphakd ASGNder.
  apply (ASGN_context_induction_dependent
           (fun (alpha : TV.T) (k : Kappa) (d : Delta) (tau' : Tau) =>
              AK d tau k -> 
              WFD (D.ctxt alpha k d) -> 
              ASGN (D.ctxt alpha k d) tau' ->
              ASGN d (subst_Tau tau' tau alpha)))
        with (k:=k); try assumption; intros; 
             clear AKder; clear ASGNder; clear WFDalphakd.
  Case "ASGN d cint".
   crush.
  Case "ASGN d (tv_t alpha)".
   unfold subst_Tau.
   case_eq(TV.beq_t beta alpha0); intros.
   apply TV.beq_t_eq in H3; subst.
   apply WFD_implies_nodup in H1.
   apply D.nodup_map_some_context_absurd 
         with (t':= B) in H; try assumption.
    inversion H.
   constructor; try assumption.
  Case "ASGN d (ptype tau)".
   crush.
  Case "ASGN d (cross t0 t1)".
   inversion H5; subst.
   simpl.
   constructor.
   apply H0 in H3; try assumption.
   apply H2 in H3; try assumption.
  Case "ASGN d (arrow t0 t1)".
   inversion H5; subst.
   simpl.
   constructor.
   apply H0 in H3; try assumption.
   apply H2 in H3; try assumption.
  Case "ASGN d (utype alpha k tau)".
   simpl.
   case_eq(TV.beq_t beta alpha0); intros.
   constructor; try assumption.
   constructor; try assumption.
   (* AK weakening using extends for this. ASGN weakening would be required. *)
   inversion H3; subst.
   pose proof H10 as H10'.
   apply WFD_weakening with (alpha:= alpha0) (k:= k1) in H10'; try assumption.
   assert (Z: D.extends d0 d0 = true).
   apply D.extends_refl.
   apply WFD_implies_nodup in H10; try assumption.
   assert (Y: D.extends d0 (D.ctxt alpha0 k1 d0) = true).
   apply D.extends_r_str; try assumption.
   apply WFD_implies_nodup in H10'.
   assumption.
   apply AK_weakening with (d':= (D.ctxt alpha0 k1 d0)) in H2; try assumption.
   apply WFD_weakening with (alpha:= beta) (k:= k1) in H10'; try assumption.
   assert(R: ASGN (D.ctxt beta k1 (D.ctxt alpha0 k1 d0)) tau0).
   admit. (* ASGN str *)
   apply H1 in H2; try assumption.
   assert (G: D.K_eq beta alpha0 = false).
   admit. (* had this from wfd *)
   unfold dctxt.
   unfold D.map.
   fold D.map.
   rewrite G; assumption.

   Case "ASGN d (etype witnesschanges alpha k tau))".
   admit.
Qed.

Lemma A_6_Substitution_4:
  forall (d : Delta) (g : Gamma) (tau : Tau) (k : Kappa),
    WFDG d g ->
    AK d tau k -> 
    forall (alpha : TV.T),
      WFDG (D.ctxt alpha k d) g ->
      WFDG d (subst_Gamma g tau alpha).
Proof.
  intros d g tau k WFDGder AKder alpha WFDder.
  apply (WFDG_context_dependent_induction
           (fun (alpha : TV.T) (k : Kappa) (d : Delta) (g : Gamma) =>
              AK d tau k -> 
              WFDG (D.ctxt alpha k d) g ->
              WFDG d (subst_Gamma g tau alpha)))
        with (k:= k); try assumption; intros; clear AKder; clear WFDGder.
  Case "WFDG d []".
   intros.
   simpl.
   constructor.
  Case "WFDG d ([(x, tau)] ++ g)".
   intros.
   simpl.
   constructor.
   admit.
   inversion H1.
   crush.
   admit.
   admit.
   admit.
   admit.
   (* This case is missing from the thesis, let's see if the proof works. *)
  Case "WFDG ([(alpha, k)] ++ d) g".
   intros.
   admit.
Qed.

Lemma A_6_Substitution_5:
  forall (alpha : TV.T) (k : Kappa) (d : Delta) (u : Upsilon)  (g : Gamma),
    WFC (dctxt alpha k d) u g ->
    forall (tau : Tau) ,
      AK d tau k -> 
      WFC d u (subst_Gamma g tau alpha).
Proof.
  intros alpha k d u g WFCder.
  inversion WFCder.
  intros.
  constructor; try assumption.
  inversion H; try assumption.
  apply A_6_Substitution_4 with (k:=k); try assumption.
  subst.
Admitted.

(* Thesis Bug, no AK is required. *)
Lemma A_6_Substitution_6: 
  forall (s : St),
      ret s ->
      forall (alpha : TV.T) (tau : Tau),
        ret (subst_St s tau alpha).
Proof.
  intros s retder.
  induction retder.
  (* crush gets 0. *)
  (* I can do these by hand or build an Ltac to do them. *)
  intros alpha tau.
  destruct e; 
    try (try intros alpha; try compute; constructor).
  
  Ltac foldunfold' :=
    try (intros alpha;
         unfold subst_St;
         fold subst_E;
         fold subst_St;
         constructor;
         crush).

  Case "ret (if_s e s1 s2)".
    foldunfold'.

  Case "ret (seq s s') 1".
   foldunfold'.

  Case "ret (seq s s') 2".
    intros alpha tau.
    unfold subst_St.
    fold subst_E.
    fold subst_St.
    apply ret_seq_2. (* Constructor takes the first rule, not all cases. *)
    crush.

  Case "ret (letx x e s)".
   foldunfold'.

  Case "ret (open e alpha x s)".
   intros alpha0 tau0.
   unfold subst_St.
   fold subst_E.
   fold subst_St.
   specialize (IHretder alpha0 tau0).
   constructor.
   assumption.

  Case "ret (openstar e alpha x s))".
   intros alpha0 tau0.
   unfold subst_St.
   fold subst_E.
   fold subst_St.
   specialize (IHretder alpha0 tau0).
   constructor.
   assumption.
Qed.


Lemma A_6_Substitution_7:
  forall (u : Upsilon) (x : EV.T) (p p': Path) (t1 t2: Tau),
    gettype u x p t1 p' t2 ->
    forall (d: Delta) (tau : Tau) (k : Kappa) (beta : TV.T),
      AK d tau k -> 
      WFU u ->
        gettype u x p (subst_Tau t1 tau beta) p' (subst_Tau t2 tau beta).
Proof.
  intros u x p p' t1 t2 gettypder.
  apply (gettype_ind 
           (fun (u : Upsilon) (x : EV.T) (p : Path) (t1 : Tau) (p' : Path) (t2 : Tau) =>
              forall (d: Delta) (tau : Tau) (k : Kappa) (beta : TV.T),
                AK d tau k -> 
                WFU u ->
                gettype u x p (subst_Tau t1 tau beta) p' (subst_Tau t2 tau beta))).
  Case "gettype u x p tau [] tau".
   intros.
   constructor.
  Case "gettype u x p (cross t0 t1) (i_pe zero_pe :: p') tau".
   intros.
   simpl.
   constructor.
   apply H0 with (beta:= beta) in H1; try assumption.
  Case "gettype u x p (cross t0 t1) (i_pe one_pe :: p') tau".
   intros.
   simpl.
   constructor.
   apply H0 with (beta:= beta) in H1; try assumption.
  Case "gettype u x p (etype aliases alpha k tau') (u_pe :: p') tau)".
   intros.
   simpl.
   destruct (D.K_eq beta alpha).
   
   admit.
   admit.
   (* 

   apply gettype_etype with (tau'':= tau''); try assumption.
   (* The alpha is from the etype. *)
   apply H1  with 
    (d:= d) (tau0:= tau0) (k:=k0) (beta:= beta) in H2; try assumption.
   crush.
   (* Is this alpha conversion? It does not seem so. *)
   (* Alpha and alpha0 swapped in goal term. Capture? Bug? *)
   admit.
*)
   admit.
Qed.

(* Do partial proofs changing the induction schema manually with a subst to
learn what I need. *)
(* AK detatched so I can't work from this. I must work from the mutual
 inductive schema. *)
(*
Lemma A_6_Substitution_8_1_2_3_bad:
  forall (d : Delta) (tau : Tau) (k : Kappa),
    AK d tau k ->
    forall (alpha : TV.T) (u : Upsilon) (g : Gamma) (e : E) (tau' : Tau) 
            (d : Delta),
      ltyp (dctxt alpha k d) u g e tau' ->
      ltyp d u (subst_Gamma g tau alpha)
           (subst_E e tau alpha)
           (subst_Tau tau' tau alpha).
Proof.
  intros d tau k AKder alpha u g e tau' d' ltypder.
  Ltac fixit d0 alpha k d':=  assert (Z: d0 = (dctxt alpha k d')).
  induction ltypder; intros.
  fixit d0 alpha k d'.
  admit.
  subst.
  admit.

  fixit d0 alpha k d'.
  admit.
  subst.
  admit.

  fixit d0 alpha k d'.
  admit.
  subst.
  unfold subst_E.
  fold subst_E.
  apply SL_3_3 with (t1:= t1); try assumption.
  admit.

  fixit d0 alpha k d'.
  admit.
  subst.
  admit.
Admitted.
*)


Lemma A_6_Substitution_8_1_2_3:
  forall (d : Delta),
    forall (alpha : TV.T) (u : Upsilon) (g : Gamma) (e : E) (tau' : Tau) 
            (d : Delta),
      ltyp d u g e tau' ->
      forall (tau : Tau) (k : Kappa),
      AK d tau k ->
      ltyp d u (subst_Gamma g tau alpha)
           (subst_E e tau alpha)
           (subst_Tau tau' tau alpha).
Proof.
  intros d alpha u g e tau' d' ltypder.
  Ltac fixit d0 alpha k d':=  assert (Z: d0 = (dctxt alpha k d')).
  (apply (ltyp_ind_mutual
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (tau' : Tau) (s : St)
                (st : styp d u g tau' s) => 
              styp d u g tau' s ->
              forall (tau : Tau) (k : Kappa),
                AK d tau k ->
                styp d u (subst_Gamma g tau alpha)
                     (subst_Tau tau' tau alpha)
                     (subst_St s tau alpha))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau' : Tau) 
                (lt : ltyp d u g  e tau') =>
              ltyp d u g e tau' ->
              forall (tau : Tau) (k : Kappa),
                AK d tau k ->
                ltyp d u (subst_Gamma g tau alpha)
                     (subst_E e tau alpha)
                     (subst_Tau tau' tau alpha))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau' : Tau) 
                (rt : rtyp d u g e tau') =>
              rtyp d u g e tau' ->
              forall (tau : Tau) (k : Kappa),
                AK d tau k ->
                rtyp d u (subst_Gamma g tau alpha)
                     (subst_E e tau alpha)
                     (subst_Tau tau' tau alpha)))); try assumption; intros.
  (* 26 goals, each one must be hand repaired. *)
  (* After a lot of manipulation, this should be the right context to prove. *)
  fixit d0 alpha k d'.
  admit.
  rewrite Z in r.
  rewrite Z in H at 1.
  rewrite Z in H0.
  clear Z.

  apply H with (tau:= tau0) (k:= k) in r; try assumption.
  




Admitted.



(* Need three of these. *)
(* I have no idea how to make the dependent induction mutual schema. *)
Lemma A_6_Substitution_8_1_2_3:
  forall (d : Delta) (tau : Tau) (k : Kappa),
    AK d tau k ->
    forall (alpha : TV.T) (u : Upsilon) (g : Gamma) (e : E) (tau' : Tau) 
            (d : Delta),
      ltyp (dctxt alpha k d) u g e tau' ->
      ltyp d u (subst_Gamma g tau alpha)
           (subst_E e tau alpha)
           (subst_Tau tau' tau alpha).
Proof.
  intros d tau k AKder.
  intros alpha u g e tau' d' ltypder.
  Ltac fixit d0 alpha k d':=  assert (Z: d0 = (dctxt alpha k d')).
  ltyp_ind_mutual_cases 
  (apply (ltyp_context_dependent_induction_mutual
           (fun (beta : TV.T) (k' : Kappa) (d : Delta) (u : Upsilon) (g : Gamma) (t : Tau) (s : St)
                (st : styp d u g t s) => 
              styp (dctxt alpha k d) u g tau' s ->
              styp d u (subst_Gamma g tau alpha)
                   (subst_Tau tau' tau alpha)
                   (subst_St s tau alpha))
           (fun (beta : TV.T) (k' : Kappa) (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau' : Tau) 
                (lt : ltyp d u g  e tau') =>
              ltyp (dctxt alpha k d) u g e tau' ->
              ltyp d u (subst_Gamma g tau alpha)
                   (subst_E e tau alpha)
                   (subst_Tau tau' tau alpha))
           (fun (beta : TV.T) (k' : Kappa) (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (rt : rtyp d u g e t) =>
              rtyp (dctxt alpha k d) u g e tau' ->
              rtyp d u (subst_Gamma g tau alpha)
                   (subst_E e tau alpha)
                   (subst_Tau tau' tau alpha))); try assumption) Case; intros;
  clear AKder; clear ltypder.
  
  

Admitted.    
