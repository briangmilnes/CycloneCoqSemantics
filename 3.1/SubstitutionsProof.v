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
Require Export StaticSemantics.
Require Export TypeSafety.
Require Export CpdtTactics.
Require Export Case.
Require Export TacticNotations.
Require Export MoreTacticals.

Require Export AlphaConversion.

Print beq_tvar.

Lemma substitution_with_different_type_variables:
  forall (alpha beta: TVar),
    beq_tvar beta alpha = false ->
    forall (tau : Tau),
      subst_Tau (tv_t alpha) tau beta = tv_t alpha.
Proof.
  intros alpha beta neqalphabeta tau.
  unfold subst_Tau.
  rewrite neqalphabeta.
  reflexivity.
Qed.

Lemma substitution_with_different_type_variables_ptype:
  forall (alpha beta: TVar),
    beq_tvar beta alpha = false ->
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
    forall(alpha : TVar),
      DM.map d alpha = None ->
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
    apply DM.map_some_none_beq_t_false with (k':= alpha) (t:= B) in AlphaNotInDomd;
      try assumption.
    apply substitution_with_different_type_variables; try assumption.
  Case  "K d (ptype (tv_t alpha)) B".
    intros alpha0 AlphaNotInDomd tau.
    apply DM.map_some_none_beq_t_false with (k':= alpha) (t:= A) in AlphaNotInDomd;
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
   apply IHkder with (tau0:= tau0) in H0.
   unfold subst_Tau.
   fold subst_Tau.
   rewrite H0.
   reflexivity.
  Case  "K d (utype alpha k tau) A".
   intros alpha0 AlphaNotInDomd tau0.
   (* Am I unfolding too soon ?  No same stuck point. *)
   case_eq (beq_tvar alpha0 alpha).
   SCase "alpha0 = alpha".
    intros.
    simpl.
    rewrite H2.
    reflexivity.
   SCase "alpha0 <> alpha".
    intros.
    unfold subst_Tau.
    fold subst_Tau.
    rewrite H2.
    specialize (IHkder alpha0).
    assert (Z: DM.map (dctxt alpha k d) alpha0 = None).
    apply DM.map_none_r_strengthen; try assumption.
    apply IHkder with (tau0:= tau0) in Z.
    rewrite Z.
    reflexivity.
  Case  "K d (etype p alpha k tau) A)".
   intros alpha0 AlphaNotInDomd tau0.
   unfold subst_Tau.
   fold subst_Tau.
   case_eq (beq_tvar alpha0 alpha).
   SCase "alpha0 = alpha".
    intros.
    (* The induction hypothesis is false, to tau0 must be connected by? *)
    apply beq_var_eq in H2.
    (* Is this now AlphaConversion? *)
    AdmitAlphaConversion.
   SCase "alpha0 <> alpha".
    intros.
    specialize (IHkder alpha0).
    assert (Z: DM.map (dctxt alpha k d) alpha0 = None).
    apply DM.map_none_r_strengthen; try assumption.
    apply IHkder with (tau0:= tau0) in Z.
    rewrite Z.
    reflexivity.
Qed.

Lemma A_4_Useless_Substitutions_2:
  forall (d : Delta) (alpha : TVar),
    DM.map d alpha = None ->
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
   assert (Z: DM.map d alpha = None). 
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
   destruct (DM.K_eq alpha alpha0).
   inversion H2.
   apply IHWFDGder with (tau:= tau) in H2.
   assumption.
Qed.  

Lemma A_4_Useless_Substitutions_3:
  forall (d : Delta) (alpha : TVar),
    DM.map d alpha = None ->
    forall (u: Upsilon) (x : EVar) (p : Path) (tau': Tau),
        WFU u ->
        UM.map u (x,p) = Some tau' ->
        forall (tau : Tau),
          subst_Tau tau' tau alpha = tau'.
Proof.
  intros d alpha mapder u x p tau' WFUder.
  WFU_ind_cases (induction WFUder) Case.
  Case "WFU []".
   intros.
   inversion H0.
  Case "WFU ([(x, p, tau)] ++ u)".
   intros.
   unfold uctxt in H2.
   unfold UM.map in H2.
   fold UM.map in H2.
   case_eq(UM.K_eq (x,p) (x0,p0)); intros; rewrite H3 in *.
   inversion H2.
   subst.
   apply A_4_Useless_Substitutions_1 with (alpha:= alpha) (tau:= tau0) in H1;
      try assumption.
    reflexivity.
    crush.
Qed.

Lemma NotFreeIn_Tau_subst_useless:
  forall (beta : TVar) (tau : Tau),
    NotFreeInTau beta tau ->
     forall (tau' : Tau),
       subst_Tau tau tau' beta = tau.
Proof.
  intros.
  Tau_ind_cases(induction tau) Case.
  Case "(tv_t t)".
   case_eq (DM.K_eq beta v).
   SCase "beta = v".
    intros.
    unfold NotFreeInTau in H0.
    unfold DM.K_eq in H1.
    unfold TVarModuleDef.TVarModule.beq_t in H1.
    unfold beq_tvar in H0.
    unfold TVarModule.beq_t in H0.
    rewrite H1 in H0.
    inversion H.
   SCase "beta <> t".
    intros.
    unfold subst_Tau.
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
   case_eq (DM.K_eq beta t).
   SCase "beta = t".
    intros.
    unfold subst_Tau.
    fold subst_Tau.
    rewrite H0.
    reflexivity.
   SCase "beta <> t".
    intros.
    unfold subst_Tau.
    fold subst_Tau.
    rewrite H0.
    unfold NotFreeInTau in H.
    fold NotFreeInTau in H.
    rewrite H0 in H.
    apply IHtau in H.
    rewrite H.
    reflexivity.
  Case "(etype p t k t0)".
   case_eq (DM.K_eq beta t).
   SCase "beta = t".
    intros.
    unfold subst_Tau.
    fold subst_Tau.
    rewrite H0.
    reflexivity.
   SCase "beta <> t".
    intros.
    unfold subst_Tau.
    fold subst_Tau.
    rewrite H0.
    unfold NotFreeInTau in H.
    fold NotFreeInTau in H.
    rewrite H0 in H.
    apply IHtau in H.
    rewrite H.
    reflexivity.
Qed.    

Lemma A_5_Commuting_Substitutions:
  forall (beta : TVar) (t2 : Tau),
    NotFreeInTau beta t2 ->
    forall (alpha : TVar) (t0 t1 : Tau),
      (subst_Tau (subst_Tau t0 t1 beta) t2 alpha) =
      (subst_Tau (subst_Tau t0 t2 alpha)
                 (subst_Tau t1 t2 alpha)
                 beta).
Proof.
  intros beta t2 notfreeder alpha t0.
  (Tau_ind_cases (induction t0) Case).
  (* crush leaves 3/7. *)
  Case "(tv_t t)".
    intros.
    case_eq (DM.K_eq alpha beta); case_eq (DM.K_eq alpha t); case_eq (DM.K_eq beta t); crush.
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
Qed.

(* Then try with extends1 step. *)
(* This is going to work but it requires new lemmas, can I use
  the more general extends more simply? *)

Inductive Extends1D : TVar -> Kappa -> Delta -> Delta -> Prop := 
  | Extends1D_alpha_kappa : 
      forall (alpha : TVar) (k : Kappa) (d : Delta) (d' : Delta), 
      d' = ([(alpha,k)] ++ d) ->
      WFD d' ->
      Extends1D alpha k d d'.
        
Lemma A_6_Substitution_1_1:
  forall (d : Delta) (tau : Tau) (k : Kappa),
      AK d tau k -> 
      forall (d' : Delta) (alpha : TVar) (k' : Kappa) (tau' : Tau), 
        K ([(alpha,k)] ++ d) tau' k' ->
        K d (subst_Tau tau' tau alpha) k'.
Proof.
  intros d tau k AKder d' alpha k' tau' Kder.
  K_ind_cases(induction Kder) Case.
 Case "K d cint B".
  admit.
 Case "K d (tv_t alpha) B".
  admit.
 Case "K d (ptype (tv_t alpha)) B".
  admit.
 Case "K d tau A".
  admit.
 Case "K d (cross t0 t1) A".
  admit.
 Case "K d (arrow t0 t1) A".
  admit.
 Case "K d (ptype tau) B".
  admit.
 Case "K d (utype alpha k tau) A".
  admit.
 Case "K d (etype p alpha k tau) A)".
  admit.
Qed.


(*
Lemma A_6_Substitution_1_extends1D:
  forall (d : Delta) (tau : Tau) (k : Kappa),
      WFD d ->
      AK d tau k -> 
      forall (d' : Delta) (alpha : TVar) (k' : Kappa) (tau' : Tau), 
        K d' tau' k' ->
        WFD d' ->
        Extends1D alpha k d d' ->
        K d (subst_Tau tau' tau alpha) k'.
Proof.
  intros d tau k WFDder AKder d' alpha k' tau' Kder.
  K_ind_cases(induction Kder) Case.
  Case "K d cint B".
   intros.
   simpl.
   constructor.
  Case "K d (tv_t alpha) B".
   intros.
   simpl.
   case_eq (DM.K_eq alpha alpha0).
   SCase "(DM.K_eq alpha alpha0) = true".
    admit.
   SCase "(DM.K_eq alpha alpha0) = false".
    intros.
    apply K_B.
    (* This is DM.map some weakening but a new form for Extends1D. *)
    admit.  
  Case "K d (ptype (tv_t alpha)) B".
   intros.
   simpl.
   case_eq (DM.K_eq alpha alpha0).
   SCase "(DM.K_eq alpha alpha0) = true".
    intros.
    apply DM.K_eq_eq in H2.
    rewrite <- H2 in H.
    apply K_ptype.
    inversion H1.
    admit.
   SCase "(DM.K_eq alpha alpha0) = false".
    intros.
    apply K_ptype.
    (* This is DM.map some weakening but a new form for Extends1D. *)
    admit.  
  Case "K d tau A".
   intros.
   apply IHKder in H.
   constructor.
   assumption.
   admit.
  Case "K d (cross t0 t1) A".
   intros.
   pose proof H as H'.
   apply IHKder1 in H.
   apply IHKder2 in H'.
   simpl.
   apply K_cross; try assumption.
   admit.
  Case "K d (arrow t0 t1) A".
   intros.
   pose proof H as H'.
   apply IHKder1 in H.
   apply IHKder2 in H'.
   simpl.
   apply K_arrow; try assumption.
  Case "K d (ptype tau) B".
   intros.
   apply IHKder in H.
   simpl.
   apply K_ptype; try assumption.
  Case "K d (utype alpha k tau) A".
    intros.
    simpl.
    case_eq (DM.K_eq alpha alpha0).
    (* Fixing Extends1D makes this wrong, I'll need to use a full extends. *)
    SCase "(DM.K_eq alpha alpha0) = true".
     intros.
     unfold subst_Tau in IHKder.
     fold subst_Tau in IHKder.
     (* This is the alpha conversion path. *)
     admit.
    SCase "(DM.K_eq alpha alpha0) = false".
     intros.
     assert (Z : Extends1D alpha k d ([(alpha0, k0)] ++ d0)).
     (* Extends1D alpha k d d0 -> 
        DM.K_eq alpha alpha0 = false
        Extends1D alpha k d ([(alpha0, k0)] ++ d0) *)
     admit.
     apply K_utype; try assumption.
     (* WFD ([(alpha0, k0)] ++ d0) ->
        DM.map d0 alpha0 = None
        WFD ([(alpha0, k0)] ++ d) *)
      admit.
      (* DM.map d0 alpha0 = None ->
        Extends1D alpha k d d0 ->
        DM.K_eq alpha alpha0 = false
        DM.map d alpha0 = None *)
     admit.
     (* This is K_weakening. *)
     admit.
  Case "K d (etype p alpha k tau) A)".
   admit.
Qed.
*)


Lemma A_6_Substitution_2:
  forall (d : Delta) (tau : Tau) (k : Kappa),
       AK d tau k -> 
       forall  (alpha : TVar)  (tau' : Tau)  (k' : Kappa) (d' : Delta),
         AK ([(alpha,k)] ++ d) tau' k' ->
        d = ([(alpha,k)] ++ d') ->

         AK d (subst_Tau tau' tau alpha) k'.
Proof.
  intros d tau k AKder.
  apply (AK_ind 
           (fun (d : Delta) (tau : Tau) (k : Kappa) =>
              forall  (alpha : TVar)  (tau' : Tau)  (k' : Kappa),
                AK ([(alpha,k)] ++ d) tau' k' ->
                AK d (subst_Tau tau' tau alpha) k')).

  Case "AK d (tv_t alpha) A".
   intros.
   constructor.
   apply A_6_Substitution_1 with (k:=k); try assumption.
   admit.
   admit.

  Case "AK d (subst_Tau (tv_t alpha0) alpha k) A".
   intros.
   constructor.
   admit.

  Case "base".
   assumption.
Qed.

Lemma A_6_Substitution_3:
  forall (d : Delta) (tau : Tau) (k : Kappa),
    AK d tau k -> 
    forall (alpha : TVar) (tau' : Tau),
      ASGN ([(alpha, k)] ++ d) tau' ->
      ASGN d (subst_Tau tau' tau alpha).
Proof.
  intros d tau k AKder.
  AK_ind_cases (induction AKder) Case.
  Case "AK d (tv_t alpha) A".
   intros.
   inversion H0.
   SCase "cint".
    simpl.
    constructor.
   SCase "(tv_t t)".
    admit.
   SCase "(ptype t)".
    simpl.
    constructor.
   SCase "(cross t t0)".
    admit.
   SCase "(arrow t t0)".
    admit.
   SCase "(utype t k t0)".
    admit.
   SCase "(etype p t k t0)".
    admit.
  Case "AK d (subst_Tau (tv_t alpha0) alpha k) A"  .
   admit.
Qed.

(* unbound d0 down there so is the induction right*) 
(*  intros d tau k AKder alpha tau' ASGNder.
  ASGN_ind_cases (induction ASGNder) Case.
  Case "ASGN d cint".
   simpl.
   constructor.
  Case "ASGN d (tv_t alpha)".
   admit.
  Case "ASGN d (ptype tau)".
   simpl.  
   constructor.
  Case "ASGN d (cross t0 t1)".
   simpl.
   constructor; try assumption.
  Case "ASGN d (arrow t0 t1)".
   simpl.
   constructor; try assumption.
  Case "ASGN d (utype alpha k tau)".
   simpl. (* What the heck is d0? *)
   constructor; try assumption.

  Case "ASGN d (etype witnesschanges alpha k tau))".
   admit.
*)

(* Do I have to move the inductive definition to the top? *)
Lemma A_6_Substitution_4:
  forall (alpha : TVar) (k : Kappa) (d : Delta) (g : Gamma),
    WFDG ([(alpha,k)] ++ d) g ->
      forall (tau : Tau), 
        AK d tau k -> 
        WFDG d (subst_Gamma g tau alpha).
Proof.
  intros alpha k d g WFDGder.
  WFDG_ind_cases (induction WFDGder) Case.
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
  Case "WFDG ([(alpha, k)] ++ d) g".
   intros.
   admit.
Qed.

Lemma A_6_Substitution_5:
  forall (alpha : TVar) (k : Kappa) (d : Delta) (u : Upsilon)  (g : Gamma),
    WFC ( [(alpha,k)] ++ d) u g ->
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
Qed.

(* Thesis Bug, no AK is required. *)
Lemma A_6_Substitution_6: 
  forall (s : St),
      ret s ->
      forall (alpha : TVar) (tau : Tau),
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
  forall (u : Upsilon) (x : EVar) (p p': Path) (t1 t2: Tau),
    gettype u x p t1 p' t2 ->
    forall (d: Delta) (tau : Tau) (k : Kappa) (beta : TVar),
      AK d tau k -> 
      WFU u ->
        gettype u x p (subst_Tau t1 tau beta) p' (subst_Tau t2 tau beta).
Proof.
  intros u x p p' t1 t2 gettypder.
  apply (gettype_ind 
           (fun (u : Upsilon) (x : EVar) (p : Path) (t1 : Tau) (p' : Path) (t2 : Tau) =>
              forall (d: Delta) (tau : Tau) (k : Kappa) (beta : TVar),
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
   destruct (DM.K_eq beta alpha).
   
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

(* Dan, is that last ltyp supposed to be an styp? *)

(* Need three of these. *)
Lemma A_6_Substitution_8_1_2_3:
  forall (d : Delta) (tau : Tau) (k : Kappa),
    AK d tau k ->
    forall (alpha : TVar) (u : Upsilon) (g : Gamma) (e : E) (tau' : Tau) 
            (d' : Delta),
      ltyp d u g e tau' ->
      d = ([(alpha,k)] ++ d') ->
      ltyp d u (subst_Gamma g tau alpha)
           (subst_E e tau alpha)
           (subst_Tau tau' tau alpha).
Proof.
  intros d tau k AKder.
  intros alpha u g e tau' d' ltypder.
  ltyp_ind_mutual_cases 
    (apply (ltyp_ind_mutual
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (t : Tau) (s : St)
                (st : styp d u g t s) => 
              d = ([(alpha,k)] ++ d') ->
              styp d u (subst_Gamma g tau alpha)
                   (subst_Tau tau' tau alpha)
                   (subst_St s tau alpha))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau' : Tau) 
                (lt : ltyp d u g  e tau') =>
              d = ([(alpha,k)] ++ d') ->
              ltyp d u (subst_Gamma g tau alpha)
                   (subst_E e tau alpha)
                   (subst_Tau tau' tau alpha))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (rt : rtyp d u g e t) =>
              d = ([(alpha,k)] ++ d') ->
              rtyp d u (subst_Gamma g tau alpha)
                   (subst_E e tau alpha)
                   (subst_Tau tau' tau alpha)))) Case; crush.
  (* crush gets one. *)
Admitted.    
