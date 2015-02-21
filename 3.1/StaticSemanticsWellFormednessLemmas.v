(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

   Lemmas about static semantics context well formedness.

*)

Require Export LanguageModuleDef.
Require Export DynamicSemanticsTypeSubstitution.
Require Export DynamicSemanticsHeapObjects.
Require Export DynamicSemantics.
Require Export DynamicSemanticsTypeSubstitution.
Require Export StaticSemanticsKindingAndContextWellFormedness.
Require Export StaticSemantics.
Require Export TypeSafety.
Require Export CpdtTactics.
Require Export TacticNotations.
Require Export AlphaConversion.

Lemma WFD_weakening:
  forall (d : Delta) (alpha : TV.T) (k : Kappa),
     WFD d ->
      D.map d alpha = None ->
      WFD (D.ctxt alpha k d).
Proof.
  intros d.
  induction d; intros.
  constructor; try reflexivity.
  constructor.
  inversion H; subst.
  apply IHd  with (alpha:= alpha) (k:= k0) in H5; try assumption.
  inversion H5; subst; try assumption.
  constructor; try assumption.
  inversion H0.
  case_eq(D.K_eq alpha k); intros; rewrite H1 in H2; try solve[inversion H2].
  reflexivity.
Qed.

(* TODO 

Lemma NotInDomU_strengthening':
  forall (u u' : Upsilon) (x : EVar) (p : P),
    WFU (u ++ u') ->
    NotInDomU (u ++ u') x p ->
    NotInDomU u x p.
Proof.
  intros u u' x p.
  induction u.
  Case "u = []".
   rewrite app_nil_l.
   intros.
   constructor.
  Case "(x,p,t) :: u".
   intros.
   destruct a as [ yp t].
   destruct yp as [ y p' ].
   inversion H.
   unfold NotInDomU in H0.
   fold NotInDomU in H0.
   apply IHu in H6.
Admitted.

Lemma NotInDomU_strengthening:
  forall (u u' : Upsilon) (x : EVar) (p : P),
    WFU (u ++ u') ->
    NotInDomU (u ++ u') x p ->
    NotInDomU u x p.
Proof.
  intros u u' x p.
  induction u.
  Case "u = []".
   rewrite app_nil_l.
   intros.
   constructor.
  Case "a::u".
   intros.
   destruct a.
   destruct p0.
   case_eq (beq_evar x e); case_eq (beq_path p p0).
   intros.
   inversion H.
   apply IHu in H8.
   unfold NotInDomU.
   fold NotInDomU.
   rewrite H1.
   rewrite H2.
   simpl.
   tauto.
   apply beq_evar_eq in H2.
   admit.
   intros.
   admit.
   intros.
   admit.
   admit.
Admitted.  

(* Dan, This should work as it uses K [] tau A and tau should be a ground type
   to be stored in memory but we don't have it here.  *)
Lemma WFU_strengthening:
 forall (u u' : Upsilon),
   WFU (u ++ u') ->
   WFU u.
Proof.
  intros.
  WFU_ind_cases (induction u) Case.
  Case "WFU []".
   constructor.
  Case "WFU ([(x, p, tau)] ++ u)".
   destruct a as [ xp t].
   destruct xp as [x p].
   constructor.
   SCase "NotInDomU u x p".
    AdmitAlphaConversion.
   SCase "WFU u".
    inversion H.
    apply IHu in H5; try assumption.
   SCase "K [] t A".
    admit. (* Thesis bug ? *)
Qed.

Lemma WFDG_g_strengthening:
  forall (d : Delta) (g g' : Gamma),
    WFDG d (g ++ g') ->
    WFDG d g.
Proof.
  intros.
  induction g.
  Case "g = []".
   rewrite app_nil_l in H.
   constructor.
   inversion H.
   crush.
  Case "a :: g'". 
   constructor.
   apply getG_None_Strengthening with (g':=g').
   assumption.
   assumption.
   assumption.
  Case "(alpha,k) :: d0".
   constructor.
   assumption.
   destruct a.
   constructor.
   inversion H1.
   apply getG_None_Strengthening with (g':=g').   
   assumption.
   crush.
   AdmitAlphaConversion.
   admit. (* K? *)
   crush.
   inversion H.
   admit. (* TODO *)
   admit.
Qed.

Lemma WFD_strengthening:
 forall (d d' : Delta),
   WFD (d ++ d') ->
   WFD d.
Proof.
   intros.
   induction d.
  Case "d=[]".
   constructor.
  Case "a :: d'".
   inversion H.
   apply IHd in H3.
   constructor. 
   AdmitAlphaConversion.
   assumption.
Qed.

(* used. *)
Lemma WFDG_d_strengthening:
  forall (d d' : Delta) (g  : Gamma),
    WFDG (d ++ d') g ->
    WFDG d g.
Proof.
  intros d d' g WFDGder.
  induction WFDGder.
  Case "g = []".
   constructor.
  Case "[(x,tau] ++ g".
   constructor.
   AdmitAlphaConversion.
   admit. (* induction wrong, d0 instead of d. *)
   assumption.
   admit.
Qed.

Lemma WFDG_strengthening:
  forall (d d' : Delta) (g g' : Gamma),
    WFDG (d ++ d') (g ++ g') ->
    WFDG d g.
Proof.
  intros.
  apply WFDG_d_strengthening in H.
  apply WFDG_g_strengthening in H.
  assumption.
Qed.

(* Is this really true? No due to delta constraints!*)
Lemma WFC_strengthening:
  forall (d d': Delta) (u u' : Upsilon) (g g': Gamma),
    WFC (d ++ d') (u ++ u') (g ++ g') ->
    WFC d u g.
Proof.
  intros d d' u u' g g' WFCder.
  apply (WFC_ind
           (fun (d : Delta) (u : Upsilon) (g : Gamma) =>
              WFC (d ++ d') (u ++ u') (g ++ g') ->
              WFC d u g)).
  intros.
  Case "WFC d0 u0 g0".
   constructor; try assumption.
  Case "WFC d u g".
   inversion WFCder.
   crush.
   apply WFD_strengthening in H; try assumption.   (* Proven. *)
   apply WFU_strengthening in H1; try assumption.  (* Proven. *)
   apply WFDG_strengthening in H0; try assumption. (* not proven. *)
   constructor; try assumption.
   assumption.
Qed.

(* Too much work to do it this way. *)
Lemma WFC_strengthening_right:
  forall (d d': Delta) (u u' : Upsilon) (g g': Gamma),
    WFC (d ++ d') (u ++ u') (g ++ g') ->
    WFC d' u' g'.
Proof.
Admitted.

(* Weakening *)

Lemma WFU_weakening:
  forall (u : Upsilon),
    WFU u ->
    forall (u' : Upsilon),
      WFU u' ->
      WFU (u ++ u').
Admitted.


(* This one might be true and needed. Might needs extendedbyG. 
  Heck might need both extended bys. *)
Lemma WFDG_g_weakening:
  forall (d : Delta) (g: Gamma),
    WFDG d g -> 
    forall (g' : Gamma),
      WFDG d g' -> 
      WFDG d (g ++ g').
Proof.
  intros d g WFDGder.
  induction g.
  Case "g = []".
   intros.
   rewrite app_nil_l.
   assumption.
  Case "a :: g".
   intros.
   SCase "((x, tau) :: g) ++ g'".
    destruct a.
    rewrite cons_is_append_singleton.
    rewrite <- app_assoc.
    constructor; try assumption.
    AdmitAlphaConversion.
    inversion WFDGder; try assumption.
    crush.
    inversion WFDGder; try assumption.
    inversion WFDGder; try assumption.
    inversion WFDGder; try assumption.
    inversion WFDGder; try assumption.
    crush.
    (* in a loop so good sign I need to strengthen the theorem. *)
 Admitted.

Lemma WFDG_g_weakening_2:
  forall (g : Gamma) (x : EVar) (t : Tau),
    ExtendedByG g ([(x,t)] ++ g) ->
    forall (d : Delta),
      WFDG d g -> 
      WFDG d ([(x,t)] ++ g).
Proof.
  (* Lost on all induction and all cases. *)
Admitted.
*)

