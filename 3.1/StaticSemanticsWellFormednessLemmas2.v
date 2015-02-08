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

Lemma WFU_t_implies_K_nil_A:
  forall t e p u',
    WFU (uctxt (e, p) t u') -> 
    K ddot t A.
Proof.
  destruct t; intros.
  Case "K [] (tv_t t) A".
   inversion H0.
   assumption.
   constructor.
  Case "K [] cint B".
   apply K_int.
  Case "K [] (cross t1 t2) A".
   apply K_cross.
   inversion H0.
   inversion H7.
   inversion H8.
   assumption.
   inversion H0.
   inversion H7.
   inversion H8.
   assumption.
  Case "K [] (arrow t1 t2) A".
   apply K_arrow.
   inversion H0.
   inversion H7.
   inversion H8.
   assumption.
   inversion H0.
   inversion H7.
   inversion H8.
   assumption.
  Case "K [] (ptype t) A".
   constructor.
   apply K_ptype.
   inversion H0.
   inversion H7.
   inversion H8.
   inversion H13.
   assumption.
  Case "K [] (utype t k t0) A".
   apply K_utype.
   constructor; try assumption.
   simpl.
   reflexivity.
   constructor.
   simpl.
   reflexivity.
   inversion H0.
   inversion H7; try assumption.
   inversion H8.
  Case "K [] (etype p0 t k t0) A".
   apply K_etype.
   constructor; try assumption.
   simpl.
   reflexivity.
   constructor.
   simpl.
   reflexivity.
   inversion H0.
   inversion H7; try assumption.
   inversion H8.
Qed.

Lemma WFU_strengthening:
 forall (u u' : Upsilon),
   UM.extends u u' = true ->
   WFU u' ->
   WFU u.
Proof.
(*
  intros u u'.
  functional induction (UM.extends u u'); try solve [crush].
  intros.
  constructor.
  intros.
  apply IHb in H0; try assumption.
  apply UM.T.beq_t_eq in e1.
  subst.
  destruct k.
  constructor; try assumption.
  admit. (* unprovable *)
  (* need to strengthen this to just have t in WFU and i'm good. *)
  apply WFU_t_implies_K_nil_A with (e:= v) (p:= p) (u':= ?); try assumption.
*)


(*
  intros u u' extends WFUder.
  induction WFUder.
  apply UM.empty_extends_only_empty in extends.
  rewrite extends.
  constructor.
  apply UM.extends_r_weaken in extends; try assumption.
  apply IHWFUder in extends; try assumption.
  admit.
  (* Looks doable but somewhat annoying with the map. *)
*)

(* Looks broken. 
  intros u.
  induction u.
  intros.
  constructor.
  intros.
  unfold UM.extends in H0.
  fold UM.extends in H0.
  case_eq(UM.map u' k); intros; rewrite H2 in H0; try solve[inversion H0].
  case_eq(UM.T_eq t t0); intros; rewrite H3 in H0; try solve[inversion H0].
  apply IHu in H0; try assumption.
  destruct k.
  constructor; try assumption.
*)

  intros.
  induction u.
  constructor.
  destruct k.
  apply WFU_A; try assumption.
  inversion H1; try assumption.
  subst.
  inversion H0.
  admit.
  admit.
  admit.
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

(* Is this really true? *)
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
   apply WFD_strengthening in H; try assumption.
   apply WFU_strengthening in H1; try assumption.
   apply WFDG_strengthening in H0; try assumption.
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

Lemma WFU_weakening:
  forall (u : Upsilon),
    WFU u ->
    forall (u' : Upsilon),
      WFU u' ->
      WFU (u ++ u').
Admitted.

