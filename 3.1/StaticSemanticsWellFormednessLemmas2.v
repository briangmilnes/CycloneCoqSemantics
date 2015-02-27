(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

   Lemmas about static semantics context well formedness.
*)
Set Implicit Arguments.
Require Export LanguageModuleDef.
Require Export CpdtTactics.
Require Export TacticNotations.
Require Export Tacticals.
Require Export AlphaConversion.
Require Export StaticSemanticsKindingAndContextWellFormednessLemmas.
Require Export StaticSemanticsKindingLemmas.

Lemma WFU_t_implies_K_nil_A:
  forall (t : Tau) (e : EVP.E.Var) (p : Path)  (u' : Upsilon),
    WFU (U.ctxt (e, p) t u') -> 
    K ddot t A.
Proof.
  destruct t; intros; try solve[inversion H; try assumption].
Qed.

Lemma WFU_strengthening:
 forall (u u' : Upsilon),
   U.extends u u' = true ->
   WFU u' ->
   WFU u.
Proof.
(*
  intros u u' ext WFUu'.
  induction WFUu'; intros; try solve[crush].
  apply U.empty_extends_only_empty in ext; subst.
  constructor.

  apply U.extends_r_weak in ext; try assumption.
  pose proof ext as ext'.
  apply IHWFUu' in ext; try assumption.
  assert (Z: WFU (U.ctxt (x, p) tau u0)).
  constructor; try assumption.
  apply WFU_implies_nodup in Z; try assumption.
  (* almost but no cigar I'd say. *)
  case_eq(U.map u (x, p)); intros.
  admit.
  reflexivity.
*)
  intros u.
  induction u; intros; try solve[crush].
Admitted.

Lemma WFD_WFDG_implies_K_d_t_A:
  forall d g x tau,
    WFD d ->
    WFDG d g ->
    G.map g x = Some tau ->
    K d tau A.
Proof.
 intros d g x tau WFDder WFDGder.
 induction WFDGder; intros; try solve[crush].
 unfold G.map in H1.
 fold G.map in H1.
 case_eq(G.K_eq x x0); intros; rewrite H2 in H1.
 inversion H1; subst; try assumption.
 apply IHWFDGder in WFDder; try assumption.
 inversion WFDder; subst. 
 apply IHWFDGder in H0; try assumption.
 apply K_weakening with (d:= d); try assumption.
 pose proof H5 as H5'.
 apply WFD_implies_nodup in H5'.
 apply D.extends_r_str; try assumption.
 apply D.extends_refl; try assumption.
 unfold D.nodup.
 fold D.nodup.
 rewrite H3.
 assumption.
Qed.

Lemma WFDG_g_strengthening:
  forall (g g' : Gamma),
    G.extends g g' = true ->
    forall (d : Delta), 
      WFD d ->
      WFDG d g' ->
      WFDG d g.
Proof.
  (* closer no cigar. *)
  intros g.
  induction g; intros; try solve[crush].

  pose proof H as H'.
  apply G.extends_l_str in H.
  apply IHg with (d:= d) in H; try assumption.
  constructor; try assumption.
  admit. (* H' WFDG g' should imply k is not in there. *)
  apply WFD_WFDG_implies_K_d_t_A with (g:= (G.ctxt k t g)) (x:= k); try assumption.
  constructor; try assumption.
  admit.
  admit.
  unfold G.map.
  fold G.map.
  rewrite G.K.beq_t_refl.
  reflexivity.
Admitted.

(* by extends induction
  intros g g'.
  functional induction (G.extends g g'); intros; try solve[crush].
  apply IHb with (d:= d) in H; try assumption.
  constructor; try assumption.
  admit. (* Stuck dang it. *)
  apply WFD_WFDG_implies_K_d_t_A with (g:= c') (x:= k); try assumption.
  apply G.T.beq_t_eq in e1; subst; try assumption.
*)

(* By  WFDG induction

  intros d g' WFDGder g ext.
  induction WFDGder; try solve[crush]; intros.

  apply G.empty_extends_only_empty in ext.
  subst.
  constructor; try assumption.

  apply G.extends_r_weak in ext; try assumption.
  apply IHwfdgdg' in ext; try assumption.
  apply WFDG_implies_nodup in wfdgdg'.
  unfold G.nodup.
  fold G.nodup.
  rewrite H; try assumption.
  admit. (* perhaps stuck. *)
  apply IHwfdgdg' in ext.
  constructor; try assumption.
Qed.

*)



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

