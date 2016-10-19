(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Defining type safety, page 67.

*)

Require Import List.
Require Export LanguageModuleDef.
Require Export TacticNotations.
Require Export StaticSemanticsKindingAndContextWellFormednessLemmas.
Require Export StaticSemanticsHeapObjectsLemmas.
Require Export AlphaConversion.

Lemma A_2_Term_Weakening_1 :
  forall (d: Delta) (u u' : Upsilon) (g g' : Gamma)
         (x : TM.EV.T) (p p' : Path) (tau tau' : Tau),
    U.extends u u' = true ->
    G.extends g g' = true ->
    WFC d u g -> 
    WFC d u' g' ->
    gettype u  x p tau p' tau' ->
    gettype u' x p tau p' tau'.
Proof.
  intros d u u' g g' x p p' tau tau' Uext Gext WFCder WFCder'.
  intros gettypeder.
  gettype_ind_cases (induction gettypeder) Case.
  Case "gettype u x p tau [] tau".
   constructor.
  Case "gettype u x p (cross t0 t1) (i_pe zero_pe :: p') tau".
   constructor.
   apply IHgettypeder in Uext; try assumption.
  Case "gettype u x p (cross t0 t1) (i_pe one_pe :: p') tau".
   constructor.
   apply IHgettypeder in Uext; try assumption.
  Case "gettype u x p (etype aliases alpha k tau') (u_pe :: p') tau)".
   apply gettype_etype with (tau'':= tau''); try assumption.
   apply U.map_extends_some_agreement with (c:= u); try assumption.
   inversion WFCder; subst; try assumption.
   apply WFU_implies_nodup; try assumption.
   apply WFU_implies_nodup; try assumption.
   inversion WFCder'; subst; try assumption.
   apply IHgettypeder in Uext; try assumption.
Qed.

(* Do I really want styp g weakening? Is it true ?*)
(* No way this is true. *)
(* Is it true with 1 step extends in some way ?*)
Lemma styp_g_weak:
  forall (d : Delta) (u : Upsilon) (g' : Gamma) (tau : Tau) (s : St),
    styp d u g' tau s ->
    forall (g : Gamma) (x : G.K),
      G.map g x = None ->
      G.extends g g' = true ->
      styp d u g tau s.
Proof.
Admitted.

(* What is really breaking this is the K [] t A which comes from the
   typing of the term but I need down in the strengthening. *)
(* TODO let, open, openstar and function application. *)
Lemma A_2_Term_Weakening_2:
  forall (d: Delta) (u : Upsilon) (g : Gamma)  (e : E) (tau : Tau),
    ltyp d u g e tau ->
    WFC d u g -> 
      forall (u' : Upsilon) (g' : Gamma),
        WFC d u' g' ->
        U.extends u u' = true ->
        G.extends g g' = true->
        ltyp d u' g' e tau.
Proof.
  intros d u g e tau ltypder.
  ltyp_ind_mutual_cases(
  apply (ltyp_ind_mutual
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (t : Tau) (s : St)
                (st : styp d u g t s) => 
              WFC d u g -> 
              forall (u' : Upsilon) (g' : Gamma),
                WFC d u' g' ->
                U.extends u u' = true ->
                G.extends g g' = true->
                styp d u' g' t s)
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (lt : ltyp d u g  e t) =>
              WFC d u g -> 
              forall (u' : Upsilon) (g' : Gamma),
                WFC d u' g' ->
                U.extends u u' = true ->
                G.extends g g' = true->
                ltyp d u' g' e t)
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (rt : rtyp d u g e t) =>
              WFC d u g -> 
              forall (u' : Upsilon) (g' : Gamma),
                WFC d u' g' ->
                U.extends u u' = true ->
                G.extends g g' = true->
                rtyp d u' g' e t))) Case; intros; try solve[crush].
  (* Basically new proof as crush gets 13 now. *)
  Case "styp_e_3_1".
   apply styp_e_3_1 with (tau':= tau').
   apply H with (u':= u') (g':= g') in H1; try assumption.
  Case "styp_let_3_6".
   apply styp_let_3_6 with (tau':=tau'); try assumption.
   apply G.admit_alpha_conversion_context.
   apply H in H1; try assumption.
   admit. (* styp u and g str *)
   admit. (* apply WFC_g_weakening. ? *)
   apply U.extends_refl.
   inversion H1; subst.
   apply WFU_implies_nodup in H7; try assumption.
   admit. (* Is this even true? *)
   admit.
  Case "styp_open_3_7".
   admit.
  Case "styp_openstar_3_8".
   admit.
  Case "SL_3_1".
   admit.
  Case "SL_3_3".
   apply SL_3_3 with (t1:= t1); try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SL_3_4".
   apply SL_3_4 with (t0:= t0); try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SR_3_1".
   apply SR_3_1 with (tau':= tau'); try assumption.
   apply G.map_extends_some_agreement with (c:= g0); try assumption.
   admit.
   admit.
   apply gettype_weakening with (u:= u0); try assumption.
   inversion H; try assumption.
   inversion H0; try assumption.
  Case "SR_3_3".
   apply SR_3_3 with (t1:= t1); try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SR_3_4".
   apply SR_3_4 with (t0:= t0); try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SR_3_9".
   apply SR_3_9 with (tau':= tau'); try assumption.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   apply H0 with (u':= u') (g':= g') in H1; try assumption.
  Case "SR_3_11".
   apply SR_3_11 with (k:=k); try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SR_3_13".
   constructor; try assumption.
   AdmitAlphaConversion.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   (* apply styp_g_weak. *)
   (* styp g weakening. *)
   admit.
   admit.
   admit.
  Case "SR_3_14".
   admit.

(*   
  Case "styp_return_3_2".
   constructor.
   apply H with (u':= u') (g':= g') in H1; try assumption.
  Case "styp_seq_3_3".
   constructor.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   apply H0 with (u':= u') (g':= g') in H1; try assumption.
  Case "styp_while_3_4".
   constructor.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   apply H0 with (u':= u') (g':= g') in H1; try assumption.
  Case "styp_if_3_5".
   constructor.
   apply H with (u':= u') (g':= g') in H2; try assumption.
   apply H0 with (u':= u') (g':= g') in H2; try assumption.
   apply H1 with (u':= u') (g':= g') in H2; try assumption.
  Case "styp_let_3_6".
*)  
(*
  (* OKay this works, modulo alpha conversion but the case is a 
      repetitive mess. *)
   intros.
   apply styp_let_3_6 with (tau':=tau'); try assumption.
   AdmitAlphaConversion.
   inversion H2; try assumption.
   assert (Z: WFC d0 u0 ([(x, tau')] ++ g0)).
   constructor; try assumption.
   constructor; try assumption.
   inversion H1; try assumption.
   inversion H3; try assumption.
   apply WFU_strengthening in H12; try assumption.
   apply H with (u':= u') (g':= g') in Z; try assumption.
   constructor; try assumption.
   apply WFDG_xt.
   AdmitAlphaConversion.
   assumption.
   apply H0 with (u':= u') (g':= g') in H1; try assumption.
   inversion H3.
   assumption.
   inversion H3; try assumption.
   apply H0 with (u':= u') (g':= g') in H1; try assumption.
*)
(*
  Case "styp_open_3_7".
   intros.
   inversion H1.
   inversion H2.
   crush.
   apply styp_open_3_7 with (p:= p) (k:= k) (tau':= tau'); try assumption.
   AdmitAlphaConversion.
   apply H16 in H2; try assumption.
   apply H0; try assumption.
   constructor; try assumption.
   constructor; try assumption.
   constructor; try assumption.
   (*  K ((alpha, k) :: d0) tau' A *)
   admit. (* Don't know where to get this K, it's coming from the pack that is e0. *)
   constructor; try assumption.
   constructor; try assumption.
   constructor; try assumption.   
   constructor; try assumption.   
   constructor; try assumption.   
   constructor; try assumption.      
   constructor; try assumption.   
   AdmitAlphaConversion.
   (*  K ((alpha, k) :: d0) tau' A *) 
   admit. (* Don't know where to get this K. *)
   constructor; try assumption.
   (* WFDG d0 (g0 ++ g') given WFDG d0 g0 *)
   admit. (* WFDG strengthening. *)
   (* What do I have here to make a WFDG true ? *)
   inversion H3; try assumption.
  admit.
  Case "styp_openstar_3_8".
   admit. (* Will have the similar problems with let. *)
  Case "SL_3_1".
   intros.
   apply SL_3_1 with (tau':=tau'); try assumption.
   apply G.map_extends_some_agreement with (c:= g0); try assumption.
   inversion H0; subst.
   apply WFDG_implies_nodup with (d:= d0); try assumption.
   inversion H4; subst.
   admit. (* is this even true? *)
   admit.
   apply gettype_weakening; try assumption.
   inversion H; try assumption.
   inversion H1; try assumption.
  Case "SL_3_2".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SL_3_3".
   intros.
   apply SL_3_3 with (t1:= t1); try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SL_3_4".
   intros.
   apply SL_3_4 with (t0:= t0); try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SR_3_1".
   intros.
   apply SR_3_1 with (tau':= tau'); try assumption.
   apply getG_Some_Weakening; try assumption.
   apply gettype_weakening; try assumption.
   inversion H; try assumption.
   inversion H1; try assumption.
  Case "SR_3_2".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SR_3_3".
   intros.
   apply SR_3_3 with (t1:= t1); try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SR_3_4".
   intros.
   apply SR_3_4 with (t0:= t0); try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SR_3_5".
   intros.
   constructor; try assumption.
  Case "SR_3_6".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SR_3_7".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   apply H0 with (u':= u') (g':= g') in H1; try assumption.
  Case "SR_3_8".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   apply H0 with (u':= u') (g':= g') in H1; try assumption.
  Case "SR_3_9".
   intros.
   apply SR_3_9 with (tau':= tau'); try assumption.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   apply H0 with (u':= u') (g':= g') in H1; try assumption.
  Case "SR_3_10".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H1; try assumption.
  Case "SR_3_11".
   intros.
   apply SR_3_11 with (k:=k); try assumption.
   apply H with (u':= u') (g':= g') in H1; try assumption.
  Case "SR_3_12".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H1; try assumption.
  (* TODO two cases and then I'm done without rtype weakening. *)
  Case "SR_3_13".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   AdmitAlphaConversion.
   admit.
   admit.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   admit.
   admit.
  Case "SR_3_14".
   intros.
   admit.
  Case "base".
   assumption.
Qed.
*)
Admitted.


Lemma A_2_Term_Weakening_3:
  forall (d: Delta) (u : Upsilon) (g : Gamma)  (e : E) (tau : Tau),
    rtyp d u g e tau ->
    WFC d u g -> 
      forall (u' : Upsilon) (g' : Gamma),
        WFC d u' g' ->
        U.extends u u' = true ->
        G.extends g g' = true ->
        WFC d u g' ->
        rtyp d u' g' e tau.
Proof.
(*
  intros d u g e tau ltypder.
  apply (rtyp_ind_mutual
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (t : Tau) (s : St)
                (st : styp d u g t s) => 
              WFC d u g -> 
              forall (u' : Upsilon) (g' : Gamma),
                WFC d u' g' ->
                WFC d (u ++ u') (g ++ g') ->
                styp d (u ++ u') (g ++ g') t s)
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (lt : ltyp d u g  e t) =>
              WFC d u g -> 
              forall (u' : Upsilon) (g' : Gamma),
                WFC d u' g' ->
                WFC d (u ++ u') (g ++ g') ->
                ltyp d (u ++ u') (g ++ g') e t)
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (rt : rtyp d u g e t) =>
              WFC d u g -> 
              forall (u' : Upsilon) (g' : Gamma),
                WFC d u' g' ->
                WFC d (u ++ u') (g ++ g') ->
                rtyp d (u ++ u') (g ++ g') e t)).
(*
  Case "styp_e_3_1".
   intros.
   constructor.
   apply H with (u':= u') (g':= g') in H1; try assumption.
  Case "styp_return_3_2".
   intros.
   constructor.
   apply H with (u':= u') (g':= g') in H1; try assumption.
  Case "styp_seq_3_3".
   intros.
   constructor.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   apply H0 with (u':= u') (g':= g') in H1; try assumption.
  Case "styp_while_3_4".
   intros.
   constructor.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   apply H0 with (u':= u') (g':= g') in H1; try assumption.
  Case "styp_if_3_5".
   intros.
   constructor.
   apply H with (u':= u') (g':= g') in H2; try assumption.
   apply H0 with (u':= u') (g':= g') in H2; try assumption.
   apply H1 with (u':= u') (g':= g') in H2; try assumption.
  Case "styp_let_3_6".
   intros.
   apply styp_let_3_6 with (tau':=tau'); try assumption.
   AdmitAlphaConversion.
   inversion H2; try assumption.
   assert (Z: WFC d0 u0 ([(x, tau')] ++ g0)). (* How do I get this ? *)
   constructor; try assumption.
   constructor; try assumption.
   admit.
   admit.
   admit.
   admit.
   admit.
   (* 
   apply H with (u':= u') (g':= g') in Z; try assumption.
   admit.
   apply H0 with (u':= u') (g':= g') in H1; try assumption.
   *)
  Case "styp_open_3_7".
   admit. (* Will have the similar problems with let. *)
  Case "styp_openstar_3_8".
   admit. (* Will have the similar problems with let. *)
  Case "SL_3_1".
  (* Should use the previous theorem.
   intros.
   apply SL_3_1 with (tau':= tau0); try assumption.
   apply getG_Some_Weakening; try assumption.
   apply gettype_weakening; try assumption.
   inversion H; try assumption.
   inversion H1; try assumption.
   *)
  admit.
  Case "SL_3_2".
   intros.
   admit. (* constructor; try assumption. *)
   (* apply H with (u':= u') (g':= g') in H0; try assumption. *)
  Case "SL_3_3".
   intros.
   apply SL_3_3 with (t1:= t1); try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SL_3_4".
   intros.
   apply SL_3_4 with (t0:= t0); try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SR_3_1".
   intros.
   apply SR_3_1 with (tau':= tau'); try assumption.
   apply getG_Some_Weakening; try assumption.
   apply gettype_weakening; try assumption.
   inversion H; try assumption.
   inversion H1; try assumption.
  Case "SR_3_2".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SR_3_3".
   intros.
   apply SR_3_3 with (t1:= t1); try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SR_3_4".
   intros.
   apply SR_3_4 with (t0:= t0); try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SR_3_5".
   intros.
   constructor; try assumption.
  Case "SR_3_6".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SR_3_7".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   apply H0 with (u':= u') (g':= g') in H1; try assumption.
  Case "SR_3_8".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   apply H0 with (u':= u') (g':= g') in H1; try assumption.
  Case "SR_3_9".
   intros.
   apply SR_3_9 with (tau':= tau'); try assumption.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   apply H0 with (u':= u') (g':= g') in H1; try assumption.
  Case "SR_3_10".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H1; try assumption.
  Case "SR_3_11".
   intros.
   apply SR_3_11 with (k:=k); try assumption.
   apply H with (u':= u') (g':= g') in H1; try assumption.
  Case "SR_3_12".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H1; try assumption.
  Case "SR_3_13".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   AdmitAlphaConversion.
   admit.
   admit.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   admit.
   admit.
  Case "SR_3_14".
   admit.
  Case "base".
   assumption.
Qed.
*)
*)
Admitted.

Lemma A_2_Term_Weakening_4:
  forall (d: Delta) (u : Upsilon) (g : Gamma)  (s : St) (tau : Tau),
    styp d u g tau s ->
    WFC d u g -> 
      forall (u' : Upsilon) (g' : Gamma),
        WFC d u' g' ->
        U.extends u u' = true ->
        G.extends g g' = true ->
        WFC d u' g' ->
        styp d u' g' tau s.
Proof.
(*
  intros d u g e tau ltypder.
  apply (styp_ind_mutual
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (t : Tau) (s : St)
                (st : styp d u g t s) => 
              WFC d u g -> 
              forall (u' : Upsilon) (g' : Gamma),
                WFC d u' g' ->
                WFC d (u ++ u') (g ++ g') ->
                styp d (u ++ u') (g ++ g') t s)
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (lt : ltyp d u g  e t) =>
              WFC d u g -> 
              forall (u' : Upsilon) (g' : Gamma),
                WFC d u' g' ->
                WFC d (u ++ u') (g ++ g') ->
                ltyp d (u ++ u') (g ++ g') e t)
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (rt : rtyp d u g e t) =>
              WFC d u g -> 
              forall (u' : Upsilon) (g' : Gamma),
                WFC d u' g' ->
                WFC d (u ++ u') (g ++ g') ->
                rtyp d (u ++ u') (g ++ g') e t)).
  Case "styp_e_3_1".
   intros.
   apply styp_e_3_1 with (tau':= tau').
   apply H with (u':= u') (g':= g') in H1; try assumption.
  Case "styp_return_3_2".
   intros.
   constructor.
   apply H with (u':= u') (g':= g') in H1; try assumption.
  Case "styp_seq_3_3".
   intros.
   constructor.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   apply H0 with (u':= u') (g':= g') in H1; try assumption.
  Case "styp_while_3_4".
   intros.
   constructor.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   apply H0 with (u':= u') (g':= g') in H1; try assumption.
  Case "styp_if_3_5".
   intros.
   constructor.
   apply H with (u':= u') (g':= g') in H2; try assumption.
   apply H0 with (u':= u') (g':= g') in H2; try assumption.
   apply H1 with (u':= u') (g':= g') in H2; try assumption.
  Case "styp_let_3_6".
   admit.
   (* 
   intros.
   apply styp_let_3_6 with (tau':=tau'); try assumption.
   AdmitAlphaConversion.
   inversion H2; try assumption.
   assert (Z: WFC d0 u0 ([(x, tau')] ++ g0)). (* How do I get this ? *)
   constructor; try assumption.
   constructor; try assumption.

   apply H with (u':= u') (g':= g') in Z; try assumption.
   admit.
   apply H0 with (u':= u') (g':= g') in H1; try assumption.
    *)
  Case "styp_open_3_7".
   admit. (* Will have the similar problems with let. *)
  Case "styp_openstar_3_8".
   admit. (* Will have the similar problems with let. *)
  Case "SL_3_1".
   intros.
   apply SL_3_1 with (tau':=tau'); try assumption.
   apply getG_Some_Weakening; try assumption.
   apply gettype_weakening; try assumption.
   inversion H; try assumption.
   inversion H1; try assumption.
  Case "SL_3_2".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SL_3_3".
   intros.
   apply SL_3_3 with (t1:= t1); try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SL_3_4".
   intros.
   apply SL_3_4 with (t0:= t0); try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SR_3_1".
   intros.
   apply SR_3_1 with (tau':= tau'); try assumption.
   apply getG_Some_Weakening; try assumption.
   apply gettype_weakening; try assumption.
   inversion H; try assumption.
   inversion H1; try assumption.
  Case "SR_3_2".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SR_3_3".
   intros.
   apply SR_3_3 with (t1:= t1); try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SR_3_4".
   intros.
   apply SR_3_4 with (t0:= t0); try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SR_3_5".
   intros.
   constructor; try assumption.
  Case "SR_3_6".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SR_3_7".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   apply H0 with (u':= u') (g':= g') in H1; try assumption.
  Case "SR_3_8".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   apply H0 with (u':= u') (g':= g') in H1; try assumption.
  Case "SR_3_9".
   intros.
   apply SR_3_9 with (tau':= tau'); try assumption.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   apply H0 with (u':= u') (g':= g') in H1; try assumption.
  Case "SR_3_10".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H1; try assumption.
  Case "SR_3_11".
   intros.
   apply SR_3_11 with (k:=k); try assumption.
   apply H with (u':= u') (g':= g') in H1; try assumption.
  Case "SR_3_12".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H1; try assumption.
  Case "SR_3_13".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   AdmitAlphaConversion.
   admit.
   admit.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   admit.
   admit.
  Case "SR_3_14".
   admit.
  Case "base".
   assumption.
*)
Admitted.
