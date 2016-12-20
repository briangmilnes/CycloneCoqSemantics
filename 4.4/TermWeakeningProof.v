(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Defining type safety, page 67.

*)

Set Implicit Arguments.
Set Implicit Arguments.
Require Export Cyclone_Formal_Syntax Cyclone_Static_Semantics_Kinding_And_Context_Well_Formedness.
Require Export Cyclone_Static_Semantics_Typing_Heap_Objects.
Require Export Cyclone_Classes Cyclone_Inductions.
Require Export Cyclone_LN_Tactics Cyclone_LN_Extra_Lemmas_And_Automation.
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
  induction H3; auto.
  apply gettype_etype with (tau'':= tau''); auto.
Qed.

Function A_2_Term_Weakening_prop (In : Type) (H : TypJudgement In) 
         (d : Delta) (u : Upsilon) (g : Gamma) (s : In) (t : Tau)
         (st : typ' d u g s t) := 
    typ' d u g s t ->
    WFC d u g -> 
      forall (u' : Upsilon) (g' : Gamma),
        WFC d u' g' ->
        LVPE.extends u u' ->
        extends g g' ->
        typ' d u' g' s t.
Hint Unfold A_2_Term_Weakening_prop.


Ltac solve_typ := 
 match goal with 
 | |- (styp _ _ _ (letx _ _) _)          
	=> idtac "1"; apply_fresh_from styp_let_3_6 with fv_of_static_goal
 | |- (styp _ _ _ (openx _ _) _)         
	=> idtac "2"; apply_fresh_from styp_open_3_7 with fv_of_static_goal
 | |- (styp _ _ _ (openstar _ _) _)      
	=> idtac "3"; apply_fresh_from styp_openstar_3_8 with fv_of_static_goal
 | |- (rtyp _ _ _ (pack _ _ _) _)       
	=> idtac "4"; apply_fresh_from SR_3_12 with fv_of_static_goal
 | |- (rtyp _ _ _ (f_e (ufun _ _)) _)    
	=> idtac "5"; apply_fresh_from SR_3_14 with fv_of_static_goal
 | |- (rtyp _ _ _ (f_e (dfun _ _ _ )) _) 
	=> idtac "6"; apply_fresh_from SR_3_13 with fv_of_static_goal
 | |- (ltyp _ _ _ (p_e _ _) _) =>
   idtac "12"; applys SL_3_1
 | |- (rtyp ?a ?b ?c (p_e ?d ?e) ?f) =>
   idtac "13 a b c d e f"; applys SR_3_1
 | |- (ltyp _ _ _  (dot (p_e _ _) zero_pe) _) =>
   idtac "14"; applys SL_3_3
 | |- (ltyp _ _ _ (dot (p_e _ _) one_pe)  _)  =>
   idtac "15"; applys SL_3_4
 | |- (rtyp _ _ _ (dot _ zero_pe) _)          =>
   idtac "16"; applys SR_3_3
 | |- (rtyp _ _ _ (dot _ one_pe)  _)          =>
   idtac "17"; applys SR_3_4
 | |- (styp _ _ _ (e_s _) _)                  =>
   idtac "18"; applys styp_e_3_1
 | |- (rtyp _ _ _ (appl _ _) _)               =>
   idtac "19"; applys SR_3_9
end.

Lemma gettype_weakening:
  forall u u' x tau' p tau,
  gettype u x nil tau' p tau ->
  LVPE.extends u u' ->
  gettype u' x nil tau' p tau.
Admitted.


Lemma A_2_Term_Weakening_2:
  forall (d : Delta) (u : Upsilon) (g : Gamma) (s : E) (t : Tau) (ty : typ' d u g s t),
   A_2_Term_Weakening_prop LtypJudgement d u g s t ty.
Proof.
  intros.
  Typ_Induction ltyp_ind_mutual A_2_Term_Weakening_prop; intros; auto.
  admit.
  admit.
  admit.
  apply SL_3_1 with (tau':=tau'); auto.
  apply gettype_weakening with (u:= u0); auto.
  apply SL_3_3 with (t1:= t1); auto.
  apply SL_3_4 with (t0:= t0); auto.
  apply SR_3_1 with (tau':= tau'); auto.
  apply gettype_weakening with (u:= u0); auto.
  apply SR_3_3 with (t1:= t1); auto.
  apply SR_3_4 with (t0:= t0); auto.
  apply SR_3_9 with (tau':= tau'); auto.
  apply SR_3_11 with (k:=k) (tau':= tau'); auto.
  admit.
  apply SR_3_13 with (L:=        ((((((((((((((L \u T.fv t) \u T.fv tau) \u T.fv tau') \u TM.fv_st s0) \u TM.fv_e s) \u
                TTM.fv_st s0) \u TTM.fv_e s) \u fv_delta d) \u 
             fv_delta d0) \u fv_gamma g) \u fv_gamma g0) \u fv_gamma g') \u 
         fv_upsilon u) \u fv_upsilon u0) \u fv_upsilon u'). auto.
  
  
  apply styp_let_3_6 with (tau':= tau') (L:= 
((((((((((((((((L \u T.fv t) \u T.fv tau) \u T.fv tau') \u TM.fv_st s0) \u
                   TM.fv_e s) \u TM.fv_e e) \u TTM.fv_st s0) \u 
                TTM.fv_e s) \u TTM.fv_e e) \u fv_delta d) \u fv_delta d0) \u 
            fv_gamma g) \u fv_gamma g0) \u fv_gamma g') \u fv_upsilon u) \u 
        fv_upsilon u0) \u fv_upsilon u').
  intros.
  auto.
  apply_fresh_from styp_let_3_6 with fv_of_static_goal.
  solve_typ.

  admit.
  admit.
  admit.

  admit.
  apply SL_3_3 with (t1:= t1); auto.
  apply SL_3_4 with (t0:= t0); auto.

  

barrier .



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
