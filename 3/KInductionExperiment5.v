(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Just the nearly working proof using Extends1D.

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.
Require Import Coq.Init.Logic.

Require Export FormalSyntax.
Require Export VarLemmas.
Require Export DynamicSemanticsTypeSubstitution.
Require Export DynamicSemanticsHeapObjects.
Require Export DynamicSemantics.
Require Export DynamicSemanticsTypeSubstitution.
Require Export StaticSemanticsKindingAndContextWellFormedness.
Require Export StaticSemantics.
Require Export TypeSafety.
Require Export ContextExtensionRelation.
Require Export StaticSemanticsKindingLemmas.

Require Export CpdtTactics.
Require Export Case.
Require Export TacticNotations.


Require Export AlphaConversion.
Require Export GetLemmasRelation.


Inductive Extends1D : TVar -> Kappa -> Delta -> Delta -> Prop := 
   Extends1D_alpha_kappa : 
      forall (alpha : TVar) (k : Kappa) (d : Delta) (d' : Delta), 
        d' = ([(alpha,k)] ++ d) ->
        WFD d' ->
        getD d alpha = None ->
        Extends1D alpha k d d'.

Tactic Notation "Extends1D_ind_cases" tactic(first) ident(c) :=
 first;
[
Case_aux c "Extends1D_alpha_kappa"
].

Lemma getD_Extends1D_agreement_1:
  forall (d d0 : Delta) (alpha alpha0 : TVar) (k : Kappa) (O : option Kappa),
    Extends1D alpha0 k d0 d ->
    getD d alpha = O -> 
    beq_tvar alpha0 alpha = false -> 
    getD d0 alpha = O.
Proof.
  (* induction d/d0 looks unusable. *)
  intros d d0 alpha alpha0 k O ext.
  induction ext.
  intros.
  rewrite H in *.
  simpl in H2.
  rewrite beq_tvar_symmetric in H3.
  rewrite H3 in H2.
  assumption.
Qed.

Lemma getD_Extends1D_inversion: 
  forall (d : Delta) (alpha : TVar) (d0 : Delta) (k k' : Kappa),
    Extends1D alpha k d0 d -> 
    getD d alpha = Some k' -> 
    k = k'.
Proof.
  intros d alpha d0 k k' ext.
  induction ext.
  intros.
  rewrite H in H2.
  simpl in H2.
  rewrite beq_tvar_reflexive in H2.
  inversion H2.
  reflexivity.
Qed.

Lemma WFD_weakening:
  forall (d0 : Delta) (alpha : TVar) (k : Kappa),
    WFD d0 ->
    getD d0 alpha = None -> 
    WFD ([(alpha,k)] ++ d0).
Proof.
  intros d0 alpha k WFDder.
  WFD_ind_cases (induction WFDder) Case.
 Case "WFD []".
  intros.
  constructor; try assumption.
  constructor.
 Case "WFD ([(alpha, k)] ++ d)".
  intros.
  constructor; try assumption.
  constructor; try assumption.
Qed.

Lemma Extends1D_agreement:
  forall (d : Delta),
    WFD d ->
    forall (d0 : Delta),
      WFD d0 ->
      forall (beta : TVar) (k0 : Kappa),
        Extends1D beta k0 d0 d ->
        getD d beta = None ->
        forall (alpha : TVar),
          beq_tvar beta alpha = false ->
          forall (k : Kappa),
            getD d0 alpha = None ->
            getD d alpha = None ->
            Extends1D beta k0 ([(alpha, k)] ++ d0) ([(alpha, k)] ++ d).
Proof.
  intros d WFDd d0 WFDd0 alpha0 k0 ext.
  induction ext.
  intros.
  constructor.
  rewrite H.
  (* Okay, I'm stuck here because I'm not using a full definition of
     partial maps. *)
  admit.
  constructor; try assumption.
  (* Are these two goals correct? *)
  rewrite <- cons_is_append_singleton.
  unfold getD.
  fold getD.
  rewrite H3; try assumption.
Qed.

Lemma K_weakening1 :
  forall d0,
    WFD d0 ->
    forall t k', 
      K d0 t k' -> 
      forall alpha k, 
        WFD ([(alpha, k)] ++ d0) -> 
        K ([(alpha, k)] ++ d0) t k'.
Proof.
  intros.
  assert (Z: ExtendedByD d0 d0).
  apply ExtendedByD_reflexive.
  apply ExtendedByD_weakening with (alpha:= alpha) (k:= k) in Z.
  apply K_weakening with (d:= d0) (d':= ([(alpha, k)] ++ d0)) (tau:= t) (k:= k') in H; try assumption.
  assumption.
Qed.

(* IH cases working, variables and bindings unknown. *)
(* Lemmas and the variable cases hold.*)
(* Binding still uncertain. *)
Lemma A_6_Substitution_1_Extends1D:
  forall (d' : Delta) (t' : Tau) (k' : Kappa),
    WFD d' -> 
    K d' t' k' ->
    forall (d : Delta) (t : Tau) (k : Kappa),
      WFD d -> 
      AK d t k ->
      forall (alpha : TVar), 
        getD d alpha = None ->
        getD d' alpha = None ->
        Extends1D alpha k d d' ->
        K d (subst_Tau t' t alpha) k'.
Proof.
  intros d' t' k' WFDd' Kder.
  K_ind_cases(induction Kder) Case.
 Case "K d cint B".
  intros.
  simpl.
  constructor.
 Case "K d (tv_t alpha) B".
  intros.
  simpl.
  case_eq (beq_tvar alpha0 alpha).
  SCase "(beq_tvar alpha0 alpha) = true".
   intros. (* The proof of the pudding is here. *)
   apply beq_tvar_eq in H5.
   rewrite H5 in *.
   clear H5.
   apply getD_Extends1D_inversion with (k':= B) in H4; try assumption.
   rewrite H4 in H1.
   inversion H1; try assumption.
  SCase "(beq_tvar alpha0 alpha) = false".
   intros. 
   apply getD_Extends1D_agreement_1 with (alpha:= alpha) (O:= Some B) in H4; try assumption.
   apply K_B; try assumption.
 Case "K d (ptype (tv_t alpha)) B".
  intros.
  simpl.
  case_eq (beq_tvar alpha0 alpha).
  SCase "(beq_tvar alpha0 alpha) = true".
   intros.
   apply beq_tvar_eq in H5.
   rewrite H5 in *.
   clear H5.
   apply getD_Extends1D_inversion with (k':= A) in H4; try assumption.
   rewrite H4 in *.
   inversion H1; try assumption.
   apply K_ptype; try assumption.
   apply K_star_A; try assumption.
  SCase "(beq_tvar alpha0 alpha) = false".
   intros.
   apply K_star_A; try assumption.
   apply getD_Extends1D_agreement_1 with (alpha:= alpha) (O:= Some A) in H4; try assumption.
 Case "K d tau A".
  intros.
  apply IHKder with (alpha:= alpha) (t:= t) (k:= k) (d0:=d0) in WFDd'; try assumption.
  constructor; try assumption.
 Case "K d (cross t0 t1) A".
  intros.
  simpl.
  pose proof WFDd' as WFDd''.
  apply IHKder1 with (alpha:= alpha) (t:= t) (k:= k) (d0:=d0) in WFDd'; try assumption.
  apply IHKder2 with (alpha:= alpha) (t:= t) (k:= k) (d0:=d0) in WFDd''; try assumption.
  apply K_cross; try assumption.
 Case "K d (arrow t0 t1) A".
  intros.
  simpl.
  pose proof WFDd' as WFDd''.
  apply IHKder1 with (alpha:= alpha) (t:= t) (k:= k) (d0:=d0) in WFDd'; try assumption.
  apply IHKder2 with (alpha:= alpha) (t:= t) (k:= k) (d0:=d0) in WFDd''; try assumption.
  apply K_arrow; try assumption.
 Case "K d (ptype tau) B".
  intros.
  apply IHKder with (alpha:= alpha) (t:= t) (k:= k) (d0:=d0) in WFDd'; try assumption.
  simpl.
  apply K_ptype; try assumption.
 Case "K d (utype alpha k tau) A".
  intros.
  simpl.
  case_eq (beq_tvar alpha0 alpha).
  SCase "(beq_tvar alpha0 alpha) = true".
   intros. (* Can I do this without alpha conversion. *)
   AdmitAlphaConversion.
   (* Broken by lemma changes. *)
  SCase "(beq_tvar alpha0 alpha) = false".
   intros.
   pose proof H5 as H5'.
   apply getD_Extends1D_agreement_1 with (alpha:= alpha) (O:= None)
     in H5; try assumption.
   pose proof H1 as H1'.
   apply WFD_weakening with (alpha:= alpha) (k:= k) in H1; try assumption.
   apply K_utype; try assumption.   
   apply IHKder with (alpha0:= alpha0) (t:= t) (k0:= k0) 
     (d0:= [(alpha,k)] ++ d0)  in H; try assumption.
   apply AK_weakening with (d:= d0) (tau:= t) (k:= k0) in H1; try assumption.
   assert (Z: ExtendedByD d0 d0).
   apply ExtendedByD_reflexive.
   apply ExtendedByD_weakening with (alpha:= alpha) (k:= k) in Z; try assumption.
   rewrite <- cons_is_append_singleton.
   unfold getD.
   fold getD.
   rewrite H6; try assumption.
   rewrite <- cons_is_append_singleton.
   unfold getD.
   fold getD.
   rewrite H6; try assumption.
   apply Extends1D_agreement; try assumption.
 Case "K d (etype p alpha k tau) A)".
  intros.
  simpl.
  case_eq (beq_tvar alpha0 alpha).
  SCase "(beq_tvar alpha0 alpha) = true".
   intros. (* Can I do this without alpha conversion. *)
   AdmitAlphaConversion.
   (* Broken by lemma changes. *)
  SCase "(beq_tvar alpha0 alpha) = false".
   intros.
   pose proof H5 as H5'.
   apply getD_Extends1D_agreement_1 with (alpha:= alpha) (O:= None)
     in H5; try assumption.
   pose proof H1 as H1'.
   apply WFD_weakening with (alpha:= alpha) (k:= k) in H1; try assumption.
   apply K_etype; try assumption.   
   apply IHKder with (alpha0:= alpha0) (t:= t) (k0:= k0) 
     (d0:= [(alpha,k)] ++ d0)  in H; try assumption.
   apply AK_weakening with (d:= d0) (tau:= t) (k:= k0) in H1; try assumption.
   assert (Z: ExtendedByD d0 d0).
   apply ExtendedByD_reflexive.
   apply ExtendedByD_weakening with (alpha:= alpha) (k:= k) in Z; try assumption.
   rewrite <- cons_is_append_singleton.
   unfold getD.
   fold getD.
   rewrite H6; try assumption.
   rewrite <- cons_is_append_singleton.
   unfold getD.
   fold getD.
   rewrite H6; try assumption.
   apply Extends1D_agreement; try assumption.
Qed. 
