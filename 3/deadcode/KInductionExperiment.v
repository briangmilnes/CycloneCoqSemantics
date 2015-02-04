(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Why can't I induct on K and keep d connected?

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

Require Export CpdtTactics.
Require Export Case.
Require Export TacticNotations.


Require Export AlphaConversion.
Require Export GetLemmasRelation.

(* Works perfectly ! d is connected. *)
Lemma K_d_induction_test_1:
  forall (d : Delta) (tau : Tau) (k : Kappa),
         K d tau k ->
         K d tau k.
Proof.
  intros d tau k Kder.
  K_ind_cases (induction Kder) Case.
  Case "K d cint B".
   constructor.
   constructor.
   assumption.
   admit.
Admitted.

Lemma K_d_induction_test_2:
  forall (d : Delta) (tau : Tau) (k : Kappa) (alpha : TVar),
         K d tau k ->
         K ([(alpha,k)] ++ d) tau k.
Proof.
  intros d tau k alpha Kder.
  K_ind_cases (induction Kder) Case.
  Case "K d cint B".
   admit.
   Case "K d (tv_t alpha) B".
   admit.
   Case "K d (ptype (tv_t alpha)) B".
   admit.
   (* Still connected. *)
Admitted.

(* This is connected. *)
Lemma K_d_induction_test_3:
  forall (d : Delta) (tau : Tau) (k : Kappa) (alpha : TVar),
         K d tau k ->
         AK d tau k .
Proof.
  intros d tau k alpha Kder.
  K_ind_cases (induction Kder) Case.
  Case "K d cint B".
   admit.
  Case "K d (tv_t alpha) B".
   admit.
  Case "K d (ptype (tv_t alpha)) B".
    admit.
Admitted.

(* This is connected. *)
Lemma K_d_induction_test_4:
  forall (d : Delta) (tau : Tau) (k : Kappa) (alpha : TVar),
         K d tau k ->
         K d (subst_Tau tau tau alpha) k.
Proof.
  intros d tau k alpha Kder.
  K_ind_cases (induction Kder) Case.
  Case "K d cint B".
   admit.
  Case "K d (tv_t alpha) B".
   admit.
  Case "K d (ptype (tv_t alpha)) B".
    admit.
Admitted.

(* Disconnected! yeah. *)
Lemma K_d_induction_test_5:
  forall (d : Delta) (tau : Tau) (k : Kappa) (alpha : TVar),
    K ([(alpha,k)] ++ d) tau k ->
    K d tau k.
Proof.
  intros d tau k alpha Kder.
  K_ind_cases (induction Kder) Case.
  Case "K d cint B".
   admit.
  Case "K d (tv_t alpha) B".
   admit.
  Case "K d (ptype (tv_t alpha)) B".
   admit.
Admitted.

(* OK so the induction principle or induction does not handle a deconstructed
 d in the inductive base. *)

(* Let's try equational connectivity. WORKS! But wrong theorem statement!*)
Lemma K_d_induction_test_6:
  forall (d : Delta) (tau : Tau) (k : Kappa) (alpha : TVar),
      K d tau k ->
      forall (d' : Delta),
        d = ([(alpha,k)] ++ d') ->
        K d tau k.
Proof.
   intros d tau k alpha Kder.
  K_ind_cases (induction Kder) Case.
  Case "K d cint B".
   admit.
  Case "K d (tv_t alpha) B".
   intros.
   admit.
  Case "K d (ptype (tv_t alpha)) B".
   admit.
Admitted.


(* Let's try equational connectivity. WORKS! *)
(* Looks good, time to try it in the real theorem. *)
Lemma K_d_induction_test_7:
  forall (d : Delta) (tau : Tau) (k : Kappa) (alpha : TVar),
      K d tau k ->
      forall (d' : Delta),
        d = ([(alpha,k)] ++ d') ->
        K d' tau k.
Proof.
  intros d tau k alpha Kder.
  K_ind_cases (induction Kder) Case.
  Case "K d cint B".
   admit.
  Case "K d (tv_t alpha) B".
   intros.
   admit.
  Case "K d (ptype (tv_t alpha)) B".
   admit.
  admit.

Admitted.
  
(* Nope I get broken induction hyptotheses! Something is 
 wrong in K induction or getD if you ask me. 

*)

Inductive K' : Delta -> Tau -> Kappa -> Prop :=
(*
 | K_int   : forall (d : Delta),
                  K' d cint B
*)

 | K_B     : forall (d : Delta) (alpha : TVar),
               getD d alpha = Some B ->
               K' d (tv_t alpha) B

 | K_star_A  : forall (d : Delta) (alpha : TVar),
                 getD d alpha = Some A -> 
                 K'  d (ptype (tv_t alpha)) B.

(*
(* Take out the A/B loop and see what happens, still disconnected. *)
 | K_B_A     : forall (d : Delta) (tau : Tau),
                  K'  d tau B ->
                  K'  d tau A

 | K_cross   : forall (d : Delta) (t0 t1 : Tau),
                    K' d t0 A ->
                    K' d t1 A ->
                    K' d (cross t0 t1) A

 | K_arrow   : forall (d : Delta) (t0 t1 : Tau),
                    K' d t0 A ->
                    K' d t1 A ->
                    K' d (arrow t0 t1) A

 | K_ptype    :  forall (d : Delta) (tau : Tau),
                    K' d tau A ->
                    K' d (ptype tau) B

 | K_utype  : forall (d : Delta) (alpha : TVar) (k : Kappa) (tau : Tau),
                   WFD ([(alpha, k)] ++ d) ->
                   getD d alpha = None -> 
                   K' ([(alpha, k)] ++ d) tau A ->
                   K' d (utype alpha k tau) A

 | K_etype  : forall (d : Delta) (alpha : TVar) (k : Kappa) (tau : Tau) (p : Phi),
                   WFD ([(alpha, k)] ++ d) ->
                   getD d alpha = None -> 
                   K' ([(alpha, k)] ++ d) tau A ->
                   K' d (etype p alpha k tau) A.
*)

Inductive AK' : Delta -> Tau -> Kappa -> Prop :=

 | AK_AK_K  : forall (d : Delta) (tau : Tau) (k : Kappa),
                   K'  d tau k ->
                   AK' d tau k

 | AK_A     : forall (d : Delta) (alpha : TVar),
                getD d alpha = Some A ->
                AK' d (tv_t alpha) A.

Lemma A_6_Substitution_1:
  forall (d : Delta) (tau : Tau) (k : Kappa),
      AK' d tau k -> 
      forall (alpha : TVar) (k' : Kappa) (tau' : Tau), 
        K' ([(alpha,k)] ++ d) tau' k' ->
        K' d (subst_Tau tau' tau alpha) k'.
Proof.
  intros d tau k AK alpha k' tau' Kder.
  induction Kder.
  Case "K d cint B".
   admit.
  Case "K d (tv_t alpha) B".
   admit. (* Disconnected starting right here. *)
Qed.


Lemma A_6_Substitution_1_extendedby:
  forall (d d' : Delta) (t' : Tau) (k' : Kappa) (alpha : TVar) (k : Kappa),
    ExtendedByD d d' ->
    getD d' alpha = Some k ->
    getD d alpha = None ->
    K d' t' k' ->
    forall (t : Tau),
      AK d t k ->
      K d (subst_Tau t' t alpha) k'.
Proof.
  intros d d' t' k' alpha k ext getd'alphasomek getdalphanone Kder.
  K_ind_cases(induction Kder) Case.
  Case "K d cint B".
   intros.
   simpl.
   constructor.
  Case "K d (tv_t alpha) B".
   intros.
   simpl.
   case_eq (beq_tvar alpha alpha0).
    SCase "beq_tvar alpha alpha0 = true".
     intros.
     admit.
    SCase "beq_tvar alpha alpha0 = false".
     intros.
     (* Still looks false. *)
     admit.
  Case "K d (ptype (tv_t alpha)) B".
   intros.
   simpl.
   case_eq (beq_tvar alpha alpha0).
    SCase "beq_tvar alpha alpha0 = true".
     intros.
     apply beq_tvar_eq in H1.
     rewrite H1 in *.
     apply K_ptype.
     inversion H0; try assumption.
     admit.
     crush.
     admit.
    SCase "beq_tvar alpha0 alpha = false".
     intros.
     apply K_ptype.
     admit.
  Case "K d tau A".
   intros.
   apply K_B_A.
   admit.
  Case "K d (cross t0 t1) A".
   intros.
   pose proof H as H'.
(*
   apply IHKder1 with (alpha:= alpha) in H; try assumption.
   apply IHKder2 with (alpha:= alpha) in H'; try assumption.
   simpl.
   apply K_cross; try assumption.
  Case "K d (arrow t0 t1) A".
   intros.
   pose proof H as H'.
   apply IHKder1 with (alpha:= alpha) in H; try assumption.
   apply IHKder2 with (alpha:= alpha) in H'; try assumption.
   simpl.
   apply K_arrow; try assumption.
  Case "K d (ptype tau) B".
   intros.
   apply IHKder with (alpha:= alpha) in H; try assumption.
   simpl.
   apply K_ptype; try assumption.
  Case "K d (utype alpha k tau) A".
    intros.
    apply IHKder with (alpha0:= alpha) in H1; try assumption.
    simpl.
    case_eq (beq_tvar alpha0 alpha).
    SCase "beq_tvar alpha0 alpha = true".
     intros.
     AdmitAlphaConversion.
    SCase "beq_tvar alpha0 alpha = false".
     intros.
     apply K_utype; try assumption.
     admit. 
     (* WFD ([(alpha, k)] ++ d)-> ExtendedByD d0 d -> WFD ([(alpha, k)] ++ d0) *)
     admit.
     (* WFD ([(alpha, k)] ++ d) -> ExtendedByD d0 d -> getD d0 alpha = None. *)
     admit.
     (* WFD ([(alpha, k)] ++ d) -> ExtendedByD d0 d -> ExtendedByD d0 ([(alpha, k)] ++ d) *)
     admit. 
     admit. (* getD ([(alpha, k)] ++ d) alpha = Some k0 why? *)
     admit.
  Case "K d (etype p alpha k tau) A)".
   admit.
*)
Admitted.

(* Doubtful this will do anything as I need an induction that wraps at
 every constructor or I must induct again on K. *)
Inductive K2 : TVar -> Kappa -> Delta -> Tau -> Kappa -> Prop :=
  | K2_wrap : 
      forall (alpha : TVar) (k : Kappa) (d : Delta) (t : Tau) (k' : Kappa),
        K ([(alpha,k)] ++ d) t k' ->
        K2 alpha k d t k'.


Lemma A_6_Substitution_1_wrapping_judgement:
  forall (d : Delta) (t' : Tau) (k' : Kappa) (alpha : TVar) (k : Kappa),
    K2 alpha k d  t' k' ->
    forall (t : Tau),
      AK d t k ->
      K d (subst_Tau t' t alpha) k'.
Proof.
  intros d t' k' alpha k K2Der.
  induction K2Der.
  intros.
  induction H.
 Case "K d cint B".
  admit.
 Case "K d (tv_t alpha) B".
 admit. (* Fail. *)
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

