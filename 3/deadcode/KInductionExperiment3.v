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


Inductive K3 : TVar -> Kappa -> Delta -> Tau -> Kappa -> Prop :=

 | K3_int   : forall (alpha : TVar) (k : Kappa) (d : Delta),
                  K ([(alpha, k)] ++ d) cint B ->
                  K3 alpha  k d cint B

 | K3_B     : forall (beta : TVar) (k : Kappa) (d : Delta) (alpha : TVar),
               getD d alpha = Some B ->
               K ([(beta,k)] ++ d) (tv_t alpha) B ->
               K3 beta k d (tv_t alpha) B

 | K3_star_A  : forall (beta : TVar) (k : Kappa) (d : Delta) (alpha : TVar),
                 getD d alpha = Some A -> 
                 K ([(beta,k)] ++ d) (ptype (tv_t alpha)) B ->
                 K3 beta k d (ptype (tv_t alpha)) B

| K3_B_A     : forall (alpha : TVar) (k : Kappa) (d : Delta) (tau : Tau),
                  K  ([(alpha,k)] ++ d) tau A ->
                  K3 alpha k d tau A

 | K3_cross   : forall (alpha : TVar) (k : Kappa) (d : Delta) (t0 t1 : Tau),
                    K ([(alpha,k)] ++ d) t0 A ->
                    K ([(alpha,k)] ++ d) t1 A ->
                    K3 alpha k d (cross t0 t1) A.
(*
 | K3_arrow   : forall (d : Delta) (t0 t1 : Tau),
                    K3 d t0 A ->
                    K3 d t1 A ->
                    K3 d (arrow t0 t1) A

 | K3_ptype    :  forall (d : Delta) (tau : Tau),
                    K3 d tau A ->
                    K3 d (ptype tau) B

 | K3_utype  : forall (d : Delta) (alpha : TVar) (k : K3appa) (tau : Tau),
                   WFD ([(alpha, k)] ++ d) ->
                   getD d alpha = None -> 
                   K3 ([(alpha, k)] ++ d) tau A ->
                   K3 d (utype alpha k tau) A

 | K3_etype  : forall (d : Delta) (alpha : TVar) (k : K3appa) (tau : Tau) (p : Phi),
                   WFD ([(alpha, k)] ++ d) ->
                   getD d alpha = None -> 
                   K3 ([(alpha, k)] ++ d) tau A ->
                   K3 d (etype p alpha k tau) A.
*)

Print K3_ind.

Inductive AK3 : Delta -> Tau -> Kappa -> Prop :=

 | AK3_AK3_K3  : forall (alpha : TVar) (k' : Kappa) 
                        (d : Delta) (tau : Tau) (k : Kappa),
                   K3  alpha k' d tau k ->
                   AK3 d tau k

 | AK3_A     : forall (d : Delta) (alpha : TVar),
                getD d alpha = Some A ->
                AK3 d (tv_t alpha) A.

Lemma A_6_Substitution_1_more_wrapping_judgement:
  forall (d : Delta) (t' : Tau) (k' : Kappa) (alpha : TVar) (k : Kappa),
    K3 alpha k d  t' k' ->
    WFD ([(alpha,k)] ++ d) ->
    forall (t : Tau),
      AK3 d t k ->
      K d (subst_Tau t' t alpha) k'.
Proof.
  intros d t' k' alpha k K3Der.
  induction K3Der.
 Case "K d cint B".
  intros.
  simpl.
  constructor.
 Case "K d (tv_t alpha) B".
  intros.
  simpl.
  case_eq (beq_tvar beta alpha).
  SCase "(beq_tvar beta alpha) = true".
   intros.
   apply beq_tvar_eq in H3.
   rewrite H3 in *.
   (* invert goal away on WFD ([(alpha, k)] ++ d) *)
   admit.
  SCase "(beq_tvar beta alpha) = false".
   intros.
   apply K3_B in H0; try assumption.
   (* I think this is correct so far. *)
   admit.
 Case "K d (ptype (tv_t alpha)) B".
  intros.
  simpl.
  case_eq (beq_tvar beta alpha).
  SCase "(beq_tvar beta alpha) = true".
   intros.
   admit.
  SCase "(beq_tvar beta alpha) = false".
   intros.
   apply K_star_A in H.
   assumption.
 Case "K d tau A".
  intros.
  constructor.
  inversion H1.
  (* Perhaps unsolvable. *)
  admit.
  admit.
 Case "K d (cross t0 t1) A".
  intros.
  (* No nice induction hypothesis. Total Failure again. *)
 Case "K d (arrow t0 t1) A".
  admit.
 Case "K d (ptype tau) B".
  admit.
 Case "K d (utype alpha k tau) A".
  admit.
 Case "K d (etype p alpha k tau) A)".
  admit.
Qed.

