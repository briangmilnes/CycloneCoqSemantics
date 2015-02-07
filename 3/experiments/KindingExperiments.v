(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  I've sussed out some properties of K that might help with the
 K [] tau A cases that pop up.

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.
Require Import Coq.Init.Logic.

Require Export FormalSyntax.
Require Export DynamicSemanticsTypeSubstitution.
Require Export DynamicSemanticsHeapObjects.
Require Export DynamicSemantics.
Require Export DynamicSemanticsTypeSubstitution.
Require Export StaticSemanticsKindingAndContextWellFormedness.
Require Export StaticSemantics.
Require Export TypeSafety.
Require Export CpdtTactics.
Require Export TacticNotations.

Require Export ListLemmas.
Require Export GetLemmasRelation.

(* Only the cases we need for below. *)
Inductive ClosedType : Tau -> Prop :=
  | ClosedType_cint  : 
      ClosedType cint

  | ClosedType_cross : 
      forall (t0 t1 : Tau), 
        ClosedType t0 ->
        ClosedType t1 ->
        ClosedType (cross t0 t1).
(* Add etype. *)

(* A strict component type, e.g., a piece of a type. *)
(* Lesson learned, disjunctive recursion. *)
Inductive ComponentType : Tau -> Tau -> Prop :=
  | ComponentType_cint : 
      ComponentType cint cint

  | ComponentType_cross:
      forall (t t0 t1 : Tau),
        ComponentType t t0 \/ ComponentType t t1 ->
        ComponentType t (cross t0 t1)

  | ComponentType_etype :
      forall (t t' : Tau),
        ComponentType t t' ->
        forall (alpha : TVar) (k : Kappa),
          ComponentType t (etype aliases alpha k t').

(* Wonderful lemma, but is it useful? *)
Lemma Kinding_A_allows_nil_component_kinding_A:
  forall (tau : Tau) (d : Delta),
    K d tau A ->
    forall (tau' : Tau),
      ClosedType tau' ->
      ComponentType tau' tau ->
      K [] tau' A.
Proof.
  intros tau d Kder.
  K_ind_cases (induction Kder) Case.
  Case "K d cint B".
   intros.
   destruct tau'; try solve[inversion H0; inversion H1].
   constructor.
  Case "K d (tv_t alpha) B".
   intros.
   destruct H0; try solve [inversion H1; inversion H0].
  Case "K d (ptype (tv_t alpha)) B".
   intros.
   destruct H0; try solve [inversion H1; inversion H0].
  Case "K d tau A". 
   intros.
   apply IHKder in H; try assumption.
   constructor; try assumption.
  Case "K d (cross t0 t1) A".
   intros.
   inversion H0.
   inversion H3.
   apply IHKder1 in H; try assumption.
   apply IHKder2 in H; try assumption.
  Case "K d (arrow t0 t1) A".
   intros.
   inversion H0.
  Case "K d (ptype tau) B".
   intros.
   inversion H0.
  Case "K d (utype alpha k tau) A".
   intros.
   inversion H2.
  Case "K d (etype p alpha k tau) A)".
   intros.
   inversion H2.
   crush.
Qed.

Lemma Closed_Concrete_Types_Kind_At_A:
  forall (tau : Tau),
      ClosedType tau ->
      K [] tau A.
Proof.
  intros tau CTder.
  induction CTder.
  Case "cint".
   constructor.
   constructor.
  Case "cross t0 t1".
   apply K_cross; try assumption.
Qed.

(* Okay so somehow I can extend this to etype with a closed type substituted in. *)
