(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

   The kinding module. 

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.
Require Import Coq.Init.Logic.
Require Import Coq.Bool.Bool.

Require Export BoolEqualitySigDef.
Require Export CpdtTactics.
Require Export Case.

Module KappaModule <: BoolEqualitySig.

Module Base.
Inductive Kappa : Type :=
 | B                         (* 'boxed' kind. *)
 | A.                        (* 'any'   kind. *)

Function beq_kappa (k k' : Kappa) : bool :=
   match k, k' with
     |  A, A => true
     |  B, B => true
     |  _, _ => false
  end.
Hint Unfold  beq_kappa.
Hint Resolve beq_kappa.

Lemma beq_kappa_refl:
  forall (k : Kappa),
    beq_kappa k k = true.
Proof.
  destruct k.
  reflexivity.
  reflexivity.
Qed.
Hint Resolve beq_kappa_refl.

Lemma beq_kappa_sym : forall x y : Kappa, beq_kappa x y = beq_kappa y x.
Proof.
  intros.
  destruct x;  destruct y; crush.
Qed.
Hint Immediate beq_kappa_sym.

Lemma beq_kappa_trans : 
  forall x y z,
    beq_kappa x y = true -> beq_kappa y z = true -> beq_kappa x z = true.
Proof.
   destruct x; destruct y; destruct z; crush.
Qed.
Hint Resolve beq_kappa_trans.

Lemma beq_kappa_eq:
  forall (k k': Kappa),
    beq_kappa k k' = true ->
    k = k'.
Proof.
  intros.
  destruct k; destruct k'.
  reflexivity.
  inversion H.
  inversion H.
  reflexivity.
Qed.
Hint Resolve beq_kappa_eq.

Lemma beq_kappa_neq:
  forall (k k': Kappa),
    beq_kappa k k' = false ->
    k <> k'.
Proof.
  intros.
  destruct k; destruct k'.
  inversion H.
  discriminate.
  discriminate.
  inversion H.
Qed.
Hint Resolve beq_kappa_neq.

Lemma beq_kappa_iff_eq:    forall a b, beq_kappa a b = true <-> a = b.
Proof.
  destruct a; destruct b; crush.
Qed.
Hint Resolve beq_kappa_iff_eq.


Lemma beq_kappa_iff_neq:   forall a b, beq_kappa a b = false <-> a <> b.
Proof.
  destruct a; destruct b; crush.
Qed.
Hint Resolve beq_kappa_iff_neq.
End Base.
Import Base.

Definition T := Kappa.
Definition beq_t := beq_kappa.
Definition beq_t_refl := beq_kappa_refl.
Definition beq_t_sym := beq_kappa_sym.
Definition beq_t_trans := beq_kappa_trans.
Definition beq_t_eq := beq_kappa_eq.
Definition beq_t_neq := beq_kappa_neq.
Definition beq_t_iff_eq := beq_kappa_iff_eq.
Definition beq_t_iff_neq := beq_kappa_iff_neq.
End KappaModule.
