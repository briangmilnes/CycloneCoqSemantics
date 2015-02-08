(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  A very simple module for two flags on existential types.

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
Require Export NatLemmas.

Module PhiModule <: BoolEqualitySig.

Inductive Phi : Type :=
 | witnesschanges  : Phi                            (* Allowing witness changes. \delta *)
 | aliases        : Phi.                             (* Allowing aliases as the opened type. \amp *)

Definition T := Phi.

Function beq_t (p p' : Phi) : bool :=
  match p, p' with
    | witnesschanges, witnesschanges => true
    | aliases, aliases => true
    | _, _ => false
  end.
Hint Unfold  beq_t.
Hint Resolve beq_t.

Lemma beq_t_refl:
  forall (k : Phi),
    beq_t k k = true.
Proof.
  destruct k.
  reflexivity.
  reflexivity.
Qed.
Hint Resolve beq_t_refl.

Lemma beq_t_sym : forall x y : Phi, beq_t x y = beq_t y x.
Proof.
  intros.
  destruct x;  destruct y; crush.
Qed.
Hint Immediate beq_t_sym.

Lemma beq_t_trans : 
  forall x y z,
    beq_t x y = true -> beq_t y z = true -> beq_t x z = true.
Proof.
   destruct x; destruct y; destruct z; crush.
Qed.
Hint Resolve beq_t_trans.

Lemma beq_t_eq:
  forall (k k': Phi),
    beq_t k k' = true ->
    k = k'.
Proof.
  intros.
  destruct k; destruct k'.
  reflexivity.
  inversion H.
  inversion H.
  reflexivity.
Qed.
Hint Resolve beq_t_eq.

Lemma beq_t_neq:
  forall (k k': Phi),
    beq_t k k' = false ->
    k <> k'.
Proof.
  intros.
  destruct k; destruct k'.
  inversion H.
  discriminate.
  discriminate.
  inversion H.
Qed.
Hint Resolve beq_t_neq.

Lemma beq_t_iff_eq:    forall a b, beq_t a b = true <-> a = b.
Proof.
  destruct a; destruct b; crush.
Qed.
Hint Resolve beq_t_iff_eq.

Lemma beq_t_iff_neq:   forall a b, beq_t a b = false <-> a <> b.
Proof.
  destruct a; destruct b; crush.
Qed.
Hint Resolve beq_t_iff_neq.
End PhiModule.