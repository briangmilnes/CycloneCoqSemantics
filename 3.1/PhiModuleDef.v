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

Module PhiModule.

Inductive Phi : Type :=
 | witnesschanges  : Phi                            (* Allowing witness changes. \delta *)
 | aliases        : Phi.                            (* Allowing aliases as the opened type. \amp *)

Function beq_phi (p p' : Phi) : bool :=
  match p, p' with
    | witnesschanges, witnesschanges => true
    | aliases, aliases => true
    | _, _ => false
  end.
Hint Unfold  beq_phi.
Hint Resolve beq_phi.

Lemma beq_phi_refl:
  forall (k : Phi),
    beq_phi k k = true.
Proof.
  destruct k.
  reflexivity.
  reflexivity.
Qed.
Hint Resolve beq_phi_refl.

Lemma beq_phi_sym : forall x y : Phi, beq_phi x y = beq_phi y x.
Proof.
  intros.
  destruct x;  destruct y; crush.
Qed.
Hint Immediate beq_phi_sym.

Lemma beq_phi_trans : 
  forall x y z,
    beq_phi x y = true -> beq_phi y z = true -> beq_phi x z = true.
Proof.
   destruct x; destruct y; destruct z; crush.
Qed.
Hint Resolve beq_phi_trans.

Lemma beq_phi_eq:
  forall (k k': Phi),
    beq_phi k k' = true ->
    k = k'.
Proof.
  intros.
  destruct k; destruct k'.
  reflexivity.
  inversion H.
  inversion H.
  reflexivity.
Qed.
Hint Resolve beq_phi_eq.

Lemma beq_phi_neq:
  forall (k k': Phi),
    beq_phi k k' = false ->
    k <> k'.
Proof.
  intros.
  destruct k; destruct k'.
  inversion H.
  discriminate.
  discriminate.
  inversion H.
Qed.
Hint Resolve beq_phi_neq.

Lemma beq_phi_iff_eq:    forall a b, beq_phi a b = true <-> a = b.
Proof.
  destruct a; destruct b; crush.
Qed.
Hint Resolve beq_phi_iff_eq.

Lemma beq_phi_iff_neq:   forall a b, beq_phi a b = false <-> a <> b.
Proof.
  destruct a; destruct b; crush.
Qed.
Hint Resolve beq_phi_iff_neq.
End PhiModule.