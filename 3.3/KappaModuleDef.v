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
Require Import Coq.Structures.Equalities.

Require Export BoolEqualitySigDef.
Require Export CpdtTactics.
Require Export Case.

Module KappaModule <: BoolEqualitySig.

Module Types.
Inductive Kappa : Type :=
 | B                         (* 'boxed' kind. *)
 | A.                        (* 'any'   kind. *)
End Types.
Include Types.

Definition t := Kappa.

Function eqb (k k' : Kappa) : bool :=
   match k, k' with
     |  A, A => true
     |  B, B => true
     |  _, _ => false
  end.
Hint Unfold  eqb.
Hint Resolve eqb.

Fixpoint eq (a b : t) : Prop :=
    match eqb a b with
     | false => False
     | true => True
    end.

Lemma eqb_refl:
  forall (k : Kappa),
    eqb k k = true.
Proof.
  destruct k.
  reflexivity.
  reflexivity.
Qed.
Hint Resolve eqb_refl.

Lemma eq_refl:
 forall (a : t),
   eq a a.
Proof.
  destruct a;  crush.
Qed.

Lemma eqb_sym : forall x y : Kappa, eqb x y = eqb y x.
Proof.
  intros.
  destruct x;  destruct y; crush.
Qed.
Hint Immediate eqb_sym.

Lemma eq_sym : forall x y : t, eq x y -> eq y x.
Proof.
  destruct x; destruct y; crush.
Qed.

Lemma eqb_trans : 
  forall x y z,
    eqb x y = true -> eqb y z = true -> eqb x z = true.
Proof.
   destruct x; destruct y; destruct z; crush.
Qed.
Hint Resolve eqb_trans.

Lemma eq_trans : 
  forall x y z,
    eq x y -> eq y z -> eq x z.
Proof.
  destruct x; destruct y; destruct z; crush.
Qed.

Lemma eqb_to_eq:
  forall (k k': Kappa),
    eqb k k' = true ->
    k = k'.
Proof.
  intros.
  destruct k; destruct k'.
  reflexivity.
  inversion H.
  inversion H.
  reflexivity.
Qed.
Hint Resolve eqb_to_eq.

Lemma eqb_to_neq:
  forall (k k': Kappa),
    eqb k k' = false ->
    k <> k'.
Proof.
  intros.
  destruct k; destruct k'.
  inversion H.
  discriminate.
  discriminate.
  inversion H.
Qed.
Hint Resolve eqb_to_neq.

Lemma eqb_iff_eq:    forall a b, eqb a b = true <-> a = b.
Proof.
  destruct a; destruct b; crush.
Qed.
Hint Resolve eqb_iff_eq.


Lemma eqb_iff_neq:   forall a b, eqb a b = false <-> a <> b.
Proof.
  destruct a; destruct b; crush.
Qed.
Hint Resolve eqb_iff_neq.

Instance eq_equiv : Equivalence eq.
Proof. 
  split.
  exact eq_refl.
  exact eq_sym.
  exact eq_trans.
Defined.

Lemma eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
Proof.   
  intros.
  destruct x; destruct y;  unfold eq; unfold eqb; crush.
Qed.

Lemma eqb_eq : forall x y : t, eqb x y = true <-> eq x y.
Proof.
  destruct x; destruct y;  crush.
Qed.
End KappaModule.
