(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  The heap is path checked using identifiers as and paths, so this
 is the domain of the Upsilon context.

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.
Require Import Coq.Init.Logic.
Require Import Coq.Bool.Bool.
Require Import Coq.Structures.Equalities.

Require Export BooleanEqualityDef.
Require Export EVarModuleDef.
Require Export PathModuleDef.
Require Export CpdtTactics. 
Require Export Case.

Module EVarPathModule <: BooleanEquality.
  Module Path := PathModule.
  Include Path.Types.
  Module EV := EVarModule.
  Definition EVar := EV.t.

Module Types.
Definition UE := prod EVar Path.
End Types.
Include Types.

(* Does andb here break unfold ? *)
Function beq_ue (u u' : UE) : bool := 
  match u, u' with
    | (x,p), (x', p') => andb (EV.eqb x x') (Path.beq_path p p')
  end.
Hint Resolve beq_ue.

Lemma beq_ue_refl:
 forall (u : UE),
   beq_ue u u = true.
Proof.
  induction u; crush.
Qed.
Hint Resolve beq_ue_refl.

Lemma beq_ue_sym : forall u u', beq_ue u u' = beq_ue u' u.
Proof.
  induction u; induction u'; try solve[crush].
  unfold beq_ue.
  fold beq_ue.
  rewrite EV.eqb_sym.
  rewrite Path.beq_path_sym.
  reflexivity.
Qed.
Hint Immediate beq_ue_sym.

Lemma beq_ue_to_eq:
  forall u u',
    beq_ue u u' = true ->
    u = u'.
Proof.
  induction u; induction u'; try solve [crush].
  unfold beq_ue.
  fold beq_ue.
  intros.
  apply andb_true_iff in H.
  inversion H.
  apply EV.eqb_to_eq in H0.
  apply Path.beq_path_eq in H1.
  subst.
  reflexivity.
Qed.
Hint Resolve beq_ue_to_eq.

Lemma beq_ue_trans:
  forall u u0 u1,
    beq_ue u u0 = true ->
    beq_ue u0 u1 = true ->
    beq_ue u u1 = true.
Proof.
  intros.
  pose proof H as H'.
  pose proof H0 as H0'.
  apply beq_ue_to_eq in H.
  apply beq_ue_to_eq in H0.
  subst.
  apply beq_ue_refl.
Qed.

Lemma beq_ue_to_neq:
  forall u u',
    beq_ue u u' = false ->
    u <> u'.
Proof.
  induction u; induction u'; try solve [crush].
  unfold beq_ue.
  fold beq_ue.
  intros.
  apply andb_false_iff in H.
  inversion H.
  apply EV.eqb_to_neq in H0.
  crush.
  apply Path.beq_path_neq in H0.
  crush.
Qed.
Hint Resolve beq_ue_to_eq.

Lemma beq_ue_iff_eq:    forall a b, beq_ue a b = true <-> a = b.
Proof.
  intros.
  split.
  apply beq_ue_to_eq.
  intros.
  rewrite H.
  apply beq_ue_refl.
Qed.
Hint Resolve beq_ue_iff_eq.

Lemma beq_ue_iff_neq:   forall a b, beq_ue a b = false <-> a <> b.
Proof.
  intros.
  split.
  apply beq_ue_to_neq.
  intros.
  induction a; induction b; try solve[crush].
Admitted.
Hint Resolve beq_ue_iff_neq.


Definition t := UE.
Definition eqb := beq_ue.
Definition eqb_refl := beq_ue_refl.
Definition eqb_sym := beq_ue_sym.
Definition eqb_trans := beq_ue_trans.
Definition eqb_to_eq := beq_ue_to_eq.
Definition eqb_to_neq := beq_ue_to_neq.
Definition eqb_iff_eq := beq_ue_iff_eq.
Definition eqb_iff_neq := beq_ue_iff_neq.

Fixpoint eq (a b : t) : Prop :=
    match eqb a b with
     | false => False
     | true => True
    end.

Ltac destruct_away := 
  repeat match goal with
    | [ |- ?X = true <-> _ ] => destruct X; try solve[crush]
         end.

Lemma eqb_eq : forall x y : t, eqb x y = true <-> eq x y.
Proof.
  induction x; induction y;
  try solve[
        unfold eq;
        unfold eqb;
        destruct_away;
        crush].
Qed.

Lemma eq_refl:
 forall (a : t),
   eq a a.
Proof.
  intros.
  rewrite <- eqb_eq.
  apply eqb_refl.
Qed.

Lemma eq_sym : forall x y : t, eq x y -> eq y x.
Proof.
  intros.
  rewrite <- eqb_eq.
  rewrite <- eqb_eq in H.
  rewrite eqb_sym.
  assumption.
Qed.

Lemma eq_trans : 
  forall x y z,
    eq x y -> eq y z -> eq x z.
Proof.
  intros.
  rewrite <- eqb_eq.
  rewrite <- eqb_eq in H.
  rewrite <- eqb_eq in H0.
  apply eqb_trans with (u:= x) (u0:= y) (u1:= z); try assumption.
Qed.

Instance eq_equiv : Equivalence eq.
Proof. 
  split.
  exact eq_refl.
  exact eq_sym.
  exact eq_trans.
Defined.

Ltac destruct_evidence := 
  repeat match goal with
    | [ |- {(if ?X then True else False)} + { _ } ] => 
      destruct X; try solve[simpl; right; congruence];
      try solve[simpl; left; trivial]
 end.

Lemma eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
Proof.   
  intros.
  destruct x; destruct y;  unfold eq; unfold eqb; destruct_evidence; crush.
Qed.

End EVarPathModule.
