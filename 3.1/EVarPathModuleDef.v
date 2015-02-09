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

Require Export BoolEqualitySigDef.
Require Export EVarModuleDef.
Require Export PathModuleDef.
Require Export CpdtTactics. 
Require Export Case.

Module EVarPathModule <: BoolEqualitySig.
  Include PathModule.

Module Base.

Definition UE := prod E.Var Path.

Function beq_ue (u u' : UE) : bool := 
  match u, u' with
    | (x,p), (x', p') => andb (E.beq_t x x') (beq_path p p')
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
  rewrite E.beq_t_sym.
  rewrite beq_path_sym.
  reflexivity.
Qed.
Hint Immediate beq_ue_sym.

Lemma beq_ue_eq:
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
  apply E.beq_t_eq in H0.
  apply beq_path_eq in H1.
  subst.
  reflexivity.
Qed.
Hint Resolve beq_ue_eq.

Lemma beq_ue_trans:
  forall u u0 u1,
    beq_ue u u0 = true ->
    beq_ue u0 u1 = true ->
    beq_ue u u1 = true.
Proof.
  intros.
  pose proof H as H'.
  pose proof H0 as H0'.
  apply beq_ue_eq in H.
  apply beq_ue_eq in H0.
  subst.
  apply beq_ue_refl.
Qed.

Lemma beq_ue_neq:
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
  apply E.beq_t_neq in H0.
  crush.
  apply beq_path_neq in H0.
  crush.
Qed.
Hint Resolve beq_ue_eq.

Lemma beq_ue_iff_eq:    forall a b, beq_ue a b = true <-> a = b.
Proof.
  intros.
  split.
  apply beq_ue_eq.
  intros.
  rewrite H.
  apply beq_ue_refl.
Qed.
Hint Resolve beq_ue_iff_eq.

Lemma beq_ue_iff_neq:   forall a b, beq_ue a b = false <-> a <> b.
Proof.
  intros.
  split.
  apply beq_ue_neq.
  intros.
  induction a; induction b; try solve[crush].
Admitted.
Hint Resolve beq_ue_iff_neq.

End Base.
Include Base.

Definition T := UE.
Definition beq_t := beq_ue.
Definition beq_t_refl := beq_ue_refl.
Definition beq_t_sym := beq_ue_sym.
Definition beq_t_trans := beq_ue_trans.
Definition beq_t_eq := beq_ue_eq.
Definition beq_t_neq := beq_ue_neq.
Definition beq_t_iff_eq := beq_ue_iff_eq.
Definition beq_t_iff_neq := beq_ue_iff_neq.
End EVarPathModule.
