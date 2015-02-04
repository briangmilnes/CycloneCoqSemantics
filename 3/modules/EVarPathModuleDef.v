(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  An attempt at a variable module in a context. 

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.
Require Import Coq.Init.Logic.
Require Import Coq.Bool.Bool.

Add LoadPath "/home/milnes/Desktop/Research/Cyclone/CycloneCoq/3".
Require Export BoolEqualitySigDef.
Require Export EVarModuleDef.
Require Export PathModuleDef.
Require Export CpdtTactics. 
Require Export Case.
Require Export TacticNotations.

Module EVarPathModule <: BoolEqualitySig.
  Module E := EVarModule.
  Module P := PathModule.

  Definition UE := prod E.Var P.P.
  Definition T := UE.

Function beq_ue (u u' : UE) : bool := 
  match u, u' with
    | (x,p), (x', p') => andb (E.beq_var x x') (P.beq_path p p')
  end.
Hint Resolve beq_ue.
Definition beq_t := beq_ue.

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
  rewrite E.beq_var_sym.
  rewrite P.beq_path_sym.
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
  apply E.beq_var_eq in H0.
  apply P.beq_path_eq in H1.
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
  apply E.beq_var_neq in H0.
  crush.
  apply P.beq_path_neq in H0.
  crush.
Qed.
Hint Resolve beq_ue_eq.

Definition beq_t_refl := beq_ue_refl.
Definition beq_t_sym := beq_ue_sym.
Definition beq_t_trans := beq_ue_trans.

Definition beq_t_eq := beq_ue_eq.
Definition beq_t_neq := beq_ue_neq.
End EVarPathModule.
