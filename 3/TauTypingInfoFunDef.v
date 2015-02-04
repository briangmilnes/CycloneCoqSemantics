(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  A module for Tau typing info proofs.

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.
Require Import Coq.Init.Logic.
Require Export Coq.Bool.Bool.

Require Export CpdtTactics.
Require Export Case.
Require Export TacticNotations.
Require Export TypingInfoProofsSigDef.
Require Export TauTypingInfoDef.
Require Export EVarDef.

Set Implicit Arguments.

Module TypingInfoFun(t : TauTypingInfo) <: TypingInfoProofsSig.
  Include t.

Lemma beq_t_refl:
 forall (t : T),
   beq_t t t = true.
Proof.
  intros.
  induction t; crush.
Qed.
Hint Resolve beq_t_refl.

(* not quite sure why I have to change the proof structure here at all. *)
Lemma beq_t_sym : forall x y, beq_t x y = beq_t y x.
Proof.
  induction x; induction y; auto.
  try solve [crush].
  try solve [crush].
  try solve [crush].
  try solve [crush].
  unfold beq_t.
  unfold beq_tau.
  fold beq_tau.
  rewrite beq_var_sym.
  rewrite beq_kappa_sym.
  rewrite IHx.
  reflexivity.
  unfold beq_t.
  unfold beq_tau.
  fold beq_tau.
  rewrite beq_var_sym.
  rewrite beq_phi_sym.
  rewrite beq_kappa_sym.
  rewrite IHx.
  reflexivity.
Qed.
Hint Immediate beq_t_sym.

Lemma beq_t_eq:
  forall t0 t1, beq_tau t0 t1 = true -> t0 = t1.
Proof.
  induction t0; induction t1; intros; try solve [inversion H].

  inversion H.
  apply beq_var_eq in H1.
  rewrite H1.
  reflexivity.
  reflexivity.
  unfold beq_tau in H.
  fold beq_tau in H.
  apply andb_true_iff in H.
  inversion H.
  apply IHt0_1 in H0.
  apply IHt0_2 in H1.
  subst.
  reflexivity.

  unfold beq_tau in H.
  fold beq_tau in H.
  apply andb_true_iff in H.
  inversion H.
  apply IHt0_1 in H0.
  apply IHt0_2 in H1.
  subst.
  reflexivity.

  unfold beq_tau in H.
  fold beq_tau in H.
  apply IHt0 in H.
  rewrite H.
  reflexivity.

  unfold beq_tau in H.
  fold beq_tau in H.
  apply andb_true_iff in H.
  inversion H.
  apply andb_true_iff in H0.
  inversion H0.
  apply IHt0 in H1.
  apply beq_var_eq in H2.
  apply beq_kappa_eq in H3.

Qed.
Hint Resolve beq_t_eq.

Lemma beq_t_neq:
  forall t0 t1, beq_tau t0 t1 = false -> t0 <> t1.
Proof.
  induction t0; induction t1; intros; try solve [inversion H]; try solve [discriminate].
  apply beq_var_neq in H.
  crush.
  unfold beq_tau in H.
  fold beq_tau in H.
  apply andb_false_iff in H.
  destruct H.
  apply IHt0_1 in H.
  crush.
  apply IHt0_2 in H.
  crush.
Qed.  
Hint Resolve beq_t_neq.

Lemma beq_t_trans : 
  forall x y z, 
    beq_t x y = true -> beq_t y z = true -> beq_t x z = true.
Proof.
  induction x; induction y; induction z; intros; try solve [inversion H]; try solve [inversion H0].
  inversion H. inversion H0.
  crush.
  apply beq_var_trans with (b:= v0) (c:= v1) in H2; try assumption.
  reflexivity.
  unfold beq_tau.
  fold beq_tau.
  unfold beq_tau in H.
  fold beq_tau in H.
  unfold beq_tau in H0.
  fold beq_tau in H0.
  apply andb_true_iff in H.
  apply andb_true_iff in H0.
  inversion H.
  inversion H0.
  apply andb_true_iff.
  apply IHx1 with (z:= z1)in H1; try assumption.
  apply IHx2 with (z:= z2)in H2; try assumption.
  split; try assumption.
Qed.
Hint Resolve beq_t_trans.
End TypingInfoFun.
