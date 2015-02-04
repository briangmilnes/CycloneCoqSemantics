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

Require Export CpdtTactics.
Require Export Case.
Require Export TacticNotations.
Require Import VariableModule2.

Set Implicit Arguments.
Set Printing Universes.


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

End TypingInfoFun.

(*
Lemma beq_tau_sym : forall x y, beq_tau x y = beq_tau y x.
Proof.
  induction x; induction y; try solve [crush].
Qed.
Hint Immediate beq_tau_sym.

Lemma beq_tau_trans : 
  forall x y z, 
    beq_tau x y = true -> beq_tau y z = true -> beq_tau x z = true.
Proof.
  induction x; induction y; induction z; intros; try solve [inversion H]; try solve [inversion H0].
  inversion H. inversion H0.
  crush.
  apply beq_tvar_trans with (x:= t) (y:= t0) (z:= t1) in H2; try assumption.
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
Hint Resolve beq_tau_trans.

Lemma beq_tau_eq:
  forall t0 t1, beq_tau t0 t1 = true -> t0 = t1.
Proof.
  induction t0; induction t1; intros; try solve [inversion H].
  inversion H.
  apply beq_tvar_eq in H1.
  rewrite H1.
  reflexivity.
  reflexivity.
  clear IHt1_1.
  clear IHt1_2.
  unfold beq_tau in H.
  fold beq_tau in H.
  apply andb_true_iff in H.
  inversion H.
  apply IHt0_1 in H0.
  apply IHt0_2 in H1.
  subst.
  reflexivity.
Qed.

Lemma beq_tau_neq:
  forall t0 t1, beq_tau t0 t1 = false -> t0 <> t1.
Proof.
  induction t0; induction t1; intros; try solve [inversion H]; try solve [discriminate].
  apply beq_tvar_neq in H.
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
*)
