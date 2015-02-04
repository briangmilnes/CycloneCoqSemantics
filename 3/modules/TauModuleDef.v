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
Require Export TVarModuleDef.
Require Export KappaModuleDef.
Require Export PhiModuleDef.
Require Export CpdtTactics. 
Require Export Case.
Require Export TacticNotations.

Module TauModule <: BoolEqualitySig.
  Module K := KappaModule.
  Module P := PhiModule.
  Module T := TVarModule.

Hint Resolve K.beq_kappa_refl.
Hint Immediate K.beq_kappa_sym.
Hint Resolve K.beq_kappa_trans.
Hint Resolve K.beq_kappa_eq.
Hint Resolve K.beq_kappa_neq.

Hint Resolve P.beq_phi_refl.
Hint Immediate P.beq_phi_sym.
Hint Resolve P.beq_phi_trans.
Hint Resolve P.beq_phi_eq.
Hint Resolve P.beq_phi_neq.


Inductive Tau : Type :=
 | tv_t   : T.Var -> Tau                             (* A type variable is a type. *)
 | cint   : Tau                                      (* Cyclone's Integers. *)
 | cross  : Tau -> Tau -> Tau                        (* Pairs. *)
 | arrow  : Tau -> Tau -> Tau                        (* Function    type. *)
 | ptype  : Tau -> Tau                               (* Pointer     type. *)
 | utype  : T.Var -> K.Kappa -> Tau -> Tau           (* Universal   type. *)
 | etype  : P.Phi -> T.Var -> K.Kappa -> Tau -> Tau. (* Existential type. *)

Definition T := Tau.

Function beq_tau (t t' : T) : bool :=
 match t, t' with
 | tv_t alpha, tv_t beta => T.beq_var alpha beta
 | cint, cint => true
 | (cross t0 t1), (cross t0' t1') => andb (beq_tau t0 t0') (beq_tau t1 t1')
 | (arrow t0 t1), (arrow t0' t1') => andb (beq_tau t0 t0') (beq_tau t1 t1')
 | ptype t, ptype t' => (beq_tau t t')
(* No alpha conversion for the moment. *)
 | utype alpha kappa tau, utype alpha' kappa' tau' =>
   andb (andb (T.beq_var alpha alpha') (K.beq_kappa kappa kappa'))
        (beq_tau tau tau')
 | etype p alpha kappa tau, etype p' alpha' kappa' tau' =>
   andb (andb (P.beq_phi p p')  (T.beq_var alpha alpha'))
        (andb (K.beq_kappa kappa kappa') (beq_tau tau tau'))
   
 | _ , _ => false
end.
Hint Resolve beq_tau.
Definition beq_t := beq_tau.

Lemma beq_tau_refl:
 forall (t : T),
   beq_tau t t = true.
Proof.
  intros.
  induction t; crush.
Qed.
Hint Resolve beq_tau_refl.

(* not quite sure why I have to change the proof structure here at all. *)
Lemma beq_tau_sym : forall x y, beq_tau x y = beq_tau y x.
Proof.
  induction x; induction y; auto.
  try solve [crush].
  try solve [crush].
  try solve [crush].
  try solve [crush].
  unfold beq_tau.
  fold beq_tau.
  rewrite T.beq_var_sym.
  rewrite K.beq_kappa_sym.
  rewrite IHx.
  reflexivity.
  unfold beq_tau.
  fold beq_tau.
  rewrite T.beq_var_sym.
  rewrite P.beq_phi_sym.
  rewrite K.beq_kappa_sym.
  rewrite IHx.
  reflexivity.
Qed.
Hint Immediate beq_tau_sym.

Lemma beq_tau_eq:
  forall t0 t1, beq_tau t0 t1 = true -> t0 = t1.
Proof.
  induction t0; induction t1; intros; try solve [inversion H].

  inversion H.
  apply T.beq_var_eq in H1.
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
  apply T.beq_var_eq in H2.
  apply K.beq_kappa_eq in H3.
  subst.
  reflexivity.

  unfold beq_tau in H.
  fold beq_tau in H.
  apply andb_true_iff in H.
  inversion H.
  apply andb_true_iff in H0.
  inversion H0.
  apply andb_true_iff in H1.
  inversion H1.
  apply IHt0 in H5.
  apply P.beq_phi_eq in H2.
  apply T.beq_var_eq in H3.
  apply K.beq_kappa_eq in H4.
  subst.
  reflexivity.
Qed.
Hint Resolve beq_tau_eq.

Lemma beq_tau_neq:
  forall t0 t1, beq_tau t0 t1 = false -> t0 <> t1.
Proof.
  induction t0; induction t1; intros; try solve [inversion H]; try solve [discriminate].
  apply T.beq_var_neq in H.
  crush.

  unfold beq_tau in H.
  fold beq_tau in H.
  apply andb_false_iff in H.
  destruct H.
  apply IHt0_1 in H.
  crush.
  apply IHt0_2 in H.
  crush.

  unfold beq_tau in H.
  fold beq_tau in H.
  apply andb_false_iff in H.
  destruct H.
  apply IHt0_1 in H.
  crush.
  apply IHt0_2 in H.
  crush.

  unfold beq_tau in H.
  fold beq_tau in H.
  apply IHt0 in H.
  crush.
  
  unfold beq_tau in H.
  fold beq_tau in H.
  apply andb_false_iff in H.
  destruct H.
  apply andb_false_iff in H.
  destruct H.
  apply T.beq_var_neq in H.
  crush.
  apply K.beq_kappa_neq in H.
  crush.
  apply IHt0 in H.
  crush.

  unfold beq_tau in H.
  fold beq_tau in H.
  apply andb_false_iff in H.
  destruct H.
  apply andb_false_iff in H.
  destruct H.
  apply P.beq_phi_neq in H.
  crush.
  apply T.beq_var_neq in H.
  crush.
  apply andb_false_iff in H.
  destruct H.
  apply K.beq_kappa_neq in H.
  crush.
  apply IHt0 in H.
  crush.
Qed.  
Hint Resolve beq_tau_neq.

Lemma beq_tau_trans: 
  forall x y z, 
    beq_tau x y = true -> beq_tau y z = true -> beq_tau x z = true.
Proof.
  intros.
  pose proof H as H'.
  pose proof H0 as H0'.
  apply beq_tau_eq in H.
  apply beq_tau_eq in H0.
  subst.
  assumption.
Qed.
Hint Resolve beq_tau_trans.

Definition beq_t_refl := beq_tau_refl.
Definition beq_t_sym := beq_tau_sym.
Definition beq_t_trans := beq_tau_trans.

Definition beq_t_eq := beq_tau_eq.
Definition beq_t_neq := beq_tau_neq.
End TauModule.
