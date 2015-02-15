(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  The typing module.

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.
Require Import Coq.Init.Logic.
Require Import Coq.Bool.Bool.

Require Export BoolEqualitySigDef.
Require Export TVarModuleDef.
Require Export KappaModuleDef.
Require Export PhiModuleDef.
Require Export CpdtTactics. 
Require Export Case.
Require Export MoreTacticals.

Module TauModule <: BoolEqualitySig.
Module Base.
 Module TV  := TVarModule. (* So terms can expose it in language module. *)
 Module K := KappaModule.

 Include KappaModule.Base.
 Include PhiModule.

Inductive Tau : Type :=
 | tv_t   : TV.Var -> Tau                             (* A type variable is a type. *)
 | cint   : Tau                                      (* Cyclone's Integers. *)
 | cross  : Tau -> Tau -> Tau                        (* Pairs. *)
 | arrow  : Tau -> Tau -> Tau                        (* Function    type. *)
 | ptype  : Tau -> Tau                               (* Pointer     type. *)
 | utype  : TV.Var -> Kappa -> Tau -> Tau           (* Universal   type. *)
 | etype  : Phi -> TV.Var -> Kappa -> Tau -> Tau. (* Existential type. *)
 
Hint Resolve   beq_kappa_refl.
Hint Immediate beq_kappa_sym.
Hint Resolve   beq_kappa_trans.
Hint Resolve   beq_kappa_eq.
Hint Resolve   beq_kappa_neq.

Hint Resolve   beq_phi_refl.
Hint Immediate beq_phi_sym.
Hint Resolve   beq_phi_trans.
Hint Resolve   beq_phi_eq.
Hint Resolve   beq_phi_neq.

Function beq_tau (t t' : Tau) : bool :=
 match t, t' with
 | tv_t alpha, tv_t beta => TV.beq_t alpha beta
 | cint, cint => true
 | (cross t0 t1), (cross t0' t1') => andb (beq_tau t0 t0') (beq_tau t1 t1')
 | (arrow t0 t1), (arrow t0' t1') => andb (beq_tau t0 t0') (beq_tau t1 t1')
 | ptype t, ptype t' => (beq_tau t t')
(* No alpha conversion for the moment. *)
 | utype alpha kappa tau, utype alpha' kappa' tau' =>
   andb (andb (TV.beq_t alpha alpha') (beq_kappa kappa kappa'))
        (beq_tau tau tau')
 | etype p alpha kappa tau, etype p' alpha' kappa' tau' =>
   andb (andb (beq_phi p p')  (TV.beq_t alpha alpha'))
        (andb (beq_kappa kappa kappa') (beq_tau tau tau'))
   
 | _ , _ => false
end.
Hint Unfold beq_tau.
Hint Resolve beq_tau.

Lemma beq_tau_refl:
 forall (t : Tau),
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
  rewrite TV.beq_t_sym.
  rewrite beq_kappa_sym.
  rewrite IHx.
  reflexivity.
  unfold beq_tau.
  fold beq_tau.
  rewrite TV.beq_t_sym.
  rewrite beq_phi_sym.
  rewrite beq_kappa_sym.
  rewrite IHx.
  reflexivity.
Qed.
Hint Immediate beq_tau_sym.

Lemma beq_tau_eq:
  forall t0 t1, beq_tau t0 t1 = true -> t0 = t1.
Proof.
  induction t0; induction t1; intros; try solve [inversion H].

  inversion H.
  apply TV.beq_t_eq in H1.
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
  apply TV.beq_t_eq in H2.
  apply beq_kappa_eq in H3.
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
  apply beq_phi_eq in H2.
  apply TV.beq_t_eq in H3.
  apply beq_kappa_eq in H4.
  subst.
  reflexivity.
Qed.
Hint Resolve beq_tau_eq.

Lemma beq_tau_neq:
  forall t0 t1, beq_tau t0 t1 = false -> t0 <> t1.
Proof.
  induction t0; induction t1; intros; try solve [inversion H]; try solve [discriminate].
  apply TV.beq_t_neq in H.
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
  apply TV.beq_t_neq in H.
  crush.
  apply beq_kappa_neq in H.
  crush.
  apply IHt0 in H.
  crush.

  unfold beq_tau in H.
  fold beq_tau in H.
  apply andb_false_iff in H.
  destruct H.
  apply andb_false_iff in H.
  destruct H.
  apply beq_phi_neq in H.
  crush.
  apply TV.beq_t_neq in H.
  crush.
  apply andb_false_iff in H.
  destruct H.
  apply beq_kappa_neq in H.
  crush.
  apply IHt0 in H.
  crush.
Qed.  
Hint Resolve beq_tau_neq.


Ltac apply_beq_eqs := 
  repeat match goal with
    | [ I : beq_tau _ _ = true 
        |- _ ] => apply beq_tau_eq in I; subst; try reflexivity
    | [ I : beq_phi _ _ = true 
        |- _ ] => apply beq_phi_eq in I; subst; try reflexivity
    | [ I : beq_kappa _ _ = true 
        |- _ ] => apply beq_kappa_eq in I; subst; try reflexivity
    | [ I : TV.beq_t _ _ = true 
        |- _ ] => apply TV.beq_t_eq in I; subst; try reflexivity
end.

Lemma beq_tau_iff_eq:    forall a b, beq_tau a b = true <-> a = b.
Proof.
  destruct a; destruct b; try solve[crush];
  split;
  intros;
  unfold beq_tau in H;
  fold beq_tau in H;
  simplify_boolean_and_true;
  apply_beq_eqs;
  intros;
  inversion H;
  subst;
  apply beq_tau_refl.
Qed.
Hint Resolve beq_tau_iff_eq.

Ltac fold_n_neq :=
  repeat match goal with
    | [ I : beq_tau ?x ?y = false |- ?x <> ?y  ] => 
      fold beq_tau in I; unfold beq_tau in I; simplify_boolean_and_false
    | [ I : beq_tau ?x _ = false,
        IH: forall _, beq_tau ?x _ = false <-> ?x <> _
       |- _ <> _  ] => 
       apply IH in I; congruence
    | [ H : TV.beq_t _ _ = false |- _ ] =>
      apply TV.beq_t_neq in H; try congruence
    | [ H : beq_kappa _ _ = false |- _ ] =>
      apply beq_kappa_neq in H; try congruence
    | [ H : beq_phi _ _ = false |- _ ] =>
      apply beq_phi_neq in H; try congruence
end.

Lemma beq_tau_iff_neq:   forall a b, beq_tau a b = false <-> a <> b.
Proof.
  induction a; induction b; try split; try intros;
  try solve[congruence];
  try solve[simpl; reflexivity];  try solve[simpl in H; inversion H];
  try solve [unfold beq_tau in H;
             fold beq_tau in H;
             simplify_boolean_and_false;
             try apply beq_tau_neq in H;
             try apply beq_tau_neq in H0;
             congruence];
  try solve[unfold beq_tau in H;
            fold beq_tau in H;
            simplify_boolean_and_false;
            fold_n_neq;
            congruence].
Admitted.
Hint Resolve beq_tau_iff_neq.

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

Function NotFreeInTau (beta : TV.Var) (tau : Tau) : Prop :=
  match tau with 
    | tv_t alpha => 
      if TV.beq_t beta alpha then False else True
    | cint        => True 
    | cross t0 t1 => 
       (NotFreeInTau beta t0) /\ (NotFreeInTau beta t1)
    | arrow t0 t1 => 
        (NotFreeInTau beta t0) /\ (NotFreeInTau beta t1)
    | ptype t     => NotFreeInTau beta t
    | utype alpha _ t =>
      if TV.beq_t beta alpha then True else NotFreeInTau beta t
    | etype _ alpha _ t =>  
      if TV.beq_t beta alpha then True else NotFreeInTau beta t
  end.
End Base.
Include Base.

Definition T := Tau.
Definition beq_t := beq_tau.
Definition beq_t_refl := beq_tau_refl.
Definition beq_t_sym := beq_tau_sym.
Definition beq_t_trans := beq_tau_trans.
Definition beq_t_eq := beq_tau_eq.
Definition beq_t_neq := beq_tau_neq.
Definition beq_t_iff_eq := beq_tau_iff_eq.
Definition beq_t_iff_neq := beq_tau_iff_neq.
End TauModule.
