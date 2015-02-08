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
  Module K := KappaModule.
  Module P := PhiModule.
  Module T := TVarModule.

Hint Resolve   K.beq_t_refl.
Hint Immediate K.beq_t_sym.
Hint Resolve   K.beq_t_trans.
Hint Resolve   K.beq_t_eq.
Hint Resolve   K.beq_t_neq.

Hint Resolve   P.beq_t_refl.
Hint Immediate P.beq_t_sym.
Hint Resolve   P.beq_t_trans.
Hint Resolve   P.beq_t_eq.
Hint Resolve   P.beq_t_neq.

Inductive Tau : Type :=
 | tv_t   : T.Var -> Tau                             (* A type variable is a type. *)
 | cint   : Tau                                      (* Cyclone's Integers. *)
 | cross  : Tau -> Tau -> Tau                        (* Pairs. *)
 | arrow  : Tau -> Tau -> Tau                        (* Function    type. *)
 | ptype  : Tau -> Tau                               (* Pointer     type. *)
 | utype  : T.Var -> K.Kappa -> Tau -> Tau           (* Universal   type. *)
 | etype  : P.Phi -> T.Var -> K.Kappa -> Tau -> Tau. (* Existential type. *)

Definition T := Tau.

Function beq_t (t t' : T) : bool :=
 match t, t' with
 | tv_t alpha, tv_t beta => T.beq_t alpha beta
 | cint, cint => true
 | (cross t0 t1), (cross t0' t1') => andb (beq_t t0 t0') (beq_t t1 t1')
 | (arrow t0 t1), (arrow t0' t1') => andb (beq_t t0 t0') (beq_t t1 t1')
 | ptype t, ptype t' => (beq_t t t')
(* No alpha conversion for the moment. *)
 | utype alpha kappa tau, utype alpha' kappa' tau' =>
   andb (andb (T.beq_t alpha alpha') (K.beq_t kappa kappa'))
        (beq_t tau tau')
 | etype p alpha kappa tau, etype p' alpha' kappa' tau' =>
   andb (andb (P.beq_t p p')  (T.beq_t alpha alpha'))
        (andb (K.beq_t kappa kappa') (beq_t tau tau'))
   
 | _ , _ => false
end.
Hint Unfold beq_t.
Hint Resolve beq_t.

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
  fold beq_t.
  rewrite T.beq_t_sym.
  rewrite K.beq_t_sym.
  rewrite IHx.
  reflexivity.
  unfold beq_t.
  fold beq_t.
  rewrite T.beq_t_sym.
  rewrite P.beq_t_sym.
  rewrite K.beq_t_sym.
  rewrite IHx.
  reflexivity.
Qed.
Hint Immediate beq_t_sym.

Lemma beq_t_eq:
  forall t0 t1, beq_t t0 t1 = true -> t0 = t1.
Proof.
  induction t0; induction t1; intros; try solve [inversion H].

  inversion H.
  apply T.beq_t_eq in H1.
  rewrite H1.
  reflexivity.

  reflexivity.

  unfold beq_t in H.
  fold beq_t in H.
  apply andb_true_iff in H.
  inversion H.
  apply IHt0_1 in H0.
  apply IHt0_2 in H1.
  subst.
  reflexivity.

  unfold beq_t in H.
  fold beq_t in H.
  apply andb_true_iff in H.
  inversion H.
  apply IHt0_1 in H0.
  apply IHt0_2 in H1.
  subst.
  reflexivity.

  unfold beq_t in H.
  fold beq_t in H.
  apply IHt0 in H.
  rewrite H.
  reflexivity.

  unfold beq_t in H.
  fold beq_t in H.
  apply andb_true_iff in H.
  inversion H.
  apply andb_true_iff in H0.
  inversion H0.
  apply IHt0 in H1.
  apply T.beq_t_eq in H2.
  apply K.beq_t_eq in H3.
  subst.
  reflexivity.

  unfold beq_t in H.
  fold beq_t in H.
  apply andb_true_iff in H.
  inversion H.
  apply andb_true_iff in H0.
  inversion H0.
  apply andb_true_iff in H1.
  inversion H1.
  apply IHt0 in H5.
  apply P.beq_t_eq in H2.
  apply T.beq_t_eq in H3.
  apply K.beq_t_eq in H4.
  subst.
  reflexivity.
Qed.
Hint Resolve beq_t_eq.

Lemma beq_t_neq:
  forall t0 t1, beq_t t0 t1 = false -> t0 <> t1.
Proof.
  induction t0; induction t1; intros; try solve [inversion H]; try solve [discriminate].
  apply T.beq_t_neq in H.
  crush.

  unfold beq_t in H.
  fold beq_t in H.
  apply andb_false_iff in H.
  destruct H.
  apply IHt0_1 in H.
  crush.
  apply IHt0_2 in H.
  crush.

  unfold beq_t in H.
  fold beq_t in H.
  apply andb_false_iff in H.
  destruct H.
  apply IHt0_1 in H.
  crush.
  apply IHt0_2 in H.
  crush.

  unfold beq_t in H.
  fold beq_t in H.
  apply IHt0 in H.
  crush.
  
  unfold beq_t in H.
  fold beq_t in H.
  apply andb_false_iff in H.
  destruct H.
  apply andb_false_iff in H.
  destruct H.
  apply T.beq_t_neq in H.
  crush.
  apply K.beq_t_neq in H.
  crush.
  apply IHt0 in H.
  crush.

  unfold beq_t in H.
  fold beq_t in H.
  apply andb_false_iff in H.
  destruct H.
  apply andb_false_iff in H.
  destruct H.
  apply P.beq_t_neq in H.
  crush.
  apply T.beq_t_neq in H.
  crush.
  apply andb_false_iff in H.
  destruct H.
  apply K.beq_t_neq in H.
  crush.
  apply IHt0 in H.
  crush.
Qed.  
Hint Resolve beq_t_neq.


Ltac apply_beq_eqs := 
  repeat match goal with
    | [ I : beq_t _ _ = true 
        |- _ ] => apply beq_t_eq in I; subst; try reflexivity
    | [ I : P.beq_t _ _ = true 
        |- _ ] => apply P.beq_t_eq in I; subst; try reflexivity
    | [ I : K.beq_t _ _ = true 
        |- _ ] => apply K.beq_t_eq in I; subst; try reflexivity
    | [ I : T.beq_t _ _ = true 
        |- _ ] => apply T.beq_t_eq in I; subst; try reflexivity
end.

Lemma beq_t_iff_eq:    forall a b, beq_t a b = true <-> a = b.
Proof.
  destruct a; destruct b; try solve[crush];
  split;
  intros;
  unfold beq_t in H;
  fold beq_t in H;
  simplify_boolean_and_true;
  apply_beq_eqs;
  intros;
  inversion H;
  subst;
  apply beq_t_refl.
Qed.
Hint Resolve beq_t_iff_eq.

Ltac fold_n_neq :=
  repeat match goal with
    | [ I : beq_t ?x ?y = false |- ?x <> ?y  ] => 
      fold beq_t in I; unfold beq_t in I; simplify_boolean_and_false
    | [ I : beq_t ?x _ = false,
        IH: forall _, beq_t ?x _ = false <-> ?x <> _
       |- _ <> _  ] => 
       apply IH in I; congruence
    | [ H : T.beq_t _ _ = false |- _ ] =>
      apply T.beq_t_neq in H; try congruence
    | [ H : P.beq_t _ _ = false |- _ ] =>
      apply P.beq_t_neq in H; try congruence
    | [ H : K.beq_t _ _ = false |- _ ] =>
      apply K.beq_t_neq in H; try congruence
end.

Lemma beq_t_iff_neq:   forall a b, beq_t a b = false <-> a <> b.
Proof.
  induction a; induction b; try split; try intros;
 try solve[congruence];
  try solve[simpl; reflexivity];  try solve[simpl in H; inversion H];
  try solve [unfold beq_t in H;
             fold beq_t in H;
             simplify_boolean_and_false;
             try apply beq_t_neq in H;
             try apply beq_t_neq in H0;
             congruence];
  try solve[unfold beq_t in H;
            fold beq_t in H;
            simplify_boolean_and_false;
            fold_n_neq;
            congruence].
Admitted.
Hint Resolve beq_t_iff_neq.

Lemma beq_t_trans: 
  forall x y z, 
    beq_t x y = true -> beq_t y z = true -> beq_t x z = true.
Proof.
  intros.
  pose proof H as H'.
  pose proof H0 as H0'.
  apply beq_t_eq in H.
  apply beq_t_eq in H0.
  subst.
  assumption.
Qed.
Hint Resolve beq_t_trans.

Function NotFreeInTau (beta : T.Var) (tau : Tau) : Prop :=
  match tau with 
    | tv_t alpha => 
      if T.beq_t beta alpha then False else True
    | cint        => True 
    | cross t0 t1 => 
       (NotFreeInTau beta t0) /\ (NotFreeInTau beta t1)
    | arrow t0 t1 => 
        (NotFreeInTau beta t0) /\ (NotFreeInTau beta t1)
    | ptype t     => NotFreeInTau beta t
    | utype alpha _ t =>
      if T.beq_t beta alpha then True else NotFreeInTau beta t
    | etype _ alpha _ t =>  
      if T.beq_t beta alpha then True else NotFreeInTau beta t
  end.

End TauModule.
