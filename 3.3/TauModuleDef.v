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
Require Import Coq.Structures.Equalities.

Require Export BoolEqualitySigDef.
Require Export TVarModuleDef.
Require Export KappaModuleDef.
Require Export PhiModuleDef.
Require Export CpdtTactics. 
Require Export Case.
Require Export MoreTacticals.

Module TauModule <: BoolEqualitySig.

Module Types.
 Module TV  := TVarModule. (* So terms can expose it in language module. *)
 Module K := KappaModule.
 Include K.Types.
 Module P := PhiModule.
 Include P.Types.
(* Fix wrt naming issues. *)


Inductive Tau : Type :=
 | tv_t   : TV.Var -> Tau                             (* A type variable is a type. *)
 | cint   : Tau                                      (* Cyclone's Integers. *)
 | cross  : Tau -> Tau -> Tau                        (* Pairs. *)
 | arrow  : Tau -> Tau -> Tau                        (* Function    type. *)
 | ptype  : Tau -> Tau                               (* Pointer     type. *)
 | utype  : TV.Var -> K.Kappa -> Tau -> Tau           (* Universal   type. *)
 | etype  : P.Phi -> TV.Var -> K.Kappa -> Tau -> Tau. (* Existential type. *)
 
End Types.
Include Types.


Function eqb (t t' : Tau) : bool :=
 match t, t' with
 | tv_t alpha, tv_t beta => TV.eqb alpha beta
 | cint, cint => true
 | (cross t0 t1), (cross t0' t1') => andb (eqb t0 t0') (eqb t1 t1')
 | (arrow t0 t1), (arrow t0' t1') => andb (eqb t0 t0') (eqb t1 t1')
 | ptype t, ptype t' => (eqb t t')
(* No alpha conversion for the moment. *)
 | utype alpha kappa tau, utype alpha' kappa' tau' =>
   andb (andb (TV.eqb alpha alpha') (K.eqb kappa kappa'))
        (eqb tau tau')
 | etype p alpha kappa tau, etype p' alpha' kappa' tau' =>
   andb (andb (P.eqb p p')  (TV.eqb alpha alpha'))
        (andb (K.eqb kappa kappa') (eqb tau tau'))
   
 | _ , _ => false
end.
Hint Unfold eqb.
Hint Resolve eqb.

Fixpoint eq (a b : Tau) : Prop :=
    match eqb a b with
     | false => False
     | true => True
    end.

Ltac destruct_away := 
  repeat match goal with
    | [ |- ?X = true ] => destruct X; try solve[inversion H]; try reflexivity
         end.

Lemma eqb_eq : forall x y : Tau, eqb x y = true <-> eq x y.
Proof.
  destruct x; destruct y; crush; destruct_away.
Qed.

Lemma eqb_to_eq:
  forall t0 t1, eqb t0 t1 = true -> t0 = t1.
Proof.
  induction t0; induction t1; intros; try solve [inversion H].

  inversion H.
  apply TV.eqb_to_eq in H1.
  rewrite H1.
  reflexivity.

  reflexivity.

  unfold eqb in H.
  fold eqb in H.
  apply andb_true_iff in H.
  inversion H.
  apply IHt0_1 in H0.
  apply IHt0_2 in H1.
  subst.
  reflexivity.

  unfold eqb in H.
  fold eqb in H.
  apply andb_true_iff in H.
  inversion H.
  apply IHt0_1 in H0.
  apply IHt0_2 in H1.
  subst.
  reflexivity.

  unfold eqb in H.
  fold eqb in H.
  apply IHt0 in H.
  rewrite H.
  reflexivity.

  unfold eqb in H.
  fold eqb in H.
  apply andb_true_iff in H.
  inversion H.
  apply andb_true_iff in H0.
  inversion H0.
  apply IHt0 in H1.
  apply TV.eqb_to_eq in H2.
  apply K.eqb_to_eq in H3.
  subst.
  reflexivity.

  unfold eqb in H.
  fold eqb in H.
  apply andb_true_iff in H.
  inversion H.
  apply andb_true_iff in H0.
  inversion H0.
  apply andb_true_iff in H1.
  inversion H1.
  apply IHt0 in H5.
  apply P.eqb_to_eq in H2.
  apply TV.eqb_to_eq in H3.
  apply K.eqb_to_eq in H4.
  subst.
  reflexivity.
Qed.
Hint Resolve eqb_eq.

Lemma eqb_refl:
 forall (t : Tau),
   eqb t t = true.
Proof.
  intros.
  induction t; crush.
Qed.
Hint Resolve eqb_refl.

Lemma eq_refl:
 forall (a : Tau),
   eq a a.
Proof.
  intros.
  apply eqb_eq.
  apply eqb_refl.
Qed.

Ltac apply_beq_eqs := 
  repeat match goal with
    | [ I : eqb _ _ = true 
        |- _ ] => apply eqb_to_eq in I; subst; try reflexivity
    | [ I : P.eqb _ _ = true 
        |- _ ] => apply P.eqb_to_eq in I; subst; try reflexivity
    | [ I : K.eqb _ _ = true 
        |- _ ] => apply K.eqb_to_eq in I; subst; try reflexivity
    | [ I : TV.eqb _ _ = true 
        |- _ ] => apply TV.eqb_to_eq in I; subst; try reflexivity
end.

Lemma eqb_iff_eq:    forall a b, eqb a b = true <-> a = b.
Proof.
  destruct a; destruct b; try solve[crush];
  split;
  intros;
  unfold eqb in H;
  fold eqb in H;
  simplify_boolean_and_true;
  apply_beq_eqs;
  intros;
  inversion H;
  subst;
  apply eqb_refl.
Qed.
Hint Resolve eqb_iff_eq.

(* not quite sure why I have to change the proof structure here at all. *)
Lemma eqb_sym : forall x y, eqb x y = eqb y x.
Proof.
  induction x; induction y; auto.
  try solve [crush].
  try solve [crush].
  try solve [crush].
  try solve [crush].
  unfold eqb.
  fold eqb.
  rewrite TV.eqb_sym.
  rewrite K.eqb_sym.
  rewrite IHx.
  reflexivity.
  unfold eqb.
  fold eqb.
  rewrite TV.eqb_sym.
  rewrite P.eqb_sym.
  rewrite K.eqb_sym.
  rewrite IHx.
  reflexivity.
Qed.
Hint Immediate eqb_sym.

Lemma eq_sym : forall x y : Tau, eq x y -> eq y x.
Proof.
  intros.
  apply eqb_eq.
  apply eqb_eq in H.
  rewrite eqb_sym.
  assumption.
Qed.

Lemma eqb_to_neq:
  forall t0 t1, eqb t0 t1 = false -> t0 <> t1.
Proof.
  induction t0; induction t1; intros; try solve [inversion H]; try solve [discriminate].
  apply TV.eqb_to_neq in H.
  crush.

  unfold eqb in H.
  fold eqb in H.
  apply andb_false_iff in H.
  destruct H.
  apply IHt0_1 in H.
  crush.
  apply IHt0_2 in H.
  crush.

  unfold eqb in H.
  fold eqb in H.
  apply andb_false_iff in H.
  destruct H.
  apply IHt0_1 in H.
  crush.
  apply IHt0_2 in H.
  crush.

  unfold eqb in H.
  fold eqb in H.
  apply IHt0 in H.
  crush.
  
  unfold eqb in H.
  fold eqb in H.
  apply andb_false_iff in H.
  destruct H.
  apply andb_false_iff in H.
  destruct H.
  apply TV.eqb_to_neq in H.
  crush.
  apply K.eqb_to_neq in H.
  crush.
  apply IHt0 in H.
  crush.

  unfold eqb in H.
  fold eqb in H.
  apply andb_false_iff in H.
  destruct H.
  apply andb_false_iff in H.
  destruct H.
  apply P.eqb_to_neq in H.
  crush.
  apply TV.eqb_to_neq in H.
  crush.
  apply andb_false_iff in H.
  destruct H.
  apply K.eqb_to_neq in H.
  crush.
  apply IHt0 in H.
  crush.
Qed.  
Hint Resolve eqb_to_neq.

Ltac fold_n_neq :=
  repeat match goal with
    | [ I : eqb ?x ?y = false |- ?x <> ?y  ] => 
      fold eqb in I; unfold eqb in I; simplify_boolean_and_false
    | [ I : eqb ?x _ = false,
        IH: forall _, eqb ?x _ = false <-> ?x <> _
       |- _ <> _  ] => 
       apply IH in I; congruence
    | [ H : TV.eqb _ _ = false |- _ ] =>
      apply TV.eqb_to_neq in H; try congruence
    | [ H : K.eqb _ _ = false |- _ ] =>
      apply K.eqb_to_neq in H; try congruence
    | [ H : P.eqb _ _ = false |- _ ] =>
      apply P.eqb_to_neq in H; try congruence
end.

Lemma eqb_iff_neq:   forall a b, eqb a b = false <-> a <> b.
Proof.
  induction a; induction b; try split; try intros;
  try solve[congruence];
  try solve[simpl; reflexivity];  try solve[simpl in H; inversion H];
  try solve [unfold eqb in H;
             fold eqb in H;
             simplify_boolean_and_false;
             try apply eqb_to_neq in H;
             try apply eqb_to_neq in H0;
             congruence];
  try solve[unfold eqb in H;
            fold eqb in H;
            simplify_boolean_and_false;
            fold_n_neq;
            congruence].
Admitted.
Hint Resolve eqb_iff_neq.

Lemma eqb_trans: 
  forall x y z, 
    eqb x y = true -> eqb y z = true -> eqb x z = true.
Proof.
  intros.
  pose proof H as H'.
  pose proof H0 as H0'.
  apply eqb_to_eq in H.
  apply eqb_to_eq in H0.
  subst.
  assumption.
Qed.
Hint Resolve eqb_trans.

Lemma eq_trans : 
  forall x y z,
    eq x y -> eq y z -> eq x z.
Proof.
  intros.
  apply eqb_eq in H.
  apply eqb_eq in H0.
  apply eqb_eq.
  apply eqb_trans with (x:= x) (y:= y) (z:= z); try assumption.
Qed.

Function NotFreeInTau (beta : TV.Var) (tau : Tau) : Prop :=
  match tau with 
    | tv_t alpha => 
      if TV.eqb beta alpha then False else True
    | cint        => True 
    | cross t0 t1 => 
       (NotFreeInTau beta t0) /\ (NotFreeInTau beta t1)
    | arrow t0 t1 => 
        (NotFreeInTau beta t0) /\ (NotFreeInTau beta t1)
    | ptype t     => NotFreeInTau beta t
    | utype alpha _ t =>
      if TV.eqb beta alpha then True else NotFreeInTau beta t
    | etype _ alpha _ t =>  
      if TV.eqb beta alpha then True else NotFreeInTau beta t
  end.

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

Lemma eq_dec : forall x y : Tau, {eq x y} + {~ eq x y}.
Proof.   
  intros.
  induction x; induction y; unfold eq; destruct_evidence.
Qed.

Definition t:= Tau.

End TauModule.
