(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Pathing module for the Upsilon context.

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
Require Export CpdtTactics. 
Require Export Case.

Module PathModule <: BooleanEquality.
(* Bug 45, should have made this just zero/one not an i to make the inductions
   work. *)
Module Types.
Inductive IPE: Type :=
 | zero_pe    
 | one_pe.

Inductive PE : Type := 
 | i_pe      : IPE -> PE
 | u_pe      : PE.

Definition Path : Type := list PE.
Definition pdot := [] : Path.
End Types.
Include Types.

Definition t := Path.

Function beq_ipe (i i' : IPE) : bool := 
  match i, i' with
    | zero_pe, zero_pe => true
    | one_pe, one_pe => true
    | _, _ => false
  end.
Hint Resolve beq_ipe.
Hint Unfold beq_ipe.

Lemma beq_ipe_refl:
  forall i, beq_ipe i i = true.
Proof.
  destruct i; crush.
Qed.
Hint Resolve beq_ipe_refl.

Lemma beq_ipe_sym:
  forall i i', beq_ipe i i' = beq_ipe i' i.
Proof.
  destruct i; destruct i'; crush.
Qed.
Hint Immediate beq_ipe_sym.

Lemma beq_ipe_trans:
  forall p p0 p1,
    beq_ipe p p0 = true -> 
    beq_ipe p0 p1 = true ->
    beq_ipe p p1 = true.
Proof.
  induction p; induction p0; induction p1; try solve[crush].
Qed.
Hint Resolve beq_ipe_trans.

Lemma beq_ipe_to_eq:
  forall i i', beq_ipe i i' = true -> i = i'.
Proof.
  destruct i; destruct i'; crush.
Qed.
Hint Immediate beq_ipe_to_eq.

Lemma beq_ipe_to_neq:
  forall i i', beq_ipe i i' = false -> i <> i'.
Proof.
  destruct i; destruct i'; crush.
Qed.
Hint Immediate beq_ipe_to_neq.

Function beq_pe (p p' : PE) : bool :=
  match p, p' with
    | i_pe x, i_pe y => beq_ipe x y
    | u_pe, u_pe => true
    | _, _ => false
  end.
Hint Resolve beq_pe.
Hint Unfold beq_pe.
 
Lemma beq_pe_refl:
  forall p, beq_pe p p = true.
Proof.
  destruct p; crush.
Qed.
Hint Resolve beq_pe_refl.

Lemma beq_pe_sym:
  forall p p', beq_pe p p' = beq_pe p' p.
Proof.
  destruct p; destruct p'; crush.
Qed.
Hint Immediate beq_pe_sym.

Lemma beq_pe_trans:
  forall p p0 p1,
    beq_pe p p0 = true -> 
    beq_pe p0 p1 = true ->
    beq_pe p p1 = true.
Proof.
  induction p; induction p0; induction p1; try solve[crush].
  crush.
  apply beq_ipe_trans with (p:= i) (p0:= i0) (p1:= i1) in H; try assumption.
Qed.
Hint Resolve beq_pe_trans.

Lemma beq_pe_eq:
  forall p p', beq_pe p p' = true -> p = p'.
Proof.
  destruct p; destruct p'; try solve [crush].
  intros.
  unfold beq_pe in H.
  apply beq_ipe_to_eq in H.
  subst.
  reflexivity.
Qed.
Hint Immediate beq_pe_eq.

Lemma beq_pe_neq:
  forall p p', beq_pe p p' = false -> p <> p'.
Proof.
  destruct p; destruct p'; try solve [crush].
  intros.
  unfold beq_pe in H.
  apply beq_ipe_to_neq in H.
  subst.
  crush.
Qed.
Hint Immediate beq_pe_neq.

Function beq_path (p q : Path) : bool := 
  match p, q with
    | [], [] => true
    | x :: p', y :: q' => andb (beq_pe x y) (beq_path p' q')
    | _  , _ => false
  end.
Hint Resolve beq_path.
Hint Unfold beq_path.

Definition eqb := beq_path.


Lemma beq_path_refl:
 forall (p : Path),
   beq_path p p = true.
Proof.
  induction p; crush.
Qed.
Hint Resolve beq_path_refl.
Definition eqb_refl := beq_path_refl.

Lemma beq_path_sym : forall p p', beq_path p p' = beq_path p' p.
Proof.
  induction p; induction p'; try solve[crush].
  unfold beq_path.
  fold beq_path.
  specialize (IHp p').
  rewrite IHp.
  rewrite beq_pe_sym.
  reflexivity.
Qed.
Hint Immediate beq_path_sym.

Lemma beq_path_eq:
  forall p p',
    beq_path p p' = true ->
    p = p'.
Proof.
  induction p; induction p'; try solve [crush].
  unfold beq_path.
  fold beq_path.
  intros.
  apply andb_true_iff in H.
  inversion H.
  apply beq_pe_eq in H0.
  subst.
  apply IHp in H1.
  subst.
  reflexivity.
Qed.
Hint Resolve beq_path_eq.

Lemma beq_path_trans:
  forall p p0 p1,
    beq_path p p0 = true ->
    beq_path p0 p1 = true ->
    beq_path p p1 = true.
Proof.
  intros.
  pose proof H as H'.
  pose proof H0 as H0'.
  apply beq_path_eq in H.
  apply beq_path_eq in H0.
  subst.
  apply beq_path_refl.
Qed.

Lemma beq_path_neq:
  forall p p',
    beq_path p p' = false ->
    p <> p'.
Proof.
  induction p; induction p'; try solve [crush].
  unfold beq_path.
  fold beq_path.
  intros.
  apply andb_false_iff in H.
  inversion H.
  apply beq_pe_neq in H0.
  crush.
  apply IHp in H0.
  crush.
Qed.
Hint Resolve beq_path_eq.

Lemma beq_path_iff_eq:    forall a b, beq_path a b = true <-> a = b.
Proof.
  intros.
  split.
  apply beq_path_eq.
  intros.
  rewrite H.
  apply beq_path_refl.
Qed.
Hint Resolve beq_path_iff_eq.

Lemma beq_path_iff_neq:   forall a b, beq_path a b = false <-> a <> b.
Proof.
  intros.
  split.
  apply beq_path_neq.
  intros.
  induction a; induction b. 
  try solve[crush].
  try solve[crush].
  try solve[crush].
  unfold beq_path.
  fold beq_path.
  apply andb_false_iff.
  (* invert on cons over <> ? *)
Admitted.
Hint Resolve beq_path_iff_neq.

Fixpoint eq (a b : t) : Prop :=
    match beq_path a b with
     | false => False
     | true => True
    end.

Lemma eq_refl:
 forall (a : t),
   eq a a.
Proof.
  induction a;  crush.
  rewrite beq_pe_refl.
  rewrite beq_path_refl.
  simpl.
  trivial.
Qed.

Lemma eq_sym : forall x y : t, eq x y -> eq y x.
Proof.
  destruct x; destruct y; crush.
  rewrite beq_pe_sym.
  rewrite beq_path_sym.
  assumption.
Qed.

Lemma eq_trans : 
  forall x y z,
    eq x y -> eq y z -> eq x z.
Proof.
  destruct x; destruct y; destruct z; crush.
  case_eq(beq_pe p p0); intros; rewrite H1 in *;
  case_eq(beq_path x y); intros; rewrite H2 in *;
  case_eq(beq_pe p0 p1); intros; rewrite H3 in *;
  case_eq(beq_path y z); intros; rewrite H4 in *;
  try solve[inversion H]; try solve[inversion H0].
  apply beq_pe_trans with (p:= p) in H3; try assumption.
  rewrite H3.
  apply beq_path_trans with (p:= x) in H4; try assumption.
  rewrite H4.
  reflexivity.
Qed.

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
  destruct(beq_pe p p0 && beq_path x y); crush.
Qed.

Lemma eqb_eq : forall x y : t, eqb x y = true <-> eq x y.
Proof.
  assert (Z: beq_path = eqb).
  reflexivity.
  destruct x; destruct y;  crush.
  rewrite Z in H.
  destruct( beq_pe p p0 && eqb x y).
  reflexivity.
  inversion H.
Qed.

Lemma eqb_iff_eq:    forall a b, eqb a b = true <-> a = b.
Proof.
  destruct a; destruct b; crush.
Qed.
Hint Resolve eqb_iff_eq.
  
Lemma eqb_iff_neq:   forall a b, eqb a b = false <-> a <> b.
Proof.
  induction a; induction b; try solve[crush].
  unfold eqb.
  unfold beq_path.
  fold beq_path.
Admitted.
Hint Resolve eqb_iff_neq.

Definition eqb_sym := beq_path_sym.
Definition eqb_trans := beq_path_trans.
Definition eqb_to_eq := beq_path_eq.
Definition eqb_to_neq := beq_path_neq.
End PathModule.
