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
Require Export CpdtTactics. 
Require Export Case.
Require Export TacticNotations.

Module PathModule <: BoolEqualitySig.
  Module E := EVarModule.

Inductive IPE: Type :=
 | zero_pe    
 | one_pe.

Inductive PE : Type := 
 | i_pe      : IPE -> PE
 | u_pe      : PE.

Definition P : Type := list PE.
Definition T := P.
 
Function beq_ipe (i i' : IPE) : bool := 
  match i, i' with
    | zero_pe, zero_pe => true
    | one_pe, one_pe => true
    | _, _ => false
  end.
Hint Resolve beq_ipe.

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

Lemma beq_ipe_eq:
  forall i i', beq_ipe i i' = true -> i = i'.
Proof.
  destruct i; destruct i'; crush.
Qed.
Hint Immediate beq_ipe_eq.

Lemma beq_ipe_neq:
  forall i i', beq_ipe i i' = false -> i <> i'.
Proof.
  destruct i; destruct i'; crush.
Qed.
Hint Immediate beq_ipe_neq.

Function beq_pe (p p' : PE) : bool :=
  match p, p' with
    | i_pe x, i_pe y => beq_ipe x y
    | u_pe, u_pe => true
    | _, _ => false
  end.
Hint Resolve beq_pe.
 
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
  apply beq_ipe_eq in H.
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
  apply beq_ipe_neq in H.
  subst.
  crush.
Qed.
Hint Immediate beq_pe_neq.

Function beq_path (p q : P) : bool := 
  match p, q with
    | [], [] => true
    | x :: p', y :: q' => andb (beq_pe x y) (beq_path p' q')
    | _  , _ => false
  end.
Hint Resolve beq_pe.
Definition beq_t := beq_path.

Lemma beq_path_refl:
 forall (p : P),
   beq_path p p = true.
Proof.
  induction p; crush.
Qed.
Hint Resolve beq_path_refl.

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

Definition beq_t_refl := beq_path_refl.
Definition beq_t_sym := beq_path_sym.
Definition beq_t_trans := beq_path_trans.

Definition beq_t_eq := beq_path_eq.
Definition beq_t_neq := beq_path_neq.
End PathModule.
