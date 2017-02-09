(* An experiment to see if I can prove the X -> ok -> Value style proofs once. *)
(* Brian Milnes 2016 *)

Set Implicit Arguments.
Require Export TLC.LibEnv.
Require Export Cyclone_Admit_Environment.
Import LibEnvNotations. (* A, I had to put the notations in a module. *)

Section Test.
Variable A : Type.

Set Printing Universes.
Check Prop.
Check Set.
Check Type.

(* Why can't I pass a prop in? 
Inductive OKP : (A -> Prop) -> env A -> Prop :=
 | OKP_empty : forall P, (@ok A) empty -> OKP P empty
 | OKP_push  : forall E x v P,
     ok (E & x ~ v) ->
     P v ->
     OKP P (E & x ~ v).

 *)

(* Why does this work ? *)
Inductive OKP (A : Type) (P: env A -> var -> A -> Prop) : env A -> Prop :=
 | OKP_empty : (@ok A) empty -> OKP P empty
 | OKP_push  : forall E x v,
     ok (E & x ~ v) ->
     P E x v ->
     OKP P (E & x ~ v).

Inductive V : Type :=
 | bevar      : nat -> V  
 | fevar      : var -> V. 

Inductive Value : V -> Prop :=
 | V_fevar : forall n,  Value (fevar n).

Function vw (A : Type) (y : A -> Prop) (E : env A) (x : var) (a : A) := (y a).
Definition OKV := OKP (vw Value).

Theorem OKP_Value__ok:
  forall E,
    OKV E ->
    ok E.
Proof.
  intros E.
  induction E using env_ind; auto; intros.
  inversion H; auto.
Qed.

Theorem OKP_Value__Value:
  forall E x v, 
    OKV (E & x ~ v) ->
    Value v.
Proof.
  intros E x v OKVd.
  inversion OKVd.
  apply empty_not_constructed in H.
  inversion H.
  apply eq_inversion_env in H.
  inversion H.
  inversion H3.
  subst*.
Qed.

(* Need a get version. *)

Theorem OKP_P__P:
  forall (A : Type) E x v P,
    (@OKP A P (E & x ~ v)) ->
    P E x v.
Proof.
  intros.
  inversion H.
  apply empty_not_constructed in H0.
  inversion H0.
  apply eq_inversion_env in H0.
  inversion H0.
  inversion H4.
  subst*.
Qed.

Theorem OKP_Value__Value':
  forall E x v, 
    OKV (E & x ~ v) ->
    Value v.
Proof.
  intros E x v OKVd.
  apply OKP_P__P in OKVd; auto.
Qed.

(* This is interesting but not clear how many lemmas it really saves me. *)