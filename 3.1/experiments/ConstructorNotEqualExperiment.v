Require Export CpdtTactics.
Require Import Omega.
Require Import Coq.Init.Tactics.

Inductive Foo: Type := 
  | foo : nat -> nat -> Foo.

Lemma test2:
  forall a1 a2 b1 b2, 
    foo a1 a2 <> foo b1 b2
->  (a1 <> b1 \/ a2 <> b2).
Proof.
(*
  intros.
  contradict H.
*)

  intros.
  
Admitted.

Lemma test_foo_intuition:
  forall a1 a2 b1 b2, 
    foo a1 a2 <> foo b1 b2 -> 
    ~(a1 = b1 /\ a2 = b2).
Proof.
  intros.
  intuition.
Qed.

Inductive Bar: Type := 
  | bar : nat -> Bar.

Lemma test1:
  forall a1 b1,
    bar a1 <> bar b1 ->  
    ~(a1 = b1).
Proof.
(* Works.
  intros.
  contradict H.
  rewrite H.
  reflexivity.
*)
(*
  intros.
  induction a1; induction b1; crush.
*)  
  intros.
  intuition.
Qed.

Lemma partial:
  forall a1 a2,
    foo a1 <> foo a2
    -> a1 <> a2.
Proof.
  intros.
  induction a1; induction a2; crush.
Qed.


Theorem not_False :
  not False.
Proof.
  unfold not. intros H. inversion H. Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  intros P H. unfold not. intros G. apply G. apply H. Qed.

Inductive Baz: Type := 
  | baz : nat -> nat -> nat -> Baz.

Lemma test_baz_intuition:
  forall a1 a2 a3 b1 b2 b3, 
    baz a1 a2 a3 <> baz b1 b2 b3 -> 
    ~(a1 = b1 /\ a2 = b2 /\ a3 = b3).
Proof.
  intros.
  intuition.
  subst.
  contradiction H.
  reflexivity.
Qed.

Lemma test_baz_intuition_congruence:
  forall a1 a2 a3 b1 b2 b3, 
    baz a1 a2 a3 <> baz b1 b2 b3 -> 
    ~(a1 = b1 /\ a2 = b2 /\ a3 = b3).
Proof.
  intros.
  intuition.
  congruence.
Qed.