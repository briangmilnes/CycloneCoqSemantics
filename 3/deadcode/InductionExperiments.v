(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

 Just messing around with experiments on inductions.

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.
Require Import Coq.Init.Logic.

(*
Inductive tree : Prop :=
  | empty  : tree
  | leaf : bool -> tree
  | branch : tree -> tree -> tree.

Print tree.
Print tree_ind.

Lemma foo:
  forall (t : tree),
    True.
Proof.
  intros.
  apply (tree_ind
           (fun (t : tree) => True)).
  admit.
  admit.
  admit.
  
(*
  induction t.
  admit.
  admit.
*)

*)

Inductive step : nat -> nat -> Prop :=
  | step_equal : forall (n : nat),
                   step n n.

Print step_ind.

Lemma step_n_n:
  forall (n m: nat),
    step n m ->
    step n (S m).
Proof.
  intros n m stepder.
  induction stepder.
Admitted.  