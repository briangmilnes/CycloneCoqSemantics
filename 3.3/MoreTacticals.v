(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Tacticals to apply for rewriting and beq_t_eq/beq_t_neq now
 that we are modularized.

*)

Set Implicit Arguments.
Require Export List.
Export ListNotations.
Require Export ZArith.
Require Export Init.Datatypes.
Require Import Coq.Bool.Bool.
Require Import Coq.Setoids.Setoid.

(* Learn to handle beq eq and neqs. *)
Ltac simplify_boolean_and_true:=
  repeat match goal with
    | [ H : andb _ _ = true |- _ ] => apply Bool.andb_true_iff in H
    | [ H : (_ = true) /\ (_ = true) |- _ ] => try inversion H; clear H
    | [ H : (_ && _ = true)  /\ (_ && _ = true) |- _ ] => try inversion H; clear H
end.

Ltac simplify_boolean_and_false:=
  repeat match goal with
    | [ H : andb _ _ = false |- _ ] => apply Bool.andb_false_iff in H
    | [ H : (_ = false) \/ (_ = false) |- _ ] => try inversion H; clear H
    | [ H :(_ && _ = false)  /\ (_ && _ = false) |- _ ] => try inversion H; clear H
end.

Ltac refold f      := unfold f; fold f.
Ltac refold_in f H := unfold f in H; fold f in H.
