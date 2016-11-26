(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION".   Daniel Grossman, August 2003 *)
(* FSet infrastructure from Lambda_JAR paper. *)
(* Brian Milnes 2016 *)

Set Implicit Arguments.
Require Import TLC.LibLN TLC.LibNat.

(** Tactics for equalities between sets *)

Lemma subset_union_2p : forall E1 E2 F1 F2 G : vars,
  E1 \c (F1 \u G) -> E2 \c (F2 \u G) -> (E1 \u E2) \c ((F1 \u F2) \u G).
Proof.
  introv H1 H2. intros x. specializes H1 x. specializes H2 x.
  repeat rewrite in_union in *.
  auto_star.
Qed.

Lemma subset_remove_11 : forall x y : var, 
  x <> y -> \{x} \c (\{x} \- \{y}).
Proof.
  introv H. intros z M. rewrite in_singleton in M. subst.
  rewrite in_remove. split. rewrite~ in_singleton. auto.
Qed.

Lemma subset_remove_2p : forall E1 E2 F1 F2 G : vars,
  E1 \c (F1 \- G) -> E2 \c (F2 \- G) -> (E1 \u E2) \c ((F1 \u F2) \- G).
Proof. introv H1 H2. forwards: subset_union_2 H1 H2. rewrite~ union_remove. Qed.

Hint Resolve subset_union_weak_l subset_union_weak_r subset_refl
  subset_union_2 subset_union_2p subset_empty_l 
  subset_remove_2p subset_remove_11 : fset.

Ltac fset := first [ auto with fset ].