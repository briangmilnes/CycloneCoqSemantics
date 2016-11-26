(* Adapt nat paths in the TLC style. *)

Set Implicit Arguments.
Require Import TLC.LibTactics TLC.LibReflect TLC.LibBool TLC.LibOperation TLC.LibRelation TLC.LibOrder  TLC.LibNat.


(* ********************************************************************** *)
(** * Inhabited and comparable *)

Definition path := list nat.
Instance path_inhab : Inhab path.
Proof using. intros. apply (prove_Inhab (cons 0 nil)). Qed.

Fixpoint path_compare (x y : path) :=
  match x, y with
    | nil, nil => true
    | (cons _ _), nil => false
    | nil, (cons _ _) => false
    | (cons a x'), (cons b y') =>
      If a = b (* The trick is to USE equality at each step! *)
      then path_compare x' y'
      else false
  end.

(* And this proves equality is valid in classical logic! *)
Instance path_comparable : Comparable path.
Proof using.
  applys (comparable_beq path_compare).
  induction x; destruct y; simpl; autos*; auto_false.
  destruct (classicT (a = n));  split; intros; try solve[inversion H].
  apply IHx in H.
  subst.
  reflexivity.
  inversion H; subst.
  apply IHx.
  reflexivity.
  inversion H.
  contradiction.
Qed.

