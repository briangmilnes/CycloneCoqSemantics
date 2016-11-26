(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION", Daniel Grossman, August 2003 *)
(* Tactics for LN *)
(* Brian Milnes 2016 *)

Set Implicit Arguments.
Require Export TLC.LibNat TLC.LibVar TLC.LibTactics.
Require Export Cyclone_LN_FSET.

(** Tactics for comparison of indices *)

Hint Extern 1 (_ < _) => nat_math.
Hint Extern 1 (_ <= _) => nat_math.


(* Modules seems to mess with Auto's definitions. *)
Hint Extern 1 (lt _ _) => nat_math.
Hint Extern 1 (le _ _ ) => nat_math.


(* ********************************************************************** *)
(** Tactics *)

(** [inst_notin H y as H'] expects [H] to be of the form
  [forall x, x \notin L, P x] and creates an hypothesis [H']
  of type [P y]. It tries to prove the subgoal [y \notin L]
  by [auto]. This tactic is very useful to apply induction
  hypotheses given in the cases with binders. *)

Tactic Notation "inst_notin" constr(lemma) constr(var)
                "as" ident(hyp_name) :=
  let go L := let Fr := fresh in assert (Fr : var \notin L);
     [ notin_solve | lets hyp_name: (@lemma var Fr); clear Fr ] in
  match type of lemma with
    forall _, _ \notin ?L -> _ => go L end.

Tactic Notation "inst_notin" "~" constr(lemma) constr(var)
                "as" ident(hyp_name) :=
  inst_notin lemma var as hyp_name; auto_tilde.

Tactic Notation "inst_notin" "*" constr(lemma) constr(var)
                "as" ident(hyp_name) :=
  inst_notin lemma var as hyp_name; auto_star.

(* To reduce naming and make the proofs more robust, sometimes you want to
  invert on the constructor equalities or lc terms in the context. *)

Ltac inversion_on_equated_constructors :=
  match goal with
    | H: (?C _) = (?C _) |- _ => inversion H
    | H: (?C _ _) = (?C _ _) |- _ => inversion H
    | H: (?C _ _ _) = (?C _ _ _) |- _ => inversion H                                           
  end.

