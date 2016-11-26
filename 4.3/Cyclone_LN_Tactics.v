(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION", Daniel Grossman, August 2003 *)
(* Tactics for LN *)
(* Brian Milnes 2016 *)

Set Implicit Arguments.
Require Export TLC.LibNat TLC.LibVar TLC.LibTactics.
Require Export Cyclone_LN_FSET Cyclone_LN_Terms Cyclone_LN_Types Cyclone_LN_Types_In_Terms.

(** Tactics for comparison of indices *)

Hint Extern 1 (_ < _) => nat_math.
Hint Extern 1 (_ <= _) => nat_math.


(* Modules seems to mess with Auto's definitions. *)
Hint Extern 1 (lt _ _) => nat_math.
Hint Extern 1 (le _ _ ) => nat_math.


(* Tactics for variables. *)

(* Tactics for building L, our finite set for cofinite induction. *)

Ltac gather_vars :=
  let A' := gather_vars_with (fun x : vars => x) in
  let B' := gather_vars_with (fun x : var  => \{x}) in
  let C' := gather_vars_with (fun x : Tau => T.fv x) in
  let D' := gather_vars_with (fun x : V => TM.fv_v x) in
  let E' := gather_vars_with (fun x : St => TM.fv_st x) in
  let F' := gather_vars_with (fun x : E => TM.fv_e x) in
  let G' := gather_vars_with (fun x : F => TM.fv_f x) in  
  let H' := gather_vars_with (fun x : Term => TM.fv x) in
  let I' := gather_vars_with (fun x : St => TTM.fv_st x) in
  let J' := gather_vars_with (fun x : E => TTM.fv_e x) in
  let K' := gather_vars_with (fun x : F => TTM.fv_f x) in
  let L' := gather_vars_with (fun x : Term => TTM.fv x) in
  constr:(A' \u (B' \u (C' \u D' \u E' \u F' \u G' \u H' \u I' \u J'
            \u K' \u L'))).

Ltac pick_fresh X :=
  let L := gather_vars in (pick_fresh_gen L X).

Tactic Notation "pick_fresh" ident(x) :=
  let L := gather_vars in pick_fresh_gen (L) x.

Tactic Notation "pick_fresh" ident(x) "from" constr(E) :=
  let L := gather_vars in pick_fresh_gen (L \u E) x.

Tactic Notation "apply_fresh" constr(T) :=
  apply_fresh_base T gather_vars ltac_no_arg.

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; auto_star.

Tactic Notation "apply_fresh" "*" constr(T) :=
  apply_fresh T; auto_star.

Tactic Notation "exists_fresh" :=
  let y := fresh "y" in let Fry := fresh "Fr" y in
  exists_fresh_gen gather_vars y Fry.

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

Hint Resolve subset_union_weak_l subset_union_weak_r subset_refl
  subset_union_2 subset_union_2p subset_empty_l 
  subset_remove_2p subset_remove_11 : fset.
