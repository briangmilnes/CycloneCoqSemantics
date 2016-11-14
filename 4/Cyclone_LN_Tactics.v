(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION", Daniel Grossman, August 2003 *)
(* Tactics for LN *)
(* Brian Milnes 2016 *)

Set Implicit Arguments.
Require Export Cyclone_Formal_Syntax LibVarPathEnv Cyclone_LN_FV.

(* Tactics for building L, our finite set for cofinite induction. *)

Ltac gather_vars :=
  let A' := gather_vars_with (fun x : vars => x) in
  let B' := gather_vars_with (fun x : var  => \{x}) in
  let C' := gather_vars_with (fun x : Tau => ftyv_tau x) in
  let D' := gather_vars_with (fun x : V => fv_v x) in
  let E' := gather_vars_with (fun x : St => fv_st x) in
  let F' := gather_vars_with (fun x : E => fv_e x) in
  let G' := gather_vars_with (fun x : F => fv_f x) in  
  let H' := gather_vars_with (fun x : Term => fv_term x) in
  let I' := gather_vars_with (fun x : St => ftyv_st x) in
  let J' := gather_vars_with (fun x : E => ftyv_e x) in
  let K' := gather_vars_with (fun x : F => ftyv_f x) in
  let L' := gather_vars_with (fun x : Term => ftyv_term x) in
  let M' := gather_vars_with (fun x : Upsilon => fv_upsilon x) in
  let N' := gather_vars_with (fun x : Heap => fv_heap x) in
  let O' := gather_vars_with (fun x : Delta => ftyv_delta x) in
  let P' := gather_vars_with (fun x : Gamma => fv_gamma x) in
  let Q' := gather_vars_with (fun x : State => fv_state x) in
  constr:(A' \u B' \u C' \u D' \u E' \u F' \u G' \u H' \u I' \u J'
            \u K' \u L' \u M' \u N' \u O' \u P' \u Q').

Ltac pick_fresh X :=
  let L := gather_vars in (pick_fresh_gen L X).

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; auto_star.

Hint Constructors Term.

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

