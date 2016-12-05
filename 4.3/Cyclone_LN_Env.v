(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION".   Daniel Grossman, August 2003 *)
(* This is all of the LN infrastructure packed in a module for types. *)
(* Brian Milnes 2016 *)

Set Implicit Arguments.
Require Export Cyclone_Formal_Syntax Cyclone_LN_Types Cyclone_LN_Terms Cyclone_LN_Types_In_Terms.
Require Export TLC.LibEnv TLC.LibList.
Close Scope list_scope.
Import LibEnvNotations.
Import LVPE.LibVarPathEnvNotations.

Function fv_heap (h : Heap) : vars :=
    dom h \u fv_in_values (fun (e : E) => TTM.fv_e e \u TM.fv_e e) h.

Function fv_state (s : State) :=
  match s with
    | (h,st) => fv_heap h \u TM.fv_st st \u TTM.fv_st st
  end.

Function fv_delta   (d : Delta)   : vars := dom d.
Function fv_gamma   (g : Gamma)   : vars :=
  dom g \u fv_in_values (fun (t : Tau) => T.fv t) g.

Function fv_upsilon (u : Upsilon) : vars := 
  LVPE.fv_in_keys (fun (xp : varpath) => \{fst xp}) u \u
  LVPE.fv_in_values (fun (t : Tau) => T.fv t) u.

(* Now we need lemmas to simplify the abstract versions of these. *)
(*
Lemma values_empty:
  values hdot = nil.
(*
Proof.
  compute.
  unfold values.
*)
Admitted.

Lemma fv_in_values_empty:
  forall f, fv_in_values f hdot = \{}.
(*
Proof.
  intros.
  unfold fv_in_values.
*)  

Lemma fv_heap_empty:
  fv_heap hdot = \{}.
Proof.
  unfold fv_heap.
  unfold hdot.
  rewrite dom_empty.

  unfold fv_in_values.
  simpl.
 *)

(* This works but is slow. *)
(*
Ltac simpl_get :=
  auto; autounfold; autorewrite with env_defs; intros; auto; try unfold get_impl;
   try unfold LVPE.V.get_impl; simpl; try case_var~.
*)

Ltac simpl_env :=
  match goal with 
  | |- context [get ?a ddot]           => rewrite~ get_empty
  | |- context [get ?a gdot]           => rewrite~ get_empty
  | |- context [get ?a hdot]           => rewrite~ get_empty
  | |- context [LVPE.V.get ?a udot]    => rewrite~ LVPE.get_empty

  | |- context [LVPE.V.get ?a (?a ~p _) ]      =>
    rewrite~ LVPE.get_single; try repeat case_var~; simpl_env
  | |- context [get ?a (?a ~ _) ]      =>
    rewrite~ get_single; try repeat case_var~; simpl_env

  | |- context [LVPE.V.get ?a (_ &p (?a ~p _)) ]      =>
    rewrite~ LVPE.get_push; try repeat case_var~; simpl_env
  | |- context [get ?a (_ & (?a ~ _)) ]      =>
    rewrite~ get_push; simpl_env; try repeat case_var~

  | |- context [LVPE.V.get ?a (_ &p (_ ~p _)) ]      =>
    rewrite~ LVPE.get_push; try repeat case_var~; simpl_env
  | |- context [get ?a (_ & (_ ~ _)) ]      =>
    rewrite~ get_push; try repeat case_var~; simpl_env

  | |- context [get ?a ((?b ~ _) & _)] =>
    rewrite~ get_concat; try repeat case_var~; simpl_env
  | |- context [LVPE.V.get ?a ((?b ~ _) & _)] =>
    rewrite~ LVPE.get_concat; try repeat case_var~; simpl_env

  | |- context [?a \u \{}] =>
    repeat rewrite union_empty_l.
  end.

Hint Extern 4 (get _ _ = _) => simpl_env.
