(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION".   Daniel Grossman, August 2003 *)
(* Lemmas for WFC  *)
(* Brian Milnes 2016 *)
Set Implicit Arguments.
Require Export Cyclone_Formal_Syntax Cyclone_Static_Semantics_Kinding_And_Context_Well_Formedness.
Require Export Cyclone_Static_Semantics_Typing_Heap_Objects.
Require Export Cyclone_Classes Cyclone_Inductions Cyclone_LN_Tactics Cyclone_LN_Extra_Lemmas_And_Automation.
Close Scope list_scope.
Import LibEnvNotations.
Import LVPE.LibVarPathEnvNotations.

Lemma WFU_ok_upsilon:
  forall u,
    WFU u ->
    LVPE.okp u.
Proof.
  intros.
  inversion H.
  constructor.
  constructor.
  assumption.
  apply LVPE.get_none_inv.
  assumption.
Qed.

Ltac WFU_ok_upsilon :=
  match goal with
    | H : WFU ?u |- LVPE.okp ?u => apply WFU_ok_upsilon
  end.
Hint Extern 1 (LVPE.okp _) => try WFU_ok_upsilon.

Lemma WFU_K:
  forall u xp tau,
   WFU (u &p xp ~p tau) ->
   K empty tau A.
Proof.
  introv WFUd.
  induction u.
  inversion WFUd.
  apply LVPE.empty_push_inv in H0.
  inversion H0.
  rewrite <- LVPE.V.empty_def in H.
  apply LVPE.eq_push_inv in H.
  inversion H.
  inversion H5.
  subst.
  assumption.
  inversion WFUd.
  apply LVPE.empty_push_inv in H0.
  inversion H0.
  apply LVPE.eq_push_inv in H.
  inversion H.
  inversion H5.
  subst.
  assumption.
Qed.
Ltac WFU_K := 
  match goal with
    | H : WFU (?u' &p ?xp' ~p ?tau') |- K empty ?tau' A => 
    apply WFU_K with (u:= u') (xp:=xp') (tau:=tau')
  end.
Hint Extern 1 (K empty _ A) => WFU_K.

Ltac simpl_lvpe_get ::=
  trace_goal;
  timeout 2
  repeat
    match goal with 
    | |- context [LVPE.V.get ?a LVPE.V.empty]    => trace_goal;
      rewrite~ LVPE.get_empty

  | |- context [LVPE.V.get ?a (?a ~p _) ]      => trace_goal;
    rewrite~ LVPE.get_single; try repeat case_var~
  | |- context [get ?a (?a ~ _) ]      => trace_goal;
    rewrite~ get_single; try repeat case_var~

  | |- context [LVPE.V.get ?a (_ &p (?a ~p _)) ]      => trace_goal;
    rewrite~ LVPE.get_push; try repeat case_var~
  | |- context [get ?a (_ & (?a ~ _)) ]      => trace_goal;
    rewrite~ get_push; try repeat case_var~

  | |- context [LVPE.V.get ?a (_ &p (_ ~p _)) ]      => trace_goal;
    rewrite~ LVPE.get_push; try repeat case_var~
  | |- context [LVPE.V.get ?a ((?b ~ _) & _)] => trace_goal;
    rewrite~ LVPE.get_concat; try repeat case_var~

  | H: context[LVPE.V.get _ empty = Some _] |- _ => 
    rewrite LVPE.get_empty in H; inversion H

  | H: context[LVPE.V.get _ LVPE.V.empty = Some _] |- _ => 
    rewrite LVPE.get_empty in H; inversion H
end.

Lemma WFU_upsilon_K:
  forall u, 
    WFU u ->
    forall x p tau, 
      LVPE.V.get (x,p) u = Some tau ->
      K empty tau A.
Proof.
  introv WFUd.
  induction WFUd.
  intros.
  auto.
  simpl_lvpe_get.
  intros.
  destruct(classicT((x0,p0) = (x,p))).
  rewrite LVPE.get_push in H2.
  rewrite If_l in H2.
  inversion H2.
  subst.
  assumption.
  rewrite If_l in H2; try assumption.
  rewrite LVPE.get_push in H2.
  rewrite If_r in H2; try assumption.
  apply IHWFUd with (x:=x0) (p:=p0); try assumption.
Qed.
Ltac WFU_upsilon_K :=
  match goal with 
    | H: WFU ?u',
      I: LVPE.V.get (?x',?p') ?u' = Some ?tau'
      |-  K empty ?tau' A =>
  apply WFU_upsilon_K with (u:=u') (x:= x') (p:=p')
end.
Hint Extern 1 (K empty _ A) => WFU_upsilon_K.
