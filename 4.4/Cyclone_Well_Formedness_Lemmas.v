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

Ltac solve_wf :=
  repeat 
    match goal with
      |- WFC ?d ?u (_ & _ ~ _) =>
      constructor*
      | H : WFC ?d  _ _|- ok ?d => 
        inversion* H
      | H : WFC _ ?u _ |- LVPE.okp ?u => 
        inversion* H
      | |- (WFDG _ (_ & _ ~ _)) =>
        simpl_contexts; constructor*
      | H: WFC ?d _ ?g |- WFDG ?d ?g => inversion* H

      | |- ok ddot => unfold ddot; apply get_empty
      | |- ok gdot => unfold gdot; apply get_empty
      | |- LVPE.okp gdot => unfold gdot; apply get_empty
  end.

Hint Extern 4 (WFC _ _ _) => idtac " (WFC _ _ _)"; trace_goal; solve_wf.
Hint Extern 4 (WFDG _ _) => idtac " (WFC _ _ _)"; trace_goal; solve_wf.

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

Lemma WFDG_ok_delta:
  forall d g,
    WFDG d g ->
    ok d.
Proof.
  intros.
  inversion* H.
Qed.

Ltac WFDG_ok_delta :=
  match goal with
    | H : WFDG ?d ?g' |- ok ?d => apply WFDG_ok_delta with (g:= g')
  end.
Hint Extern 1 (ok _) => try WFDG_ok_delta.

Lemma WFDG_ok_gamma:
  forall d g,
    WFDG d g ->
    ok g.
Proof.
  intros.
  inversion H; subst.
  constructor.
  constructor.
  assumption.
  apply* get_none_inv.
Qed.
Ltac WFDG_ok_gamma :=
  match goal with
    | H : WFDG _ ?g |- ok ?g => apply WFDG_ok_gamma
  end.
Hint Extern 1 (ok _) => try WFDG_ok_gamma.

Lemma WFC_ok_delta:
  forall d u g, 
    WFC d u g ->
    ok d.
Proof.
  intros.
  inversion* H.
Qed.
Ltac WFC_ok_delta :=
  match goal with
    | H : WFC ?d ?u' ?g'|- ok ?d => apply WFC_ok_delta with (u:=u') (g:=g')
  end.
Hint Extern 1 (ok _) => try WFC_ok_delta.

Lemma WFC_ok_gamma:
  forall d u g, 
    WFC d u g ->
    ok g.
Proof.
  intros.
  inversion* H; subst.
  inversion H0; subst.
  constructor.
  constructor.
  assumption.
  apply* get_none_inv.
Qed.
Ltac WFC_ok_gamma :=
  match goal with
    | H : WFC ?d' ?u' ?g|- ok ?g => apply WFC_ok_gamma with (d:= d') (u:=u')
  end.
Hint Extern 1 (ok _) => try WFC_ok_gamma.

Lemma WFU_K:
  forall u xp tau,
    WFU (u &p xp ~p tau) ->
    K ddot tau A.
Proof.
  introv WFUd.
  induction u.
  inversion WFUd.
  unfold udot in H0.
  apply LVPE.empty_push_inv in H0.
  inversion H0.
  rewrite <- LVPE.V.empty_def in H.
  apply LVPE.eq_push_inv in H.
  inversion H.
  inversion H5.
  subst.
  assumption.
  inversion WFUd.
  unfold udot in H0.
  apply LVPE.empty_push_inv in H0.
  inversion H0.
  apply LVPE.eq_push_inv in H.
  inversion H.
  inversion H5.
  subst.
  assumption.
Qed.

Lemma WFDG_K:
  forall d g,  
    WFDG d g ->
    forall x tau,
      binds x tau g ->
      K d tau A.
Proof.
  intros.
  induction H.
  unfold binds in H0.
  unfold gdot in H0.
  rewrite get_empty in H0.
  inversion H0.
  unfold binds in H0, IHWFDG.
  rewrite get_push in H0.
  case_var.
  inversion H0; subst.
  assumption.
  apply IHWFDG.
  assumption.
Qed.

Lemma WFC_K:
  forall d u g,
    WFC d u g ->
    forall x tau,
      binds x tau g ->
      K d tau A.
Proof.
  intros.
  inversion H; subst.
  apply WFDG_K with (g:=g) (x:=x).
  assumption.
  assumption.
Qed.
