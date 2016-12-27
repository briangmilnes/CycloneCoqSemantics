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
    | H : WFDG ?d' ?g |- ok ?g => apply WFDG_ok_gamma with (d:=d')
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
  intros*.
  inversion* H; subst.
Qed.
Ltac WFC_ok_gamma :=
  match goal with
    | H : WFC ?d' ?u' ?g|- ok ?g => apply WFC_ok_gamma with (d:= d') (u:=u')
  end.
Hint Extern 1 (ok _) => try WFC_ok_gamma.

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

Lemma WFDG_K:
  forall d g,  
    WFDG d g ->
    forall x tau,
      get x g = Some tau ->
      K d tau A.
Proof.
  intros.
  induction H.
  rewrite get_empty in H0.
  inversion H0.
  rewrite get_push in H0.
  case_var.
  inversion H0; subst.
  assumption.
  apply IHWFDG.
  assumption.
Qed.
Ltac WFDG_K := 
  match goal with
    | H : WFDG ?d' ?g', I: get ?x' ?g' = Some ?tau' |- K ?d' ?tau' A =>
      apply WFDG_K with (d:=d') (g:=g') (x:= x') (tau:=tau')
  end.
Hint Extern 1 (K _ _ A) => WFDG_K.

Lemma WFC_K:
  forall d u g,
    WFC d u g ->
    forall x tau,
      get x g = Some tau ->
      K d tau A.
Proof.
  intros.
  inversion H; subst.
  auto.
Qed.
Ltac WFC_K := 
  match goal with
    | H : WFC ?d' ?u' ?g', I: get ?x' ?g' = Some ?tau' |- K ?d' ?tau' A =>
      apply WFC_K with (d:=d') (g:=g') (x:= x') (tau:=tau')
  end.
Hint Extern 1 (K _ _ A) => WFC_K.
