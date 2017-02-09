(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION".   Daniel Grossman, August 2003 *)
(* Lemmas for WFDG  *)
(* Brian Milnes 2016 *)
Set Implicit Arguments.
Require Export Cyclone_Formal_Syntax Cyclone_Static_Semantics_Kinding_And_Context_Well_Formedness.
Require Export Cyclone_Static_Semantics_Typing_Heap_Objects.
Require Export Cyclone_Classes Cyclone_Inductions Cyclone_LN_Tactics Cyclone_LN_Extra_Lemmas_And_Automation.
Require Export Cyclone_Context_Weakening_Proof.
Require Export Cyclone_Admit_Environment.
Close Scope list_scope.
Import LibEnvNotations.
Import LVPE.LibVarPathEnvNotations.

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

Lemma WFDG_gamma_K:
  forall d g, 
    WFDG d g ->
    forall x tau, 
      get x g = Some tau ->
      K d tau A.
Proof.
  introv WFDGd.
  induction WFDGd; intros.
  apply binds_empty_inv in H0.
  inversion H0.
  specialize (IHWFDGd x0 tau0).
  unfold binds in *.
  destruct(classicT(x0 = x)); subst.
  rewrite get_push in H3.
  case_var.
  inversion H3; subst; assumption.
  rewrite get_push in H3.
  case_var.
  auto.
Qed.
Ltac WFDG_gamma_K :=
  match goal with 
   | H:  WFDG ?d' ?g', 
     I: get ?x' ?g' = Some ?tau'
   |- K ?d' ?tau' A =>
    apply WFDG_gamma_K with (d:=d') (g:=g') (x:=x') (tau:=tau')
end.
Hint Extern 1 (K _ _ A) => WFDG_gamma_K.

Lemma WFDG_gamma__K_A:
  forall d g alpha tau,
    WFDG d (g & alpha ~ tau) ->
    K d tau A.
Proof.
  introv WFDGd.
  apply WFDG_gamma_K with (g:= g & alpha ~ tau) (x:=alpha); auto.
Qed.  
Ltac WFDG_gamma__K_A :=
  match goal with
  | H: WFDG ?d (?g' & ?alpha ~ ?tau) |- K ?d ?tau A =>
    apply WFDG_gamma_K with (g:= ?g' & ?alpha ~ ?tau) (x:=?alpha); auto
  end.
    
Lemma WFDG_gamma_weakening:
  forall d g y tau, 
    y \notin (fv_gamma g) ->
    K d tau A ->
    WFDG d g ->
    WFDG d (g & (y ~ tau)).
Proof.
  introv NI WFd.
  auto.
Qed.
Ltac WFDG_gamma_weakening :=
  match goal with
    | H: K ?d' ?tau' A, 
      I: WFDG ?d' ?g' 
    |-  WFDG ?d' (?g' & (?y' ~ ?tau')) =>
      apply WFDG_gamma_weakening with (tau:=tau');
      notin_solve
  end.
Hint Extern 1 (WFDG _ (_ & (_ ~ _))) => WFDG_gamma_weakening.

Lemma WFDG_delta_weakening:
  forall alpha d g k, 
    alpha \notin fv_delta d ->
    WFDG d g ->
    WFDG (d & alpha ~ k) g.
Proof.
  lets: WFDG_gamma_weakening.
  introv ANI WFDGd.
  induction WFDGd; auto.
  assert(alpha \notin fv_delta d).
  auto.
  apply IHWFDGd in H4.
  constructor; try assumption.
  constructor; try assumption.
  apply A_1_Context_Weakening_1 with (d:= d); try assumption.
  auto.
  auto.
Qed.
Ltac WFDG_delta_weakening :=
  match goal with
    | H: ?alpha \notin _,
      I: WFDG ?d' ?g'
    |- WFDG (?d' & ?alpha ~ ?k) ?g' =>
      apply WFDG_delta_weakening; notin_solve
  end.
Hint Extern 1 (WFDG (_ & _ ~ _) _) => WFDG_delta_weakening.

Lemma WFDG_strength:
  forall alpha d0 g0 tau,
  alpha \notin fv_delta d0 ->
  alpha \notin fv_gamma g0 ->
  WFDG d0 (g0 & alpha ~ tau) ->
  WFDG d0 g0.
Proof.
  introv ad ag WFDGd.
  inversions* WFDGd.
  apply empty_not_constructed in H.
  inversion H.
  apply eq_inversion_env in H.
  inversion H.
  subst*.
Qed.
