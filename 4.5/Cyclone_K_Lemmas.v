(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

   Some K Lemmas.

*)

Set Implicit Arguments.
Require Export Cyclone_Formal_Syntax Cyclone_Static_Semantics_Kinding_And_Context_Well_Formedness.
Require Export Cyclone_Static_Semantics_Typing_Heap_Objects.
Require Export Cyclone_Classes Cyclone_Inductions Cyclone_LN_Tactics Cyclone_LN_Extra_Lemmas_And_Automation.
Require Export Cyclone_Ok_Lemmas Cyclone_LN_Types_Lemmas.
Require Export Cyclone_Fset_Lemmas Cyclone_Get_Lemmas.
Require Export Cyclone_WFD_Lemmas.
Close Scope list_scope.
Import LibEnvNotations.
Import LVPE.LibVarPathEnvNotations.

Lemma K_weakening:
  forall tau d,
    K d tau A ->
    forall d',
      WFD d ->
      extends d d' ->
      K d'     tau A.
Proof.
  introv Kempty.
  induction Kempty; try solve[auto].
  intros.
  apply_fresh K_utype; intros.
  assert(I: y \notin L); auto.
  intros.
  apply_fresh K_etype; intros.
  assert(I: y \notin L); auto.
Qed.  

Lemma K_empty_var:
  forall v k, 
    K empty (ftvar v) k -> False.
Proof.
  intros.
  inversions H.
  rewrite get_empty in H2.
  inversion H2.
  inversions H0.
  rewrite get_empty in H2.
  inversion H2.
Qed.
Hint Immediate K_empty_var.

(* I need a stronger lemma, = or to rewrite. *)

Lemma open_var_fv_eq : forall t n x,
    T.fv (T.open_rec n (ftvar x) t) = (T.fv t \u \{x}) \/
    T.fv (T.open_rec n (ftvar x) t) = (T.fv t).
Proof.
  intros t.
  induction t; intros; simpl; try case_nat; auto with fset;
  try solve[
        simpl;
        left;
        rewrite union_empty_l;
        auto with fset].
(* Bug ugly won't ltac. *)

  specialize(IHt1 n x);
  specialize(IHt2 n x);
  inversion IHt1; inversion IHt2;
  rewrite H; rewrite H0.
  left.
  rewrite <- union_assoc.
  rewrite <- union_assoc.
  rewrite* union_middle_shuffle.
  left.
  rewrite <- union_assoc.
  rewrite <- union_assoc.
  rewrite* union_middle_r.
  left.
  rewrite* <- union_assoc.  
  right*.

  specialize(IHt1 n x);
  specialize(IHt2 n x);
  inversion IHt1; inversion IHt2;
  rewrite H; rewrite H0.
  left.
  rewrite <- union_assoc.
  rewrite <- union_assoc.
  rewrite* union_middle_shuffle.
  left.
  rewrite <- union_assoc.
  rewrite <- union_assoc.
  rewrite* union_middle_r.
  left.
  rewrite* <- union_assoc.  
  right*.  
Qed.  

Lemma fv_var:
  forall A alpha tau (d : env A), 
    alpha \notin T.fv tau ->
    T.fv tau \c \{ alpha} \u dom d ->
    T.fv tau \c dom d.
Proof.
  intros.
  induction tau; simpl; simpl in H; simpl in H0; auto with fset.
  assert(alpha <> v); auto.
  lets: subset_remove_r (fset Tau).
  apply subset_remove_r with (b:= alpha); auto.
  assert(alpha \notin T.fv tau1); auto.
  assert(alpha \notin T.fv tau2); auto.
  specialize (IHtau1 H1).
  specialize (IHtau2 H2).
  assert(H3 : (T.fv tau1 \u T.fv tau2 \c \{ alpha} \u dom d)); auto.
  apply subset_remove_l_r in H0.  
  apply subset_remove_l_l in H3.
  auto with fset.

  assert(H3 : (T.fv tau1 \u T.fv tau2 \c \{ alpha} \u dom d)); auto.
  apply subset_remove_l_r in H0.  
  apply subset_remove_l_l in H3.
  auto with fset.  
Qed.  

Lemma fv_var_2:
  forall A alpha tau (d : env A), 
    alpha \notin T.fv tau ->
    T.fv tau \u \{ alpha} \c \{ alpha} \u dom d ->
    T.fv tau \c dom d.
Proof.
  intros.
  apply subset_remove_l_r in H0.
  apply fv_var with (alpha:= alpha); auto.
Qed.

Lemma K_fv:
  forall tau d k,
    WFD d ->
    K d tau k ->
    T.fv tau \c fv_delta d.
Proof.
(* BUG ugly, repetition, will not ltac *)
  introv WFDd Kd.
  induction Kd; assert(ok d); auto; try solve[simpl; auto with fset].

  pick_fresh alpha.
  assert(NI: alpha \notin L); auto.
  assert(OKda: ok(d & alpha ~ k)); auto.
  assert(WFDda: WFD(d & alpha ~k)); auto.
  specialize (H0 alpha NI OKda WFDda).
  lets: open_var_fv_eq tau 0 alpha.
  inversion H2.
  rewrite H3 in H0.
  unfold fv_delta.
  unfold fv_delta in H0.
  rewrite dom_push in H0.
  apply fv_var_2 with (alpha:=alpha); auto.
  rewrite H3 in H0.
  unfold fv_delta in H0.
  unfold fv_delta.
  apply fv_var with (alpha:= alpha); auto.
  unfold fv_delta in H0.
  unfold fv_delta.
  rewrite dom_push in H0.
  auto.  

  pick_fresh alpha.
  assert(NI: alpha \notin L); auto.
  assert(OKda: ok(d & alpha ~ k)); auto.
  assert(WFDda: WFD(d & alpha ~k)); auto.
  specialize (H0 alpha NI OKda WFDda).
  lets: open_var_fv_eq tau 0 alpha.
  inversion H2.
  rewrite H3 in H0.
  unfold fv_delta.
  unfold fv_delta in H0.
  rewrite dom_push in H0.
  apply fv_var_2 with (alpha:=alpha); auto.
  rewrite H3 in H0.
  unfold fv_delta in H0.
  unfold fv_delta.
  apply fv_var with (alpha:= alpha); auto.
  unfold fv_delta in H0.
  unfold fv_delta.
  rewrite dom_push in H0.
  auto.  
Qed.

Lemma K_empty_closed:
  forall tau k,
    K empty tau k ->
    T.fv tau = \{}.
Proof.
  intros.
  lets: K_fv tau (@empty Kappa).
  apply H0 in H.
  unfold fv_delta in H.
  rewrite dom_empty in H.
  apply contained_in_empty in H; auto.
  auto.
Qed.

