(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Term Weakening 

*)

Set Implicit Arguments.
Require Export Cyclone_Formal_Syntax Cyclone_Static_Semantics_Kinding_And_Context_Well_Formedness.
Require Export Cyclone_Static_Semantics_Typing_Heap_Objects.
Require Export Cyclone_Classes Cyclone_Inductions Cyclone_LN_Tactics Cyclone_LN_Extra_Lemmas_And_Automation.
Require Export Cyclone_Context_Weakening_Proof.
Require Export Cyclone_LN_Types_Lemmas.
Require Export Cyclone_Admit_Environment.
Require Export Cyclone_Subst_Lemmas.
Require Export Cyclone_K_Lemmas.
Require Export Cyclone_WFD_Lemmas.
Close Scope list_scope.
Import LibEnvNotations.
Import LVPE.LibVarPathEnvNotations.

Lemma L2:
  forall tau alpha' d k alpha, 
    T.fv tau  \c fv_delta (d & alpha' ~ k) ->
    alpha <> alpha' ->
    alpha # d ->
    alpha \notin T.fv tau.
Proof.
  intros.
  unfolds in H1.
  unfolds.
  unfold not.
  intros.
  unfolds in H.
  specialize (H alpha H2).
  unfold fv_delta in H.
  rewrite dom_push in H.
  rewrite in_union in H.
  inversion H.
  rewrite in_singleton in H3.
  contradiction.
  apply H1 in H3.
  contradiction.
Qed.

Lemma in_union_strength:
  forall (A : Type) (x : A) (E F : fset A), x \in E -> x \in E \u F.
Proof.
  intros.
  rewrite in_union.
  left*.
Qed.

Lemma L1:
  forall tau alpha' d k alpha, 
    T.fv tau \u \{ alpha'} \c fv_delta (d & alpha' ~ k) ->
  alpha <> alpha' ->
  alpha # d ->
  alpha \notin T.fv tau.
Proof.
  intros.
  unfolds in H1.
  unfolds.
  unfold not.
  intros.
  unfolds in H.
  apply in_union_strength with (F:=\{alpha'}) in H2.
  specialize (H alpha H2).
  unfold fv_delta in H.
  rewrite dom_push in H.
  rewrite in_union in H.
  inversion H.
  rewrite in_singleton in H3.
  contradiction.
  apply H1 in H3.
  contradiction.
Qed.  

Lemma A_4_Useless_Substitutions_1:
  forall alpha d,
    alpha \notin dom d ->
    ok d ->
    forall tau' k, 
      K d tau' k ->
      forall tau, 
        T.subst tau alpha tau' = tau'.
Proof.
  introv NI OKd Kd.
  induction Kd; intros;
  try solve[simpl; auto; try case_var*; 
            try solve[rewrite* get_none in H; inversion H]; fequals*].
  (* Bug ugly won't automate. *)
  simpl.
  fequals.
  pick_fresh alpha'.
  assert(NIL: alpha' \notin L). auto.
  assert(NILA: alpha <> alpha'). auto.
  assert(OK: ok (d & alpha' ~ k)). auto.
  specialize (H alpha' NIL OK).
  apply K_fv in H; auto.
  assert(alpha \notin fv_delta(d & alpha' ~ k)). auto.
  assert(alpha \notin T.fv tau).
  lets: (open_var_fv_eq tau 0 alpha').
  inversion H2.
  rewrite H3 in H.
  apply L1 with (alpha':= alpha') (d:=d) (k:= k); auto.
  rewrite H3 in H.
  apply L2 with (alpha':= alpha') (d:=d) (k:= k); auto.
  apply* fv_subst.

  simpl.
  fequals.
  pick_fresh alpha'.
  assert(NIL: alpha' \notin L). auto.
  assert(NILA: alpha <> alpha'). auto.
  assert(OK: ok (d & alpha' ~ k)). auto.
  specialize (H alpha' NIL OK).
  apply K_fv in H; auto.
  assert(alpha \notin fv_delta(d & alpha' ~ k)). auto.
  assert(alpha \notin T.fv tau).
  lets: (open_var_fv_eq tau 0 alpha').
  inversion H2.
  rewrite H3 in H.
  apply L1 with (alpha':= alpha') (d:=d) (k:= k); auto.
  rewrite H3 in H.
  apply L2 with (alpha':= alpha') (d:=d) (k:= k); auto.
  apply* fv_subst.  
Qed.
 
Lemma A_4_Useless_Substitutions_2:
  forall alpha d g,
    alpha \notin dom d ->
    WFDG d g ->
    forall tau, 
      EnvOps.map (fun tau' =>  (T.subst tau alpha tau')) g = g.
Proof.  
  introv NI WFDGd.
  induction WFDGd.
  intros.
  rewrite* map_empty.
  intros.
  rewrite map_push.
  rewrite* IHWFDGd.
  rewrite A_4_Useless_Substitutions_1 with (d:=d) (k:=A); auto.
Qed.

Lemma A_4_Useless_Substitutions_3:
  forall u,
    WFU u ->
    forall tau alpha, 
      LVPE.V.map (fun tau' => (T.subst tau alpha tau')) u = u.
Proof.  
  introv WFUd.
  induction WFUd; intros.
  rewrite* LVPE.map_empty.

  rewrite LVPE.map_push.
  rewrite IHWFUd.
  rewrite A_4_Useless_Substitutions_1 with (d:= empty) (k:=A); auto.
Qed.

