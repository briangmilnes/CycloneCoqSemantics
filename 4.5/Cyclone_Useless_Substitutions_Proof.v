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
Close Scope list_scope.
Import LibEnvNotations.
Import LVPE.LibVarPathEnvNotations.

Lemma punt:
  forall d alpha alpha' k k' tau tau0,  
    alpha' \notin T.fv tau -> 
    K (d & alpha' ~ k) (T.open_rec 0 (ftvar alpha') tau) k' -> (* perhaps exists k' *)
    T.subst tau0 alpha (T.open_rec 0 (ftvar alpha') tau) =
                        T.open_rec 0 (ftvar alpha') tau -> 
    T.subst tau0 alpha tau = tau.
Proof.
  intros.
  induction tau; auto; simpl; fequals;
  try solve[simpl in H1;
  inversion H1;
  inversion H0; subst;
  try apply IHtau1; auto;
  try apply IHtau1; auto;
  try apply IHtau2; auto;
  try apply IHtau2; auto;
  inversion H2].

  simpl in H0.
  inversion H0; subst.
  apply IHtau; auto.
  inversion H2; subst.
Admitted.

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
  (* is this an induction problem with L needing to be d ? *)

  simpl.
  fequals.
  pick_fresh alpha'.
  assert(N: alpha' \notin L); auto.
  assert(O: alpha' # d); auto.
  assert(P: ok (d & alpha' ~ k)); auto.
  assert(Q: alpha # d & alpha' ~ k); auto.
  specialize (H alpha' N P).
  specialize (H0 alpha' N P Q P tau0).
  assert(R: alpha \notin (T.fv tau)); auto.

(*  apply punt with (d:= d) (alpha':=alpha') (k:= k) (k':= A); try assumption. *)
Admitted.

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

