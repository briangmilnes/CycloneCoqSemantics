(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Typing Well Formedness

*)

Set Implicit Arguments.
Require Export Cyclone_Formal_Syntax Cyclone_Static_Semantics_Kinding_And_Context_Well_Formedness.
Require Export Cyclone_Static_Semantics_Typing_Heap_Objects.
Require Export Cyclone_Classes Cyclone_Inductions Cyclone_LN_Tactics Cyclone_LN_Extra_Lemmas_And_Automation.
Require Export Cyclone_WFC_Lemmas.
Require Export Cyclone_WFU_Lemmas.
Require Export Cyclone_Context_Weakening_Proof.
Require Export Cyclone_Substitutions_Proof.
Require Export Cyclone_LN_Types_Lemmas.
Require Export Cyclone_Get_Lemmas.
Require Export Cyclone_Admit_Environment.
Close Scope list_scope.
Import LibEnvNotations.
Import LVPE.LibVarPathEnvNotations.

Lemma A_7_Typing_Well_Formedness_1:
  forall u,
    WFU u ->
    forall x p t p' t',
      gettype u x p t p' t' ->
      forall d,
        ok d  ->
        K d t A ->
        K d t' A.
Proof.
  introv WFUd Gd.
  induction Gd; auto; intros.

  inversions H0.
  applys* IHGd.
  inversions H1.
  inversions H0.
  applys* IHGd.
  inversions H1.

  apply* IHGd.

  inversion H1; subst; try solve[inversion H2].
  pick_fresh alpha.
  assert(NI: alpha \notin L); auto.
  assert(OKa: ok (d & alpha ~ k)); auto.
  specialize(H4 alpha NI OKa).
(* Still interesting 
  inversions* Gd; intros.
  


  pick_fresh alpha.
  assert(NI: alpha \notin L); auto.
  assert(OKa: ok (d & alpha ~ k)); auto.
  specialize (H4 alpha NI OKa).
  assert(K empty tau'' A).
  apply WFU_upsilon_K with (u:= u) (x:=x) (p:=p); auto.
  lets CW2: A_1_Context_Weakening_2 WFUd x p d tau''.
  specialize (CW2 H0 H).
  lets SL1: A_6_Subsititution_1 d (@empty Kappa) tau'' A.
  rewrite drop_empty in SL1.
  specialize (SL1 H0 CW2 alpha tau A).
  rewrite drop_empty in SL1.
  apply* IHGd.
  apply ok_change_k with (k':= A) in OKa.
  specialize (SL1 OKa).
*)
  
Admitted.

Function A_7_Typing_Well_Formedness_Prop (In : Type) (H : TypJudgement In) 
         (d : Delta) (u : Upsilon) (g : Gamma) (s : In) (t : Tau)
         (st : typ' d u g s t) := 
    typ' d u g s t ->
    (WFC d u g /\ K d t A).
Hint Unfold A_7_Typing_Well_Formedness_Prop.

Ltac inversion_K_B :=
  match goal with
    | H : K _ (cross _ _) B |- _ => try solve[inversion H]
  end.

Ltac forwards_ih :=
  match goal with
  | A: ?x, H: ?x -> WFC _ _ _ /\ K _ _ _ |- _ =>
    forwards*: H
  end.

Ltac invert_and :=
  match goal with
  | H : _ /\ _ |- _ => inversions* H
  end.

Ltac invert_complex_K :=
  match goal with
  | H : K _ (_ _ _) _ |- _ => inversions* H
  end.

Lemma A_2_Term_Weakening_2_ltyp:
  forall (d : Delta) (u : Upsilon) (g : Gamma) (s : E) (t : Tau) (ty : typ' d u g s t),
   A_7_Typing_Well_Formedness_Prop LtypJudgement d u g s t ty.
Proof.
  intros.
  Typ_Induction ltyp_ind_mutual A_7_Typing_Well_Formedness_Prop;
    try solve[auto]; intros; split*;
    try solve[forwards_ih;
            invert_and;
            invert_complex_K;
            try inversion_K_B];
  try solve[
        pick_fresh alpha;
        assert(NI: alpha \notin L); auto;
        specialize (H alpha NI);
        try specialize (r alpha NI); auto;
        try specialize (s1 alpha NI); auto;
          applys* H];
  try solve[inversions* H;
              apply A_7_Typing_Well_Formedness_1 with (u:=u0) (x:= x) (p:= nil) (p':= p) (t:= tau'); auto];
  try solve[
        apply K_B_A;
        apply K_ptype;
        auto;
        applys* H].

  specialize (H r).
  specialize (H0 r0).
  inversion H0.
  inversion H.
  inversions* H5.
  inversion H6.

  forwards*: H.
  inversion H1.
  lets SL1: A_6_Subsititution_1.
  inversions* H3; try solve[inversion H4].
  admit.


  pick_fresh alpha.
  assert(NI: alpha \notin L); auto.
  try specialize (s1 alpha NI); auto.
  try specialize (H alpha NI s1).
  inversion H.
  apply WFC_strength with (alpha:= alpha) (tau:= tau); auto.

  pick_fresh alpha.
  assert(NI: alpha \notin L); auto.
  try specialize (s1 alpha NI); auto.
  try specialize (H alpha NI).
  try specialize (r alpha NI); auto.
  apply* K_arrow.
  inversions* H0.

  try applys* H.






    