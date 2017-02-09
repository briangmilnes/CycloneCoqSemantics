(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 
  
 Heap Object Safety

*)

Set Implicit Arguments.
Require Export Cyclone_Formal_Syntax Cyclone_Static_Semantics_Kinding_And_Context_Well_Formedness.
Require Export Cyclone_Dynamic_Semantics.
Require Export Cyclone_Classes Cyclone_Inductions Cyclone_LN_Tactics Cyclone_LN_Extra_Lemmas_And_Automation.
Require Export Cyclone_WFC_Lemmas.
Require Export Cyclone_WFU_Lemmas.
Require Export Cyclone_Context_Weakening_Proof.
Require Export Cyclone_Substitutions_Proof.
Require Export Cyclone_LN_Types_Lemmas.
Require Export Cyclone_Get_Lemmas.
Require Export Cyclone_Admit_Environment.
Require Export Cyclone_Path_Extension_Proof.
Require Export Cyclone_Canonical_Forms_Proof.
Require Export Case.
Close Scope list_scope.
Import LibEnvNotations.
Import LVPE.LibVarPathEnvNotations.

Ltac invert_get_nil:=
  match goal with
  | H: get' ?v1 nil _ |- _ => inversions* H
  end.

(* Path induction is not strong enough. *)
Lemma A_11_Heap_Object_Safety_1:
  forall v1 p, 
    Value v1 ->
    forall v2, 
      get' v1 p v2 ->
      forall v3,
        get' v1 p v3 ->
        v2 = v3.
Proof.
  introv Vv1 getd.
  induction getd; intros; try invert_get_nil;
  try solve[inversions H2; applys* IHgetd];
  try solve[inversions H1; applys* IHgetd].
Qed.

Lemma A_11_Heap_Object_Safety_2:
  forall p1, 
  forall v0 v1,
    Value v0 ->
    Value v1 ->
    get' v0 p1 v1 ->
    forall p2 v2,
      Value v2 ->
      get' v0 (app p1 p2) v2 ->
      get' v1 p2 v2.
Proof.
  intros p1.
  induction p1; intros.
  simpl in H3; auto.
  inversions *H1.
  destruct a; try destruct i.
  inversions H1.
  inversions H3.
  applys* (IHp1 v3).
  inversion H1; subst.
  inversion H3; subst.
  applys* (IHp1 v4).
  inversion H1; subst.
  inversion H3; subst.
  applys (IHp1 v3); auto.
Qed.

Ltac evert :=
  repeat 
  match goal with
    | H: exists _ _, _ |- _ => inversion H; clear H
    | H: exists _,  _ |- _ => inversion H; clear H
  end.
Ltac everts := evert; subst.

Ltac avert :=
  repeat 
  match goal with
    | H: _ /\ _ /\ _ |- _ => inversion H; clear H
    | H: _ /\ _ |- _ => inversion H; clear H
  end.
Ltac averts := avert; subst.

Ltac vert := repeat (evert || avert).
Ltac verts := vert; subst.

Lemma htyp_h__Value:
  forall u h g,
    htyp u g h g ->
    forall x v,
      get x h = Some v ->
      Value v.
Proof.
  introv htypd.
  induction htypd; intros.
  rewrite get_empty in H.
  inversion H.
  destruct(classicT(x0 = x)); subst.
  SearchAbout(get _ (_ & _ & _) = _).
  apply get_middle_eq_inv in H1; subst; auto.
  admit. (* ok (h & x ~ v & h') *)
  apply get_subst in H1; auto.
  applys* IHhtypd.
Qed.  

Ltac htyp_h__Value :=
  match goal with
  | H : htyp ?u' ?g' ?h' ?g', I: get ?x' ?h' = Some ?v' |- Value ?v' =>
    apply htyp_h__Value with (u:=u') (g:=g') (h:=h') (x:=x') (v:=v')
  end.
Hint Extern 1 (Value _) => htyp_h__Value.
  
Lemma get'_preserves_value:
  forall v,
    Value v ->
    forall p v',
      get' v p v' ->
      Value v'.
Proof.
  introv getd.
  induction getd; intros; inversions* H.
Qed.
Ltac get'_preserves_value :=
  match goal with
  | G: get' ?x ?p' ?y |- Value ?y =>
    apply get'_preserves_value with (v:= x) (p:=p') (v':=y); auto
  end.
Hint Extern 2 (Value _) => get'_preserves_value.

Lemma refp_h_u_pack_agreement:
  forall h u,
    refp h u ->
    forall x h Hx,
      get x h = Some Hx ->
      forall p1 Uxp1, 
      LVPE.V.get (x, p1) u = Some Uxp1 ->
      forall p1 t3 t4 v3 k,
        get' Hx p1 (pack t4 v3 (etype aliases k t3)) ->
        t4 = Uxp1.
Proof.
  introv refpd.
  induction refpd; intros.

  rewrite LVPE.get_empty in H0.
  inversion H0.

  forwards G: H2.
  rewrite LVPE.get_push in H2.
  case_varpath.
  inversions C.
  case_if.
  inversions H2.
(* Missing Path.
  applys* IHrefpd.
  admit.
*)
  admit.
  case_if.
  applys IHrefpd; eauto.
(*
  apply IHrefpd with (x:=x0)(h:=h0)(Hx:=Hx)
                     (p1:=p1)(p2:=p0) (t3:=t3)(v3:=v3)(k:=k0); auto.
*)
Admitted.


Lemma A_11_Heap_Object_Safety_3_1:
  forall h u, 
    refp h u ->
    forall g,
      htyp u g h g ->
      forall p2 t2, 
      forall x v p1 v1, 
        get x h = Some v ->
        get' v p1 v1 ->
        forall t1, 
          rtyp empty u g v1 t1 ->
            gettype u x p1 t1 p2 t2 ->
  exists v2,
    get' v (app p1 p2) v2 /\
    rtyp empty u g v2 t2.
Proof.
  introv refpd htypd.
  induction p2; intros.
  Case "p2=nil".
   inversions* H2.
   exists v1.
   rewrite* List.app_nil_r.
   auto.

  destruct a; try destruct i.
(* Bug: simplify backwards chain, fix lists. *)
  Case "p2 =0 ...".
   rename v into Hx.
   rename p2 into p3.
   forwards G: H2.
   inversions* H2.  
   rename t0 into t10.
   rename t3 into t11.
   forwards R: H1.
   apply A_9_Canonical_Forms_2 with (t0:=t10) (t1:=t11) in H1; auto.
   verts.
   rename x0 into v10.
   rename x1 into v11.
   assert(P: cpair v10 v11 =cpair v10 v11); auto.
   lets PE: (@A_10_Path_Extension_1_A_pair Hx p1 (cpair v10 v11) H0 v10 v11 P).
   averts.
   inversions* R.
   specialize (IHp2 t2 x Hx (app p1 (cons (i_pe zero_pe) nil)) v10 H H1 t10 H10 H8).
   (* Fuck lists are not read write consistent. *)
   assert(LT: (app (app p1 (cons (i_pe zero_pe) nil)) p3) =
              (app p1 (cons (i_pe zero_pe) p3))).
   admit.
   rewrite <- LT.
   assumption.
  Case "p2 =1 ...".
   admit.
  Case "p2 =u ...".
   rename v into Hx.
   rename p2 into p3.
   inversions* H2.
   rename tau' into t3.
   rename tau'' into Uxp1.
   forwards R: H1.
   apply A_9_Canonical_Forms_7 with (k:=k) (t':=t3) in H1; auto.
   verts.
   rename x0 into t4.
   rename x1 into v3.
   assert(pack t4 v3 (etype aliases k t3) =pack t4 v3 (etype aliases k t3)); auto.
   lets PE: (@A_10_Path_Extension_1_A_pack Hx p1 (pack t4 v3 (etype aliases k t3)) H0
             t4 v3 t3 k H1).

   assert(t4 =Uxp1). 
   eapply refp_h_u_pack_agreement; eauto.

   inversions* R.
   pick_fresh alpha.
   assert(NI: alpha \notin L); auto.
   specialize (H11 alpha NI).
   subst.
   specialize(IHp2 t2 x Hx (app p1 (cons u_pe nil)) v3 H PE (T.open_rec 0 Uxp1 t3) H11 H9).
   assert(LT: (app (app p1 (cons u_pe nil)) p3) =(app p1 (cons u_pe p3))).
   admit.
   rewrite <- LT.
   auto.
Qed.

Lemma A_11_Heap_Object_Safety_3_2:
  forall h u, 
    refp h u ->
    forall g,
      htyp u g h g ->
      forall x v p1 v1, 
        get x h = Some v ->
        get' v p1 v1 ->
        forall t1, 
          rtyp empty u g v1 t1 ->
          forall p2 t2, 
            gettype u x p1 t1 p2 t2 ->
            forall v2', (* Is this the v2' of above?*)
              exists v1', set' v1 p2 v2' v1'.
Admitted.

(* Nope, 
Corollary A_11_Heap_Object_Safety_3_1':
    forall h u, 
    refp h u ->
    forall g,
      htyp u g h g ->
      forall x v empty v1, 
        get x h = Some v ->
        get' v empty v1 ->
        forall t1, 
          rtyp empty u g v1 t1 ->
          forall p2 t2, 
            gettype u x empty t1 p2 t2 ->
            forall v2', (* Is this the v2' of above?*)
              exists v1', set' v1 p2 v2' v1'.
 *)

