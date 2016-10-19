(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Defining type safety, page 67.

*)

Require Export LanguageModuleDef.
Require Export StaticSemantics.
Require Export DynamicSemanticsHeapObjects.
Require Export TacticNotations.

(* Bug, Miswrote theorem. I like the forall quantified version although
   I can naturally express this with exists.  *)
(* This is not the right induction just whacking a length on it. *)
(* I need to induct on path extension, perhaps reverse paths? *)

Functional Scheme rev_ind := Induction for rev Sort Prop.

Lemma A_11_Heap_Object_Safety_1:
  forall (v1 : E),
      forall (p : Path) (v2 : E) (v3 : E),
        get v1 p v2 ->
        get v1 p v3 -> 
        v2 = v3. 
Proof.
  intros v1.
  induction v1;
   try (intros p v2 v3 getv1pv2 getv1pv3;
        inversion getv1pv2;
        inversion getv1pv3;
        try reflexivity;
        crush).
  (* 1,2 should invert on getv1pv* why didn't it? *)
  specialize (IHv1_1 p0 v3 v2).
  apply IHv1_1 in H14.
  crush.
  assumption.
  
  specialize (IHv1_2 p0 v3 v2).
  apply IHv1_2 in H14.
  crush.
  assumption.

  specialize (IHv1 p0 v2 v3).
  apply IHv1 in H6.
  crush.
  assumption.
Qed.

Lemma A_11_Heap_Object_Safety_2:
  forall (v0 : E) (p1 : Path) (v1 : E),
    Value v0 ->
    Value v1 ->
    get v0 p1 v1 ->
    forall (p2 : Path) (v2 : E),
      Value v2 ->
      get v0 (p1 ++ p2) v2 ->
      get v1 p2 v2.
Proof.
  (* Try induction on the values. *)
  intros v0.
  (* Try to learn to get rid of silly goals. *)
  induction v0; 
    try ( 
        intros p1 v1 val0 val1 getv0p1v1;
        inversion getv0p1v1;
        intros p2 v2 valv2;
        intros get;
        inversion get;
        crush).
  intros p1;
  induction p1 as [| pe1 p1'].
  Case "pair and p1=[]".
   intros v1 valpair valv1 getcpair p2 v2 valv2 getcpairnil.
   inversion getcpair.
   crush.

  (* A pair and a pack, nice strong induction hypotheses. *)
  Case "pair and pe1::p1".
    SCase "pe1= i which won't work".
    intros v1 valpair valv1 getcpair p2 v2 valv2 getcpairnil.
    destruct pe1; try destruct i.
    SSCase "pe1=zero_pe".
    inversion valpair; inversion getcpair; inversion getcpairnil; crush.
    specialize (IHv0_1 p1' v1 H1 H6 H10 p2 v2 H14 H18).
    assumption.
    SSCase "pe1=one_pe".
    inversion valpair.
    inversion getcpair.
    inversion getcpairnil.
    crush.
    specialize (IHv0_2 p1' v1 H2 H6  H10 p2 v2 H14 H18).
    assumption.
    SSCase "pe1=u_pe".
     inversion getcpair.
   Case "v0 is pack".
    intros p1 v1 valpack valv1.
    destruct p1.
    SCase "p1 is []".
    intros getpack p2 v2 valv2 getpackp2.
    rewrite app_nil_l in getpackp2.
    inversion valpack; inversion getpack; inversion getpackp2; crush.
    SCase "p1 is ".
     destruct p.
     intros integerpath.
     inversion integerpath.
     inversion valpack.
     intros getpacku p2 v2 valv2 step.
     inversion getpacku.
     crush.
     inversion step.
     crush.
     apply IHv0 with (p1:= p1); try assumption.
Qed.

Lemma A_11_Heap_Object_Safety_3:
  forall (h : Heap) (u : Upsilon) (g : Gamma) 
         (x : EVar) (vhx v1 : E) (t1 t2: Tau) 
         (p1 p2 : Path),
    Value v1 ->
    refp h u ->
    htyp u g h g ->
    H.map h x = Some vhx ->
    get vhx p1 v1 ->
    rtyp D.empty u g v1 t1 ->
    gettype u x p1 t1 p2 t2 ->
    (exists (v2 : E),
       get vhx (p1 ++ p2) v2 /\ 
       rtyp D.empty u g v2 t2) /\
    (forall (v2' : E),
       Value v2' ->
       (exists (v1' : E),
          Value v1' ->
          set v1 p2 v2' v1')).
Proof.
  intros h u g x vhx v1 t1 t2 p1 p2.
  intros valv1 refpder htypder getHder getder rtypder gettypeder.
  split.
  (* Try induction v1, p. 
  induction v1; induction p2. 24 uncrushable goals. *)
  (* Try functional induction on get type, 12/24.*)
  gettype_ind_cases (induction gettypeder) Case;
    try inversion gettypeder;   (* 12/24 *)
    try (rewrite app_nil_r;
         apply ex_intro with (x:=v1);
         split;
         assumption;
         inversion gettypeder;
         assumption). (* 8/12 *)
  (* Well I chopped the goals down, but now is it actually provable? *)
  (* Scotch whisky society, 10.76, bunnahbin distilery,
     like smoking a hookah over oyster shells. *)
  crush.
(* Why can I not clear the bad goals with an inversion on rtypder? *)
(* destruct v1.  *)
(*  induction v1 *)
(* induction rtypder ? *)
  (* Have to get more in the context and then destruct v1. *)
  (* But it's an existential. *)
  (* assert (A: get v1 (i_pe zero_pe) v2). *)
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
Admitted.

Lemma gettype_nil_path:
  forall (u : Upsilon) (x : EVar) (p : Path) (t1 t2 : Tau),
    gettype u x p t1 [] t2 ->
     t1 = t2.
Proof.
  intros u x p t1 t2.
  induction t1.
  crush.
  crush.
  crush.
  crush.
  crush.
  crush.
  intros.
Admitted.
(* 
  destruct p0.
  compute in H.
  crush.
  compute in H.
  crush.
Qed.  
*)
Lemma A_11_Heap_Object_Safety_3_induction_tests:
  forall (h : Heap) (u : Upsilon) (g : Gamma) 
         (x : EVar) (vhx v1 : E) (t1 t2: Tau) 
         (p1 p2 : Path),
    refp h u ->
    htyp u g h g ->
    H.map h x = Some vhx ->
    Value v1 ->
    get vhx p1 v1 ->
    rtyp D.empty u g v1 t1 ->
    gettype u x p1 t1 p2 t2 ->
    (exists (v2 : E),
       get vhx (p1 ++ p2) v2 /\ 
       rtyp D.empty u g v2 t2) /\
    (forall (v2' : E),
       Value v2' ->
       (exists (v1' : E),
          Value v1' ->
          set v1 p2 v2' v1')).
Proof.
Admitted. 
(*
  intros h u g x vhx v1 t1 t2 p1 p2.
  intros refpder htypder valv1 H.mapder getder rtypder.
  induction p2; try destruct a; try destruct i.
  Case "p2=[]".
   intros gettypeder.
   apply gettype_nil_path in gettypeder.
   crush.
   apply ex_intro with (x:=v1).
   split.
   SCase "get".
    rewrite app_nil_r.
    assumption.
    assumption.
   SCase "set".
    apply ex_intro with (x:=v1).
    intros.
    assert (E: v1 = v2').
    admit. (* TODO apply both halves of the theorem in this goal. *)
    rewrite E.
    constructor.
    assumption.
    assumption.
  Case "p = zero_pe :: p2".
   intros gettypeder.
   destruct t1. 
  (* Have to sequentially invert as this is unfolding some things we don't want.*)
  (* Just clearing meaningless goals. *)
   inversion gettypeder. 
   inversion gettypeder.   
   Focus 2.
   inversion gettypeder.
   Focus 2.
   inversion gettypeder.
   Focus 2.
   inversion gettypeder.
   (* Dan's one inversion is really three. *)
   destruct v1; inversion H.mapder; inversion rtypder. 
   (* And crush is unfolding a gettypeder. *)
   apply A_10_Path_Extension_1_A with (v0:=v1_1 ) (v1:=v1_2) in getder.

   admit.
   admit.
   constructor; assumption.
   reflexivity.
  Case "p = one_pe :: p2".
   admit.
  Case "p = u_pe :: p2".
   admit.
Admitted.

Check A_11_Heap_Object_Safety_3.
*)

Lemma A_11_Heap_Object_Safety_3_Corollary :
  forall (h : Heap) (u : Upsilon) (g : Gamma) 
         (x : EVar) (v1 : E) (t1 t2: Tau) 
         (p2 : Path),
    Value v1 ->
    refp h u ->
    htyp u g h g ->
    H.map h x = Some v1 ->
    get v1 [] v1 ->
    rtyp D.empty u g v1 t1 ->
    gettype u x [] t1 p2 t2 ->
    (exists (v2 : E),
       get v1 ([] ++ p2) v2 /\ 
       rtyp D.empty u g v2 t2) /\
    (forall (v2' : E),
       Value v2' ->
       (exists (v1' : E),
          Value v1' ->
          set v1 p2 v2' v1')).
Proof.
  intros h u g x v1 t1 t2 p2.
  intros valv1 refpder htypder getHmapder getder rtypder gettypeder.
  apply A_11_Heap_Object_Safety_3 with (h:=h) (x:=x) (t1:=t1);
    try assumption;
    try constructor;
    try assumption.
Qed.

(*
Lemma A_11_Heap_Object_Safety_4: 
  forall (h : Heap) (u : Upsilon) (g : Gamma) 
         (x : EVar) (vhx v1 : E) (t1 t2: Tau) 
         (p1 p2 : Path),
    Value v1 ->
    refp h u ->
    htyp u g h g ->
    H.map h x = Some vhx ->
    get vhx p1 v1 ->
    rtyp D.empty u g v1 t1 ->
    gettype u x p1 t1 p2 t2 ->
    (exists (v2 : E),
       get vhx (p1 ++ p2) v2 /\ 
       rtyp D.empty u g v2 t2) /\
    (forall (v2' : E),
       Value v2' ->
       (exists (v1' : E),
          Value v1' ->
          set v1 p2 v2' v1')) -> 
    ASGN [] t2 ->
    forall (p':P), 
      getU u x (p1++p2++p') = None.
Proof.
  (* By lemmas and case analysis on t2. *)
  intros h u g x vhx v1 t1 t2 p1 p2.
  intros valv1 refpder htypder H.mapder getder rtypder gettypeder.
  intros big.
  intros asgnder.
  intros p'.
  induction t2.
  Case "t2 = tvar t".
   inversion asgnder.
   assert (H1': getD [] t = None).
   apply getD_from_nil_None.
   rewrite H1 in H1'.
   inversion H1'.
  Case "t2 = cint".
   admit.
  Case "t2 = cross".
   admit.
  Case "t2 = arrow".
   admit.
  Case "t2 = ptype".
   admit.
  Case "t2 = utype".
   admit.
  Case "t2 = etype".
   admit.
Admitted.

(* TODO 
Lemma A_11_Heap_Object_Safety_5.
Admitted.
Lemma A_11_Heap_Object_Safety_5_Corollary.
Admitted.
*)

*)