(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Defining type safety, page 67.

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.
Require Import Coq.Init.Logic.

Require Export FormalSyntax.
Require Export DynamicSemanticsTypeSubstitution.
Require Export DynamicSemanticsHeapObjects.
Require Export DynamicSemantics.
Require Export DynamicSemanticsTypeSubstitution.
Require Export StaticSemanticsKindingAndContextWellFormedness.
Require Export StaticSemantics.
Require Export TypeSafety.
Require Export CpdtTactics.
Require Export Case.

(* Bug, Miswrote theorem. I like the forall quantified version although
   I can naturally express this with exists.  *)
(* This is not the right induction just whacking a length on it. *)
(* I need to induct on path extension, perhaps reverse paths? *)

Functional Scheme rev_ind := Induction for rev Sort Prop.

Lemma A_11_Heap_Object_Safety_1:
  forall (v1 : E),
      forall (p : P) (v2 : E) (v3 : E),
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
  forall (v0 : E) (p1 : P) (v1 : E),
    Value v0 ->
    Value v1 ->
    get v0 p1 v1 ->
    forall (p2 : P) (v2 : E),
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
    SCase "p1 is nil".

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
  forall (h : H) (u : Upsilon) (g : Gamma) 
         (x : EVar) (vhx v1 : E) (t1 t2: Tau) 
         (p1 p2 : P),
    refp h u ->
    htyp u g h g ->
    getH h x = Some vhx ->
    get vhx p1 v1 ->
    rtyp [] u g v1 t1 ->
    gettype u x p1 t1 p2 = Some t2 ->
    (exists (v2 : E),
       get vhx (p1 ++ p2) v2 /\ 
       rtyp [] u g v2 t2) /\
    (forall (v2' : E),
       Value v2' ->
       (exists (v1' : E),
          Value v1' ->
          set v1 p2 v2' v1')).
Proof.
  intros h u g x vhx v1 t1 t2 p1 p2.
  induction p2. (* TODO is functional induction rev better? *)
  (* crush adds 2 goals. *)
  Case "p2 = []".
  intros.
  Focus 2.
  destruct a.
  crush.
Admitted.


(* Just instantiating the above at H(x) = v and p1 = nil. *)
(* Dan, is U; \Gamma supposed to be \Upsilon ; \Gamma ? *)
Lemma A_11_Heap_Object_Safety_3_Corollary :
  forall (h : H) (u : Upsilon) (g : Gamma) 
         (x : EVar) (p2 : P) (t1 t2 : Tau)
         (v1 v2 vhx : E),
    refp h u ->
    htyp u g h g ->
    getH h x = Some v1 ->
    get vhx [] v1 ->
    rtyp [] u g v1 t1 ->
    gettype u x [] t1 p2 = Some t2 ->
    (exists (v2 : E),
       get vhx ([] ++ p2) v2 /\ 
       rtyp [] u g v2 t2) /\
    (forall (v2' : E),
       Value v2' ->
       (exists (v1' : E),
          Value v1' ->
          set v1 p2 v2' v1')).
Proof.
  (* Prove using A_11_Heap_Object_Safety_3 *)
Admitted.

Lemma A_11_Heap_Object_Safety_4: 
  forall (h : H) (u : Upsilon) (g : Gamma) 
         (x : EVar) (vhx v1 : E) (t1 t2: Tau) 
         (p1 p2 : P),
    refp h u ->
    htyp u g h g ->
    getH h x = Some vhx ->
    get vhx p1 v1 ->
    rtyp [] u g v1 t1 ->
    gettype u x p1 t1 p2 = Some t2 ->
    ASGN [] t2 ->
    (exists (v2 : E),
       get vhx (p1 ++ p2) v2 /\ 
       rtyp [] u g v2 t2) /\
    (forall (v2' : E),
       Value v2' ->
       (exists (v1' : E),
          Value v1' ->
          set v1 p2 v2' v1')).
Proof.
  (* By lemmas and case analysis on t2. *)

Admitted.

(* TODO write lemma 5
Lemma A_11_Heap_Object_Safety_5.
*)
