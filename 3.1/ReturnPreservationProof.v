(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Defining type safety, page 67.

*)
Set Implicit Arguments.
Require Export LanguageModuleDef.
Require Export Tacticals.
Require Export DynamicSemanticsTypeSubstitution.
Require Export DynamicSemanticsHeapObjects.
Require Export DynamicSemantics.
Require Export DynamicSemanticsTypeSubstitution.
Require Export StaticSemanticsKindingAndContextWellFormedness.
Require Export StaticSemantics.
Require Export SubstitutionsProof.
Require Export TypeSafety.
Require Export CpdtTactics.
Require Export Case.
(* Require Export SubstitutionsProof. *)

Lemma A_8_Return_Preservation:
  forall (s : St),
    ret s ->
    forall (h h' : Heap) (s' : St),
      S h s h' s' ->
      ret s'.
Proof.
  intros s retder.
  induction retder.
  (* Cases are all messed up due to quantifier changes! *)
  Case "retn e".
   intros h h' s' H.
   inversion H.
   subst.
   constructor.
  Case "if".
   intros h h' s' H.
   inversion H.
   SCase "if 0".
    rewrite <- H5.
    assumption.
   SCase "if <> 0".
    rewrite <- H5.
    assumption.
   SCase "if e->e'".
    constructor.
    SSCase "ret s1".
    assumption.
    SSCase "ret s2".
    assumption.
  Case "seq s1 s2".
   intros h h' s'0 H.
   inversion H.
   SCase "seq (e_s v) s'".
   subst.
   inversion retder. (* e_s v does not return. *)
   SCase "ret (retn v)".
   constructor.
   subst.
   SCase "(seq s1 s2) (seq s1' s2)".
   constructor.
   specialize (IHretder h h' s'1).
   apply IHretder in H5.
   assumption.
   SCase "ret (seq s'1 s)".
   intros h h' s'0 H.
   inversion H.
   crush.
   constructor.
   crush.
  Case "let".
   intros h h' s' H.
   inversion H.
   SCase "let s->s'".
   rewrite H5 in retder.
   assumption.
   SCase "let e->e'".
   constructor.
   exact retder.
   Case "open".
   intros h h' s' H.
   inversion H.
   constructor.
   crush.
   apply A_6_Substitution_6.
   assumption.

   SCase "ret (open e' alpha x s)".
   intros.
   constructor.
   assumption.

   Case "openstar".
   intros h h' s' H.
   inversion H.
   constructor.
   crush.
   apply A_6_Substitution_6.
   assumption.
   SCase "ret (open e' alpha x s)".
   crush.
Qed.

