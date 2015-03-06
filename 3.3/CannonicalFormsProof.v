(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Defining type safety, page 67.

*)

(* DONE *)
Require Export CpdtTactics.
Require Export Tacticals.
Require Export LanguageModuleDef.
Require Export StaticSemantics.

(* Wow, my first real proof! *)
Lemma A_9_Cannonical_Forms_1:
  forall (u : Upsilon) (g : Gamma) (v : E),
    Value v ->
    rtyp D.empty u g v cint ->
    exists z : Z, v = (i_e (i_i z)).
Proof.
  intros u g v valv.
  intros rtypder.
  destruct valv; inversion rtypder.
  exists z.
  reflexivity.
Qed.

Lemma A_9_Cannonical_Forms_2:
  forall (u : Upsilon) (g : Gamma) (v : E) (t0 t1 : Tau),
    Value v ->  
    rtyp D.empty u g v (cross t0 t1) ->
    exists (v0 v1 : E),
      Value v0 /\  Value v1 /\ v = (cpair v0 v1).
Proof.
  intros u g v t0 t1 valv.
  intros rtypder.
  destruct valv; inversion rtypder.
  exists v0.
  exists v1.
  eauto.
Qed.

Lemma A_9_Cannonical_Forms_3:
  forall (u : Upsilon) (g : Gamma) (v : E) (t0 t1 : Tau),
    Value v ->
    rtyp D.empty u g v (arrow t0 t1) ->
    exists (x : EVar) (s : St), 
      v = (f_e (dfun t0 x t1 s)).
Proof.
  intros u g v t0 t1 valv.
  intros rtypder.
  destruct valv; inversion rtypder.
  subst.
  exists x.
  exists s.
  reflexivity.
Qed.

Lemma A_9_Cannonical_Forms_4:
  forall (u : Upsilon) (g : Gamma) (v : E) (t' : Tau),
    Value v ->
    rtyp D.empty u g v (ptype t') ->
    exists (x : EVar) (p : Path),
      v = (amp (p_e x p)).
Proof.
  intros u g v t' valv.
  intros rtypder.
  destruct valv; inversion rtypder.
  subst.
  exists x.
  exists p.
  reflexivity.
Qed.


Lemma A_9_Cannonical_Forms_5:
  forall (u : Upsilon) (g : Gamma) (v : E) (tau' : Tau) (alpha : TVar)
         (k : Kappa),
    Value v ->
    rtyp D.empty u g v (utype alpha k tau') ->
    exists (f : F),
      v = (f_e (ufun alpha k f)).
Proof.
  intros u g v tau' alpha kappa valv.
  intros rtypder.
  destruct valv; inversion rtypder.
  subst.
  exists f.
  reflexivity.
Qed.

Lemma A_9_Cannonical_Forms_6:
  forall (u : Upsilon) (g : Gamma) (v : E) (tau' : Tau) (alpha : TVar)
         (k : Kappa),
    Value v ->
    rtyp D.empty u g v (etype witnesschanges alpha k tau') ->
    exists (tau'' : Tau) (v' : E),
      v = (pack tau'' v' (etype witnesschanges alpha k tau')).
Proof.
  intros u g v tau' alpha kappa valv.
  intros rtypder.
  destruct valv; inversion rtypder.
  subst.
  exists tau.
  exists v.
  reflexivity.
Qed.

Lemma A_9_Cannonical_Forms_7:
  forall (u : Upsilon) (g : Gamma) (v : E) (tau' : Tau) (alpha : TVar)
         (k : Kappa),
    Value v ->
    rtyp D.empty u g v (etype aliases alpha k tau') ->
    exists (tau'' : Tau) (v' : E),
      v = (pack tau'' v' (etype aliases alpha k tau')).
Proof.
  intros u g v tau' alpha kappa valv.
  intros rtypder.
  destruct valv; inversion rtypder.
  subst.
  exists tau.
  exists v.
  reflexivity.
Qed.
