(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Defining type safety, page 67.

*)

Set Implicit Arguments.
Set Implicit Arguments.
Require Export Cyclone_Formal_Syntax Cyclone_Static_Semantics_Kinding_And_Context_Well_Formedness.
Require Export Cyclone_Static_Semantics_Typing_Heap_Objects.
Require Export Cyclone_LN_Tactics Cyclone_LN_Extra_Lemmas_And_Automation.
Close Scope list_scope.
Import LibEnvNotations.
Import LVPE.LibVarPathEnvNotations.

Lemma A_1_Context_Weakening_1:
  forall (d : Delta) (tau : Tau) (k : Kappa),
    ok d -> 
    K d tau k ->
    forall (d' : Delta), 
      extends d d' ->
      ok d' ->
      K d' tau k.
Proof.
  introv okd Kdtk.
  induction Kdtk; intros;
   try solve[K_constructors; auto];
   try solve[constructor;
            apply extends_get with (d:=d); auto];
   try apply_fresh K_utype;
   try apply_fresh K_etype;
   assert(N: y \notin L);
   auto;
   intros;
   unfold fv_delta in Fry;
   assert(D: y # d'); auto;
   assert(E: ok (d & y ~ k)); auto;
   apply extends_push_both with (x:=y) (v:= k) in H1; auto.
Qed.  

Lemma A_1_Context_Weakening_2:
  forall (u : Upsilon),
    WFU u ->
    forall x p d tau, 
      ok d -> (* Thesis change *)
      LVPE.V.get (x,p) u = Some tau ->
      K d tau A.
Proof.
  lets PT: A_1_Context_Weakening_1.
  introv WFUu.
  induction WFUu; introv Okd G.
  rewrite LVPE.get_empty in G.
  inversion G.

  apply PT with (d:= empty) (d':= d); auto.
  rewrite LVPE.get_push in G.
  case_varpath.
  rewrite C in G.
  rewrite* If_l in G.
  inversion G.
  subst*.
  rewrite* If_r in G.
Qed.

(* I have to strengthen this to kill the Magic K or get it elsewhere. *)

Lemma A_1_Context_Weakening_2:
  forall (u : Upsilon),
    WFU u ->
    forall x p d tau, 
      ok d -> (* Thesis change *)
      LVPE.V.get (x,p) u = Some tau ->
      K d tau A.
Proof.
  lets PT: A_1_Context_Weakening_1.
  introv WFUu.
  induction WFUu; introv Okd G.
  rewrite LVPE.get_empty in G.
  inversion G.

  apply PT with (d:= empty) (d':= d); auto.
  rewrite LVPE.get_push in G.
  case_varpath.
  rewrite C in G.
  rewrite* If_l in G.
  inversion G.
  subst*.
  rewrite* If_r in G.
Qed.
