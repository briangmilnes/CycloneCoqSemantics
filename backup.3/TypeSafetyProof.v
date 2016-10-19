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


Theorem Type_Safety :
(*   If ·; ·; ·; τ styp s, ret s, and ·; s → H ; s *)
 forall (s : St) (tau : Tau),
        styp [] [] [] tau s ->
        ret s ->
        exists (h' : H) (s' : St), 
           Sstar [] s h' s' -> 
           NotStuck h' s'.
Proof.
Admitted.

Lemma A_1_Context_Weakening_1:
  forall (d d' : Delta) (tau : Tau) (k : Kappa),
    K d tau k ->
    K (d ++ d') tau k.
Proof.
Admitted.

Lemma A_1_Context_Weakening_2:
  forall (u : Upsilon) (d : Delta) (tau : Tau) 
         (x : EVar) (p : P),
    WFU u ->
    getU u x p = Some tau ->
    K d tau A.
Proof.
Admitted.

Lemma A_2_Term_Weakening_1 :
  forall (d: Delta) (u u' : Upsilon) (g g' : Gamma)
         (x : EVar) (p p' : P) (tau tau' : Tau),
    WFC d (u ++ u') (g ++ g') ->
    gettype u x p tau p' = Some tau' ->
    gettype (u ++ u') x p tau p' = Some tau'.
Proof.
Admitted.

Lemma A_2_Term_Weakening_2 :
  forall (d: Delta) (u u' : Upsilon) (g g' : Gamma)
         (e : E) (tau : Tau),
    WFC d (u ++ u') (g ++ g') ->
    ltyp d u g e tau ->
    ltyp d (u ++ u') (g++g') e tau.
Proof.
Admitted.

Lemma A_2_Term_Weakening_3 :
  forall (d: Delta) (u u' : Upsilon) (g g' : Gamma)
         (e : E) (tau : Tau),
    WFC d (u ++ u') (g ++ g') ->
    rtyp d u g e tau ->
    rtyp d (u ++ u') (g++g') e tau.  
Proof.
Admitted.

Lemma A_2_Term_Weakening_4 :
  forall (d: Delta) (u u' : Upsilon) (g g' : Gamma)
         (s : St) (tau : Tau),
    WFC d (u ++ u') (g ++ g') ->
    styp d u g               tau s ->
    styp d (u ++ u') (g++g') tau s.
Proof.
Admitted.

Lemma A_3_Heap_Weakening_1:
  forall (u u' : Upsilon) (g g' g'': Gamma) (h : H),
   (WFC [] (u ++ u') (g ++ g') /\ htyp u g h g'') ->
    htyp (u ++ u') (g ++ g') h g''.
Proof.
Admitted.

Lemma A_3_Heap_Weakening_2:
  forall (u u' : Upsilon) (h h': H),
    refp h u ->
    refp (h ++ h') u.
Proof.
Admitted.

Lemma A_4_Useless_Substitutions_1:
  forall (d : Delta) (alpha : TVar) (tau tau' : Tau) (k : Kappa),
    getD d alpha = None ->
    K d tau' k ->
    subst_Tau tau' tau alpha = tau'.
Proof.
Admitted.    

Lemma A_4_Useless_Substitutions_2:
  forall (d : Delta) (alpha : TVar) (tau tau' : Tau) (g : Gamma),
    getD d alpha = None ->
    WFDG d g ->
    subst_Gamma g tau alpha = g.
Proof.
Admitted.    

Lemma A_4_Useless_Substitutions_3:
  forall (d : Delta) (alpha : TVar) (tau tau': Tau) (u : Upsilon) (p : P)
         (x : EVar),
    getD d alpha = None ->
    WFU u ->
    getU u x p = Some tau' ->
    subst_Tau tau' tau alpha = tau'.
Proof.
Admitted.    

(* TODO do I have the ordering right? *)
Lemma A_5_Commuting_Substitutions:
  forall (alpha beta : TVar) (t0 t1 t2 : Tau),
    NotFreeInTau beta t2 = true ->
    (subst_Tau (subst_Tau t0 t1 beta) t2 alpha) = 
    (subst_Tau (subst_Tau t0 t2 alpha)
              (subst_Tau t1 t2 alpha)
              beta).
Proof.
Admitted.

Lemma A_6_Substitution_1:
  forall (d : Delta) (alpha : TVar) (tau tau' : Tau) (k k': Kappa),
    AK d tau k -> 
    K (d ++ [(alpha,k)]) tau' k' ->
    K d (subst_Tau tau' tau alpha) k'.
Proof.
Admitted.    

Lemma A_6_Substitution_2:
  forall (d : Delta) (alpha : TVar) (tau tau' : Tau) (k k': Kappa),
    AK d tau k -> 
    K (d ++ [(alpha,k)]) tau' k' ->
    AK d (subst_Tau tau' tau alpha) k'.
Proof.
Admitted.    

Lemma A_6_Substitution_3:
  forall (d : Delta) (alpha : TVar) (tau tau' : Tau) (k : Kappa),
    AK d tau k -> 
    ASGN (d ++ [(alpha, k)]) tau' ->
    ASGN d (subst_Tau tau' tau alpha).
Proof.
Admitted.    

Lemma A_6_Substitution_4:
  forall (d : Delta) (alpha : TVar) (tau : Tau) (g : Gamma) (k : Kappa),
    AK d tau k -> 
    WFDG (d ++ [(alpha,k)]) g ->
    WFDG d (subst_Gamma g tau alpha).
Proof.
Admitted.    

Lemma A_6_Substitution_5:
  forall (d : Delta) (u : Upsilon ) (alpha : TVar) (tau : Tau) 
         (g : Gamma) (k : Kappa),
    AK d tau k -> 
    WFC (d ++ [(alpha,k)]) u g ->
    WFC d u (subst_Gamma g tau alpha).
Proof.
Admitted.    

Lemma A_6_Substitution_6:
  forall (d : Delta) (alpha : TVar) (tau : Tau) (s : St) (k : Kappa),
    AK d tau k -> 
    ret s ->
    ret (subst_St s tau alpha).
Proof.
Admitted.    

Lemma A_6_Substitution_7:
  forall (d: Delta) (u : Upsilon ) (alpha : TVar) (x : EVar) 
         (t1 t2 tau : Tau) (p p': P) (k : Kappa),
    AK d tau k -> 
    WFU u ->
    gettype u x p t1 p' = Some t2 ->
    gettype u x p (subst_Tau t1 tau alpha) p' = 
    Some (subst_Tau t2 tau alpha).
Proof.
Admitted.    

Lemma A_6_Substitution_8_1:
  forall (d : Delta) (alpha : TVar) (u : Upsilon) (g : Gamma) 
         (e : E) (tau tau' : Tau) (k : Kappa),
    AK d tau k ->
    ltyp (d ++ [(alpha,k)]) u g  e tau' ->
    ltyp d u (subst_Gamma g tau alpha)
              (subst_E e tau alpha)
              (subst_Tau tau' tau alpha).
Proof.
Admitted.    

Lemma A_6_Substitution_8_2:
  forall (d : Delta) (alpha : TVar) (u : Upsilon) (g : Gamma) 
         (e : E) (tau tau' : Tau) (k : Kappa),
    AK d tau k ->
    rtyp (d ++ [(alpha,k)]) u g  e tau' ->
    rtyp d u (subst_Gamma g tau alpha)
              (subst_E e tau alpha)
              (subst_Tau tau' tau alpha).
Proof.
Admitted.    

Lemma A_6_Substitution_8_3:
  forall (d : Delta) (alpha : TVar) (u : Upsilon) (g : Gamma) 
         (s : St) (tau tau' : Tau) (k : Kappa),
    AK d tau k ->
    styp (d ++ [(alpha,k)]) u g tau' s ->
    styp d u (subst_Gamma g tau alpha)
              (subst_Tau tau' tau alpha)
              (subst_St s tau alpha).
Proof.
Admitted.    

Lemma A_7_Typing_Well_Formedness_1 :
  forall (d: Delta) (u : Upsilon) (x : EVar) (tau tau' : Tau) (p p' : P),
    WFU u ->
    gettype u x p tau p' = Some tau' ->
    K d tau A ->
    K d tau' A.
Proof.
Admitted.

Lemma A_7_Typing_Well_Formedness_2 :
  forall (d: Delta) (g : Gamma) (u : Upsilon) (tau : Tau) (e : E),
  ltyp d u g e tau ->
  (WFC d u g /\ 
   K d tau A).
Proof.
Admitted.

Lemma A_7_Typing_Well_Formedness_3 :
  forall (d: Delta) (g : Gamma) (u : Upsilon) (tau : Tau) (e : E),
    rtyp d u g e tau ->
    (WFC d u g /\ 
     K d tau A).
Proof.
Admitted.

Lemma A_7_Typing_Well_Formedness_4 :
  forall (d: Delta) (g : Gamma) (u : Upsilon) (tau : Tau) (s : St),
    styp d u g tau s ->
    WFC d u g.
Proof.
Admitted.

Lemma A_7_Typing_Well_Formedness_5 :
  forall (d: Delta) (g : Gamma) (u : Upsilon) (tau : Tau) (s : St),
    styp d u g tau s ->
    ret s ->
    K d tau A.
Proof.
Admitted.

Lemma A_8_Return_Preservation:
  forall (s s' : St) (h h' : H),
  ret s ->
  S h s h' s' ->
  ret s'.
Proof.
Admitted.

Lemma A_9_Cannonical_Forms_1:
  forall (u : Upsilon) (g : Gamma) (v : E) (tau : Tau),
    rtyp [] u g v tau ->
    Value v ->
    tau = cint -> 
    exists z : Z, v = (i_e (i_i z)).
Proof.
Admitted.

Lemma A_9_Cannonical_Forms_2:
  forall (u : Upsilon) (g : Gamma) (v : E) (tau t0 t1 : Tau),
    rtyp [] u g v tau ->
    Value v ->  
    tau = (cross t0 t1) ->
    exists (v0 v1 : E),
      Value v0 /\  Value v1 /\ v = (cpair v0 v1).
Proof.
Admitted.

Lemma A_9_Cannonical_Forms_3:
  forall (u : Upsilon) (g : Gamma) (v : E) (tau t0 t1 : Tau),
    rtyp [] u g v tau ->
    Value v ->
    tau = (arrow t0 t1) ->
    exists (v0 v1 : E) (x : EVar) (s : St), 
      Value v0 /\  Value v1 /\ v = (f_e (dfun t0 x t1 s)).
Proof.
Admitted.

Lemma A_9_Cannonical_Forms_4:
  forall (u : Upsilon) (g : Gamma) (v : E) (tau t' : Tau),
    rtyp [] u g v tau ->
    Value v ->
    tau = (ptype t') ->
    exists (x : EVar) (p : P),
      v = (amp (p_e x p)).
Proof.
Admitted.

Lemma A_9_Cannonical_Forms_5:
  forall (u : Upsilon) (g : Gamma) (v : E) (tau tau' : Tau) (alpha : TVar)
         (k : Kappa),
    rtyp [] u g v tau ->
    Value v ->
    tau = (utype alpha k tau') ->
    exists (f : F),
      v = (f_e (ufun alpha k f)).
Proof.
Admitted.

Lemma A_9_Cannonical_Forms_6:
  forall (u : Upsilon) (g : Gamma) (v : E) (tau tau' : Tau) (alpha : TVar)
         (k : Kappa),
    rtyp [] u g v tau ->
    Value v ->
    tau = (etype nowitnesschange alpha k tau') ->
    exists (tau'' : Tau) (v' : E),
      Value v /\ 
      v = (pack tau'' v' (etype nowitnesschange alpha k tau')).
Proof.
Admitted.

Lemma A_9_Cannonical_Forms_7:
  forall (u : Upsilon) (g : Gamma) (v : E) (tau tau' : Tau) (alpha : TVar)
         (k : Kappa),
    rtyp [] u g v tau ->
    Value v ->
    tau = (etype aliases alpha k tau') ->
    exists (tau'' : Tau) (v' : E),
      Value v /\ 
      v = (pack tau'' v' (etype aliases alpha k tau')).
Proof.
Admitted.

(* Ask Dan about the we can not derive clauses. 
   If he uses them in proof they'd just be inversions. *)
Lemma A_10_Path_Extension_1_A:
  forall (v v0 v1 : E) (p : P),
    Value v ->
    Value v0 ->
    Value v1 -> 
    get v p (cpair v0 v1) ->
    get v (p ++ [i_pe (i_i 0)]) v0 /\ 
    get v (p ++ [i_pe (i_i 1)]) v1.
Proof.
Admitted.

(* TODO ask Dan, I don't trust this. *)
Lemma A_10_Path_Extension_1_B:
  forall (v v' v0 : E) (tau tau' : Tau) (alpha : TVar) (k : Kappa)
         (p : P),
    Value v' ->
    Value v0 ->
    v' = (pack tau' v0 (etype aliases alpha k tau)) ->
    get v (p ++ [u_pe]) v0.
Proof.
Admitted.

Lemma A_10_Path_Extension_2_A:
  forall (u : Upsilon) (x : EVar) (p p' : P) (t' tau t0 t1 : Tau),
    t' = (cross t0 t1) ->
    (gettype u x p tau (p' ++ [i_pe (i_i 0)]) = Some t0  /\
     gettype u x p tau (p' ++ [i_pe (i_i 1)]) = Some t1).
Proof.
Admitted.

Lemma A_10_Path_Extension_2_B:
  forall (u : Upsilon) (x : EVar) (p p' : P) (t' ut tau t0: Tau)
         (alpha : TVar) (k : Kappa),
    t' = (etype aliases alpha k t0) ->
    getU u x p = Some ut ->
    gettype u x p tau (p' ++ [u_pe]) = Some (subst_Tau t0 ut alpha).
Proof.
Admitted.

(* TODO are the orderings of quantifiers correct? *)
Lemma A_11_Heap_Object_Safety_1:
  forall (v1 : E) (p : P),
    Value v1 ->
    exists ! (v2 : E),
      Value v2 ->
      get v1 p v2.
Proof.
Admitted.

Lemma A_11_Heap_Object_Safety_2:
  forall (v0 v1 v2 : E) (p1 p2 : P),
    Value v0 ->
    Value v1 ->
    Value v2 ->
    (get v0 p1 v1 /\ get v0 (p1 ++ p2) v2) ->
    get v1 p2 v2.
Proof.
Admitted.

(* TODO is this the right formulation of the theorem ? *)
Lemma A_11_Heap_Object_Safety_3:
  forall (h : H) (u : Upsilon) (g : Gamma) 
         (x : EVar) (p1 p2 : P) (t1 t2 : Tau)
         (v1 v2 vhx : E),
    Value v1 ->
    Value v2 ->
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
Admitted.

(* TODO interesting, how to write this. *)
(*
Lemma A_11_Heap_Object_Safety_3_Corollary :
Proof.
Admitted.
*)

Inductive extends_Gamma : Gamma -> Gamma -> Prop := 
  | A_12_Extension_Gamma : 
      forall (g1 g2 : Gamma),
        (exists (g3 : Gamma), g2 = g1 ++ g3) ->
        extends_Gamma g2 g1.

Inductive extends_Upsilon : Upsilon -> Upsilon -> Prop := 
  | A_12_Extension_Upsilon : 
      forall (u1 u2 : Upsilon),
        (exists (g3 : Upsilon), u2 = u1 ++ g3) ->
        extends_Upsilon u2 u1.

Lemma A_13_Term_Preservation_1:
  forall (u : Upsilon) (g : Gamma) (e e' : E) (tau : Tau) (h h' : H),
    (ltyp [] u g e tau /\ L h (e_s e)  h' (e_s e')) ->
    exists (g' : Gamma) (u' : Upsilon),
      htyp u' g' h' g' /\ 
      refp h' u' /\
      ltyp [] u' g' e' tau.
Proof.
Admitted.

Lemma A_13_Term_Preservation_2:
  forall (u : Upsilon) (g : Gamma) (e e' : E) (tau : Tau) (h h' : H),
    (rtyp [] u g e tau /\ R h (e_s e)  h' (e_s e')) ->
    exists (g' : Gamma) (u' : Upsilon),
      htyp u' g' h' g' /\ 
      refp h' u' /\
      rtyp [] u' g' e' tau.
Proof.
Admitted.

Lemma A_13_Term_Preservation_3:
  forall (u : Upsilon) (g : Gamma) (s s': St) (tau : Tau) (h h' : H),
    (styp [] u g tau s /\ S h s  h' s') ->
    exists (g' : Gamma) (u' : Upsilon),
      htyp u' g' h' g' /\ 
      refp h' u' /\
      styp [] u' g' tau s'.
Proof.
Admitted.

Lemma A_14_Term_Progress_1:
  forall (g : Gamma) (u : Upsilon) (h : H) (e : E) (tau : Tau),
    (htyp u g h g /\ refp h u) ->
    (ltyp [] u g e tau -> 
     (exists (x : EVar) (p : P), e = (p_e x p) \/
      exists (h' : H) (e' : E),  L h (e_s e) h' (e_s e'))).
Proof.
Admitted.

Lemma A_14_Term_Progress_2:
  forall (g : Gamma) (u : Upsilon) (h : H) (e : E) (tau : Tau),
    (htyp u g h g /\ refp h u) ->
    (rtyp [] u g e tau -> 
     (Value e \/
      exists (h' : H) (e' : E),  R h (e_s e) h' (e_s e'))).
Proof.
Admitted.

Lemma A_14_Term_Progress_3:
  forall (g : Gamma) (u : Upsilon) (h : H) (s : St) (tau : Tau),
    (htyp u g h g /\ refp h u) ->
    (styp [] u g tau s -> 
     ((exists (v : E), Value v /\ (s = (e_s v) \/ s = retn v)) \/
      (exists (h' : H) (s' : St), S h s h' s'))).
Proof.
Admitted.
