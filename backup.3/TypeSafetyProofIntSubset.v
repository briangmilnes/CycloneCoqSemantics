(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  The trivial subset of the language. 

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.
Require Import CpdtTactics.

Require Export FormalSyntax.
Require Export DynamicSemanticsTypeSubstitution.
Require Export DynamicSemanticsHeapObjects.
Require Export DynamicSemantics.
Require Export DynamicSemanticsTypeSubstitution.
Require Export StaticSemanticsKindingAndContextWellFormedness.
Require Export StaticSemantics.
Require Export TypeSafetyProof.

(* The smallest trivial subset that I can think of, integer with 
 the return statement. *)
(* This may not really work without subsetting I also.
   These have to be mutually recursive. *)

Fixpoint IntSubsetTau (tau : Tau) :=
  match tau with
    | cint => True
    | _ => False
  end.
Fixpoint IntSubsetI    (i : I)        := True.
Fixpoint IntSubsetEVar (x : EVar)     := False.
Fixpoint IntSubsetTVar (alpha : TVar) := False.

Fixpoint IntSubsetF (f : E) := False.

Fixpoint IntSubsetE (e : E) :=
  match e with 
    | i_e i => IntSubsetI i
    | _ => False
  end.

Fixpoint IntSubsetSt (s : St) :=
  match s with
    | (retn e) => IntSubsetE e
    | (e_s e) => IntSubsetE e
    | _ => False
  end.

(* I'm first searching through the theorems to get each type of
  simultaneous induction and setting up their apply. *)

Theorem Type_Safety_Int :
 forall (s : St) (tau : Tau),
   styp [] [] [] tau s ->
   IntSubsetSt s ->
   IntSubsetTau tau ->
   ret s ->
   exists (h' : H) (s' : St), 
     Sstar [] s h' s' -> 
     NotStuck h' s'.
Proof.
 Definition Thm (s : St) (tau : Tau) : Prop := 
    (IntSubsetSt s ->
     IntSubsetTau tau ->
     ret s ->
     exists (h' : H) (s' : St), 
       Sstar [] s h' s' -> 
       NotStuck h' s').
  intros s tau.
  (* This works without the subsetting. *)
  apply (Term_ind_mutual
           (fun (s : St) =>  
              forall (tau : Tau) (ts : (styp [] [] [] tau s)), 
                Thm s tau)
           (fun (e : E ) =>
              forall (tau : Tau) (ts : (styp [] [] [] tau (e_s e))),
                Thm (e_s e) tau)
           (fun (f : F) =>
              forall (ts : (styp [] [] [] tau (e_s (f_e f)))),
                Thm (e_s (f_e f)) tau));
        repeat (unfold Thm; crush).
  (* Case (retn (e_s e)). *)
  destruct e; crush.
  apply ex_intro with (x:= []).
  apply ex_intro with (x:= (retn (i_e i))).
  intros Ss.
  eauto with Chapter3.
  (* Bug 38, IIsAValue too specific. *)
  (* Case (e_s (i_e i)), no return no go. *)
  inversion H1.
Qed. 

(* Mutual Induction on *typ. *)
(* Hmm, this is really A.7 2,3,4 but missing ret. *)
(* Perhaps this is close. *)
Lemma A_7_Typing_Well_Formedness_2 :
  forall (d: Delta) (g : Gamma) (u : Upsilon) (tau : Tau) (e : E),
    ltyp d u g e tau ->
    IntSubsetE e ->
    IntSubsetTau tau ->
    (WFC d u g /\ 
     K d tau A).
Proof.
  intros d g u tau e.
  apply (typ_ind_mutual
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (t: Tau) (s: St)  (st : styp d u g t s) =>
              IntSubsetE e ->
              IntSubsetTau tau ->
              (WFC d u g /\ K d tau A))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) (lt : ltyp d u g e t) =>
              IntSubsetE e ->
              IntSubsetTau tau ->
              (WFC d u g /\ K d tau A))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) (rt : rtyp d u g e t) =>
              IntSubsetE e ->
              IntSubsetTau tau ->
              (WFC d u g /\ K d tau A)));
    crush.
Admitted.

(*
Check R_ind.
Check L_ind.
Check S_ind.

(* Pretty deep printing depth is required. *)
Set Printing Depth 80.
Check R_ind_mutual.
Check S_ind_mutual.
Check L_ind_mutual.
Check SLR_ind_mutual.
*)

(* Mutual induction on the S/R/L. *)
Lemma A_8_Return_Preservation:
  forall (s s' : St) (h h' : H),
    ret s ->
    S h s h' s' ->
    IntSubsetSt s ->
    ret s'.
Proof.
  intros s s' h h'.
  intros rets.
  apply (SLR_ind_mutual
           (fun (h : H) (s : St) (h' : H) (s' : St) (rd : R h s h' s') =>
              IntSubsetSt s -> 
              ret s')
           (fun (h : H) (s : St) (h' : H) (s' : St) (sd : S h s h' s') =>
              IntSubsetSt s -> 
              ret s')
           (fun (h : H) (s : St) (h' : H) (s' : St) (ld : L h s h' s') =>
              IntSubsetSt s -> 
              ret s')); intros; crush; eauto with Chapter3.
  eauto with Chapter3.
  apply ret_ret. (* TODO Why will ret not apply, it's in Tacticals. *)
Qed.