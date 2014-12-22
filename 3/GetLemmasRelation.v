(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Useful lemmas about get functions. 

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.

Require Import FormalSyntax.
Require Import VarLemmas.
Require Import ListLemmas.
Require Import StaticSemanticsKindingAndContextWellFormedness.

Lemma getD_None_Strengthening: 
  forall (d d' : Delta) (alpha : TVar),
    getD (d ++ d') alpha = None ->
    getD d alpha = None.
Proof.
 intros.
 induction d.
 Case "d = []".
  simpl.
  destruct alpha.
  reflexivity.
 Case "a :: d".
  destruct a.
  unfold getD.
  fold getD.
  unfold getD in H.
  simpl in H.
  fold getD in H.
  destruct (beq_tvar alpha t).
  inversion H.
  apply IHd in H.
  assumption.
Qed.

Lemma getG_None_Strengthening: 
  forall (g g' : Gamma) (x : EVar),
    getG (g ++ g') x = None ->
    getG g x = None.
Proof.
 intros.
 induction g.
 Case "g = []".
  simpl.
  destruct x.
  reflexivity.
 Case "a :: g".
  destruct a.
  unfold getG.
  fold getG.
  rewrite cons_is_append_singleton in H.
  rewrite <- app_assoc in H.
  case_eq (beq_evar x e).
  intros.
  inversion H.
  rewrite H0 in H2.
  inversion H2.
  intros.
  unfold getG in H.
  simpl in H.
  fold getG in H.
  rewrite H0 in H.
  apply IHg in H.
  assumption.
Qed.

Lemma getD_Some_Weakening:
 forall (alpha : TVar) (k : Kappa) (d d' : Delta),
   WFD (d ++ d') ->
   getD d alpha = Some k ->
   getD (d ++ d') alpha = Some k.
Proof.
  intros alpha k d d' WFDder getDder.
  functional induction (getD d alpha); crush.
  inversion WFDder.
  apply IHo in H3.
  assumption.
  assumption.
Qed.

(* TODO strengthen this with WFCDG or build a WFG? *)
Lemma getG_Some_Weakening:
 forall (x: EVar) (tau : Tau) (g g' : Gamma),
   getG g x = Some tau ->
   getG (g ++ g') x = Some tau.
Proof.
  intros x tau g g' getGder.
  functional induction (getG g x); crush.
Qed.

(* Not used yet. *)
Lemma getD_Some_None_Implies_Different_Variables:
  forall (alpha : TVar) (d : Delta) (n : nat) (k : Kappa),
      getD d (tvar n ) = Some k ->
      forall (n' : nat),
        getD d (tvar n') = None ->
        beq_nat n' n = false.
Proof.
  intros alpha d n k getDder.
  induction (cons (alpha,k) d); crush.
  (* TODO It's true but how to show it? *)
Admitted.

Lemma getD_Some_non_empty_d:
  forall (d : Delta) (alpha : TVar) (k : Kappa),
    getD d alpha = Some k ->
    d <> [].
Proof.
  intros d alpha k getDder.
  crush.
Qed.