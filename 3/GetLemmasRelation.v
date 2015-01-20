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
Require Import StaticSemanticsKindingAndContextWellFormedness.
Require Import VarLemmas.
Require Import ListLemmas.
Require Import ContextExtensionRelation.

Lemma getU_Some_Weakening:
  forall (u : Upsilon) (x : EVar) (p : P) (tau : Tau),
    getU u x p tau ->
    forall (u' : Upsilon),
      getU (u ++ u') x p tau.
Proof.
  intros u x p tau getUder.
  induction u.
  Case "[]".
   inversion getUder.
  Case "a :: u".
   intros u'.
   destruct a.
   destruct p0.
   inversion getUder.
   constructor.
   constructor.
   assumption.
   crush.
Qed.

(* TODO must be strengthened with WFDG and even WFDG d? *)
Lemma getG_weakening:
 forall (g : Gamma) (x : EVar) (tau : Tau),
   getG g x = Some tau ->
   (* WFDG [] g ->  *)
   forall (g' : Gamma),
     (* WFDG [] (g ++ g') -> *)
    getG (g ++ g') x = Some tau.
Proof.
Admitted.

Lemma getH_Some_weakening:
  forall (h : H) (x : EVar) (v : E),
    getH h x = Some v -> 
    forall (h' : H),
      getH (h ++ h') x = Some v.
Proof.
  intros h x v getHder.
  functional induction (getH h x); crush.
Qed.

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

Lemma getG_Some_Weakening:
 forall (x: EVar) (tau : Tau) (g g' : Gamma),
   getG g x = Some tau ->
   getG (g ++ g') x = Some tau.
Proof.
  intros x tau g g' getGder.
  functional induction (getG g x); crush.
Qed.

Lemma getD_Some_non_empty_d:
  forall (d : Delta) (alpha : TVar) (k : Kappa),
    getD d alpha = Some k ->
    d <> [].
Proof.
  intros d alpha k getDder.
  crush.
Qed.

Lemma getD_extension_agreement:
  forall (d : Delta) (alpha : TVar) (k : Kappa),
    getD d  alpha = Some k ->
    WFD d ->
    forall (d' : Delta),
      WFD d' ->
      ExtendedByD d d' ->
      getD d' alpha = Some k.
Proof.
  (* Laphroig 10 year. *)
  intros d alpha k.
  functional induction (getD d alpha).
  Case "Some k0 = k0".
   intros.
   apply beq_tvar_eq in e1.
   inversion H.
   rewrite <- e1 in H2.
   rewrite <- e1 in H0.
   rewrite H4 in H2.
   rewrite H4 in H0.
   inversion H2.
   assumption.
  Case "getD d' alpha = Some k".
   intros.
   inversion H0.
   inversion H2.
   apply IHo with (d'0 := d'0) in H; try assumption.
  Case "None = Some".
   intros.
   inversion H.
Qed.

Lemma getD_extension_agreement_fun:
  forall (d : Delta) (alpha : TVar) (k : Kappa),
    getD d alpha = Some k ->
  forall (d' : Delta),
    WFD d' ->
    ExtendedByD d d' ->
    getD d' alpha = Some k.
Proof.
  intros d alpha k.
  functional induction (getD d alpha).
  intros.
  Case "alpha = b".
   apply beq_tvar_eq in e1.
   inversion H1.
   rewrite <- H2 in H1.
   rewrite <- H2 in H6.
   inversion H.
   rewrite H9 in H1.
   crush.
  Case "?".
   intros.
   apply IHo with (d'0:= d'0) in H; try assumption.
   inversion H1.
   assumption.
  Case "false".
   intros.
   inversion H.
Qed.

Lemma Duplicate_Alpha_implies_not_WFD:
  forall (d' : Delta) (alpha : TVar) (k k' : Kappa),
    getD d' alpha = Some k -> 
    ~ WFD ((alpha,k') :: d').
Proof.
  intros d' alpha k k' getDder.
  unfold not.
  intros WFDder.
  inversion WFDder.
  rewrite H1 in getDder.
  inversion getDder.
Qed.

Lemma getD_weakening:
  forall (d : Delta) (alpha beta : TVar),
    getD d alpha = None -> 
    getD d beta = None ->
    (beq_tvar beta alpha) = false -> (* Alpha Conversion. *)
    forall (k : Kappa),
      getD ([(alpha, k)] ++ d) beta = None.
Proof.
  intros.
  induction d.
  Case "[]".
   rewrite app_nil_r.
   unfold getD.
   rewrite H1.
   reflexivity.
 Case "a :: d".
  destruct a.
  unfold getD in H.
  fold getD in H.
  unfold getD in H0.
  fold getD in H0.
  case_eq (beq_tvar alpha t).
  intros.
  rewrite H2 in H.
  inversion H.
  intros.
  rewrite H2 in H.
  case_eq (beq_tvar beta t).  
  intros.
  rewrite H3 in H0.
  inversion H0.
  intros.
  rewrite H3 in H0.
  apply IHd in H; try assumption.
  simpl.
  case_eq (beq_tvar beta alpha).
  intros.
  inversion H4.
  rewrite H1 in H4.
  discriminate.
  intros.
  rewrite H3.
  assumption.
Qed.

Lemma getD_alpha_some_beta_none:
  forall (d : Delta) (alpha : TVar) (k : Kappa),
    getD d alpha = Some k ->
    forall (beta : TVar),
      getD d beta  = None ->
      beq_tvar alpha beta = false.
Proof.
  intros.
  induction d.
  Case "[]".
   inversion H.
  Case "a :: d".
   case_eq a.
   intros.
   crush.
   case_eq (beq_tvar alpha t); case_eq (beq_tvar beta t); case_eq (beq_tvar alpha beta); intros; try reflexivity.
   (* four contradictions to invert away. *)
   rewrite H2 in H0.
   inversion H0.
   apply beq_tvar_eq in H1.
   apply beq_tvar_eq in H3.
   apply beq_tvar_neq in H2.
   rewrite H1 in H3.
   congruence.

   apply beq_tvar_eq in H1.
   apply beq_tvar_eq in H2.
   apply beq_tvar_neq in H3.
   rewrite H1 in H3.
   congruence.

   (* Can't discriminate away on this on variables.  *)
   rewrite H3 in H.
   rewrite H2 in H0.
   apply IHd in H; try assumption.
   congruence.
Qed.
