(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Why can't I induct on K and keep d connected?

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.
Require Import Coq.Init.Logic.

Require Export FormalSyntax.
Require Export VarLemmas.
Require Export DynamicSemanticsTypeSubstitution.
Require Export DynamicSemanticsHeapObjects.
Require Export DynamicSemantics.
Require Export DynamicSemanticsTypeSubstitution.
Require Export StaticSemanticsKindingAndContextWellFormedness.
Require Export StaticSemantics.
Require Export TypeSafety.
Require Export ContextExtensionRelation.

Require Export CpdtTactics.
Require Export Case.
Require Export TacticNotations.


Require Export AlphaConversion.
Require Export GetLemmasRelation.

(* At this point I'm down to three possibilities that I should work in 
 parallel. At each step I should think at the type theory level.

 1) ExtendByD can be made to work.
 2) Extends1D with reflexivity.
 3) A different inductive schema. 
 4) Fully detailed paper proof.
 5) Destructing d' outside induction is good up to
    a false induction hypothesis, so it says the general extends case
    should be required.
*)


(*  1) ExtendByD can be made to work. *)
(* No looks like I can't do this with more than one step of extension. *)
Lemma A_6_Substitution_1_extendedby:
  forall (d d' : Delta) (t' : Tau) (k' : Kappa) (alpha : TVar) (k : Kappa),
    ExtendedByD d d' ->
    getD d' alpha = Some k ->
    getD d alpha = None ->
    K d' t' k' ->
    forall (t : Tau),
      AK d t k ->
      K d (subst_Tau t' t alpha) k'.
Proof.
  intros d d' t' k' alpha k ext getd'alphasomek getdalphanone Kder.
  K_ind_cases(induction Kder) Case.
  Case "K d cint B".
   intros.
   simpl.
   constructor.
  Case "K d (tv_t alpha) B".
   intros.
   simpl.
   case_eq (beq_tvar alpha alpha0).
    SCase "beq_tvar alpha alpha0 = true".
     intros.
     apply beq_tvar_eq in H1.
     rewrite H1 in *.
     clear H1.
     assert (Z: k = B).
     admit. (* Thesis argument seems to hold. *)
     rewrite Z in *.
     inversion H0; try assumption.
    SCase "beq_tvar alpha alpha0 = false".
     intros.
     assert (Z: getD d alpha0 = Some B).
     admit. (* No, single extension yes, big extension no. *)
     apply K_B; try assumption.
  Case "K d (ptype (tv_t alpha)) B".
   intros.
   simpl.
   case_eq (beq_tvar alpha alpha0).
    SCase "beq_tvar alpha alpha0 = true".
     intros.
     apply beq_tvar_eq in H1.
     rewrite H1 in *.
     apply K_ptype.
     inversion H0; try assumption.
     admit. (* ? *)
     crush.
     admit.
    SCase "beq_tvar alpha0 alpha = false".
     intros.
     assert (Z: getD d alpha0 = Some A).
     admit. (* Just wrong in the extends method, 
               right in the ([(alpha,k)] ++ d) method. *)
     (* So I either need another method here or I need the 
     ([(alpha,k)] ++ d) method. *)

     apply K_star_A; try assumption.
  Case "K d tau A".
   intros.
   apply K_B_A.
   apply IHKder with (t:= t) in ext; try assumption.
  Case "K d (cross t0 t1) A".
   intros.
   pose proof H as H'.
   apply IHKder1 with (t:= t) in H; try assumption.
   apply IHKder2 with (t:= t) in H'; try assumption.
   simpl.
   apply K_cross; try assumption.
  Case "K d (arrow t0 t1) A".
   intros.
   pose proof H as H'.
   apply IHKder1 with (t:= t) in H; try assumption.
   apply IHKder2 with (t:= t) in H'; try assumption.
   simpl.
   apply K_arrow; try assumption.
  Case "K d (ptype tau) B".
   intros.
   apply IHKder with (t:= t) in H; try assumption.
   simpl.
   apply K_ptype; try assumption.
  Case "K d (utype alpha k tau) A".
    intros.
    apply IHKder with (t:= t) in H1; try assumption.
    simpl.
    case_eq (beq_tvar alpha alpha0).
    SCase "beq_tvar alpha0 alpha = true".
     intros.
     AdmitAlphaConversion.
    SCase "beq_tvar alpha alpha0 = false".
     intros.
     apply K_utype; try assumption.
     admit. 
     (* WFD ([(alpha0, k0)] ++ d0) -> 
        ExtendedByD d d0 -> WFD ([(alpha0, k0)] ++ d) *)
     admit. 
    (* ExtendedByD d d0 ->
       getD d0 alpha0 = None 
       getD d alpha0 = None. *)
     admit.
    (* K_strenthening. *)
     admit. 
    (* ExtendedByD d d0 -> getD d0 alpha0 = None ->  ExtendedByD d d0 *)
     admit. (* getD some weakening. *)
  Case "K d (etype p alpha k tau) A)".
   admit.
Qed.



(* 

  3) A different inductive schema. 

*)

Print K_ind.

(*   5) Destructing d' outside induction.
 int, induction works.
*)

Lemma A_6_Substitution_1_destruct:
  forall (alpha : TVar) (d' d: Delta) (t' : Tau) (k : Kappa) (k' : Kappa),
    d' = ([(alpha,k)]) ++ d ->
    K d' t' k' ->
    forall (t : Tau),
      AK d t k ->
      K d (subst_Tau t' t alpha) k'.
Proof.
  intros alpha d' d t' k k' d'alphakd Kder.
  induction Kder.
 Case "K d cint B".
  intros.
  simpl.
  constructor.
 Case "K d (tv_t alpha) B".
  intros.
  simpl.
  case_eq (beq_tvar alpha alpha0).
   SCase "(beq_tvar alpha alpha0) = true".
    admit.
   SCase "(beq_tvar alpha alpha0) = false".
    intros.
    assert (Z: getD d alpha0 = Some B).
    admit. 
   (* d0 = [(alpha, k)] ++ d -> 
     getD d0 alpha0 = Some B ->
     beq_tvar alpha alpha0 = false -> 
     getD d alpha0 = Some B *)
    apply K_B; try assumption.
 Case "K d (ptype (tv_t alpha)) B".
  admit.
 Case "K d tau A".
  intros.
  apply IHKder with (t:= t) in d'alphakd; try assumption.
  constructor; try assumption.
 Case "K d (cross t0 t1) A".
  intros.
  pose proof d'alphakd as d'alphakd'.
  apply IHKder1 with (t:=t) in d'alphakd; try assumption.
  apply IHKder2 with (t:=t) in d'alphakd'; try assumption.
  simpl.
  apply K_cross; try assumption.
 Case "K d (arrow t0 t1) A".
  admit.
 Case "K d (ptype tau) B".
  admit.
 Case "K d (utype alpha k tau) A".
  rewrite d'alphakd in IHKder.
  (* False induction hypothese. FAIL. *)
  (* Or is this really the case that ++ is a list and NOT a partial function? *)
  case_eq (beq_tvar alpha alpha0).
  SCase "(beq_tvar alpha alpha0) = true".
   admit. (* Inversion WFD ([(alpha0, k0)] ++ d0) kills this case. *)
  SCase "(beq_tvar alpha alpha0) = false".   
   intros.
   assert (Z: [(alpha0, k0)] ++ [(alpha, k)] ++ d = [(alpha, k)] ++ d).
   admit. (* But false. *)
   apply IHKder with (t:= t) in Z; try assumption.
   simpl.
   rewrite H1.
   apply K_utype; try assumption.
   admit. (* WFD manip ok. *)
   admit. (* get manip ok. *)
   admit. (* K strengthening. *)
 Case "K d (etype p alpha k tau) A)".
  admit.
Qed.