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
Require Import Coq.Program.Equality.

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

Inductive K' : Delta -> Tau -> Kappa -> Prop :=
 | K'_int   : forall (d : Delta),
                  K' d cint B

 | K'_B     : forall (d : Delta) (alpha : TVar),
               getD d alpha = Some B ->
               K' d (tv_t alpha) B
 
(*
 | K_star_A  : forall (d : Delta) (alpha : TVar),
                 getD d alpha = Some A -> 
                 K'  d (ptype (tv_t alpha)) B.


 | K_B_A     : forall (d : Delta) (tau : Tau),
                  K'  d tau B ->
                  K'  d tau A
*)
 | K'_cross   : forall (d : Delta) (t0 t1 : Tau),
                    K' d t0 A ->
                    K' d t1 A ->
                    K' d (cross t0 t1) A.
(*
 | K_arrow   : forall (d : Delta) (t0 t1 : Tau),
                    K' d t0 A ->
                    K' d t1 A ->
                    K' d (arrow t0 t1) A

 | K_ptype    :  forall (d : Delta) (tau : Tau),
                    K' d tau A ->
                    K' d (ptype tau) B

 | K_utype  : forall (d : Delta) (alpha : TVar) (k : Kappa) (tau : Tau),
                   WFD ([(alpha, k)] ++ d) ->
                   getD d alpha = None -> 
                   K' ([(alpha, k)] ++ d) tau A ->
                   K' d (utype alpha k tau) A

 | K_etype  : forall (d : Delta) (alpha : TVar) (k : Kappa) (tau : Tau) (p : Phi),
                   WFD ([(alpha, k)] ++ d) ->
                   getD d alpha = None -> 
                   K' ([(alpha, k)] ++ d) tau A ->
                   K' d (etype p alpha k tau) A.
*)



Inductive AK' : Delta -> Tau -> Kappa -> Prop :=

 | AK'_AK_K  : forall (d : Delta) (tau : Tau) (k : Kappa),
                   K'  d tau k ->
                   AK' d tau k

 | AK'_A     : forall (d : Delta) (alpha : TVar),
                getD d alpha = Some A ->
                AK' d (tv_t alpha) A.

(* What's the smallest K_ind that will show me this bug? *)

Lemma minimally_broken_induction:
  forall (alpha : TVar) (k : Kappa) (d : Delta) (tau : Tau), 
    K' ([(alpha,k)] ++ d) tau k ->
    K' d tau k.
Proof.
  intros alpha k d tau K'der.
  induction K'der.
  Case "K d cint B".
   (* Good. *)
   admit.
  Case "K d (tv_t alpha) B".
   admit. (* disconnected. *)
   admit.
Qed.

Print K'_ind.

Definition K'_ind_saved := 
fun (P : Delta -> Tau -> Kappa -> Prop) (f : forall d : Delta, P d cint B)
  (f0 : forall (d : Delta) (alpha : TVar),
        getD d alpha = Some B -> P d (tv_t alpha) B)
  (f1 : forall (d : Delta) (t0 t1 : Tau),
        K' d t0 A -> P d t0 A -> K' d t1 A -> P d t1 A -> P d (cross t0 t1) A) =>
fix F (d : Delta) (t : Tau) (k : Kappa) (k0 : K' d t k) {struct k0} :
  P d t k :=
  match k0 in (K' d0 t0 k1) return (P d0 t0 k1) with
  | K'_int d0 => f d0
  | K'_B d0 alpha e => f0 d0 alpha e
  | K'_cross d0 t0 t1 k1 k2 => f1 d0 t0 t1 k1 (F d0 t0 A k1) k2 (F d0 t1 A k2)
  end.

Check K_B.

Definition K'_ind_2 := 
fun (P  : TVar -> Kappa -> Delta -> Tau -> Kappa -> Prop) 
    (f  : forall (alpha : TVar) (k : Kappa) (d : Delta), P alpha k d cint B)
    (f0 : forall (alpha : TVar) (k : Kappa) (d : Delta) (alpha0 : TVar), 
            getD d alpha0 = Some B -> 
            P alpha k d (tv_t alpha0) B) 
    (f1 : forall (alpha : TVar) (k : Kappa) (d : Delta) (t0 t1 : Tau),
        K' d t0 A -> P alpha k d t0 A -> K' d t1 A -> P alpha k d t1 A ->
         P alpha k d (cross t0 t1) A) =>
fix F (alpha : TVar) (k1 : Kappa) (d : Delta) (t : Tau) (k2 : Kappa) (k0 : K' d t k2)
    { struct k0} :
  P alpha k1 d t k2 :=
match k0 in (K' d0 t0 k2) return (P alpha k1 d0 t0 k2) with
| K'_int x => f alpha k1 x
| K'_B d' a' getd => f0 alpha k1 d' a' getd
| K'_cross d0 t0 t1 k1' k2' => 
   f1 alpha k1 d0 t0 t1 k1' (F alpha k1 d0 t0 A k1') k2' (F alpha k1 d0 t1 A k2')
end.

Check K'_ind_2.

Lemma minimally_broken_induction_with_handmade_induction:
  forall (alpha : TVar) (k1 : Kappa) (d : Delta) (tau : Tau) (k2: Kappa), 
    K' ([(alpha,k1)] ++ d) tau k2 ->
    K' d tau k2.
Proof.
  intros alpha k1 d tau k2 K'der.
  apply (K'_ind_2 
           (fun (alpha : TVar) (k1 : Kappa) (d : Delta) (tau : Tau) (k2: Kappa) =>
              K' ([(alpha,k1)] ++ d) tau k2 ->
              K' d tau k2))
        with (alpha := alpha) (k1:= k1).
  Case "K d cint B".
   (* Good. *)
   admit.
  Case "K d (tv_t alpha) B".
   intros.
   admit.
  Case "K d (cross t0 t1) A".
   intros.
   (* ?   H : K' d0 t0 A and H1 : K' d0 t1 A *)
   admit.
  Case "K' d tau k2".
   admit.
  Case "base".
   assumption.
Qed.

(* I'm absolutely not sure I'm building this right until I apply it in the 
right inductive form.  But its building interesting cases. 
*)


Lemma A_6_Substitution_1_my_induction:
  forall (d : Delta) (tau : Tau) (k1 : Kappa),
      AK' d tau k1 -> 
      forall (alpha : TVar) (k2 : Kappa) (tau' : Tau), 
        K' ([(alpha,k1)] ++ d) tau' k2 ->
        K' d (subst_Tau tau' tau alpha) k2.
Proof.
  intros d tau k1 AKder alpha k2 tau' Kder.
  apply (K'_ind_2 
           (fun (alpha : TVar) (k1 : Kappa) (d : Delta) (tau' : Tau) (k2: Kappa) =>
              K' ([(alpha,k1)] ++ d) tau' k2 ->
              K' d (subst_Tau tau' tau alpha) k2))
        with (k1:= k1).
  Case "K d cint B".
   intros.  
   simpl.
   constructor.
  Case "K d (tv_t alpha) B".
   intros.
   admit.
  Case "K d (cross t0 t1) A".
   intros.
   simpl.
   inversion H3.
   apply H0 in H7.
   apply H2 in H8.
   constructor; try assumption.
  Case "K' d tau k2".
   (* Unprovable! Darn. *)

   admit.
  Case "assumption".
   assumption.
Qed.


Lemma A_6_Substitution_1_dep_destruction:
  forall (d : Delta),
      forall (alpha : TVar) (k1 : Kappa) (k2 : Kappa) (tau' : Tau), 
        K' ([(alpha,k1)] ++ d) tau' k2 ->
        forall (tau : Tau),
          AK' d tau k1 -> 
          K' d (subst_Tau tau' tau alpha) k2.
Proof.
  intros d alpha k1 k2 tau' Kder.
  dependent induction Kder.
  Case "K d cint B".
   intros.  
   simpl.
   constructor.
  Case "K d (tv_t alpha) B".
   intros.
   admit.
  Case "K d (cross t0 t1) A".
   intros.
   simpl.
   constructor; try assumption.

Qed.

Lemma A_6_Substitution_1_full_extends:
  forall (d : Delta),
      forall (alpha : TVar) (k1 : Kappa) (k2 : Kappa) (tau' : Tau), 
        K' ([(alpha,k1)] ++ d) tau' k2 ->
        forall (tau : Tau),
          AK' d tau k1 -> 
          K' d (subst_Tau tau' tau alpha) k2.
Proof.