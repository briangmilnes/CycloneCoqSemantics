Set Implicit Arguments.
Require Export LanguageModuleDef.

(* A mini K to work out context destructing induction. *)

Inductive K : Delta -> Tau -> Kappa -> Prop :=

 | K_int   : forall (d : Delta),
                  K d cint B

 | K_B     : forall (d : Delta) (alpha : TV.T),
               D.map d alpha = Some B ->
               K d (tv_t alpha) B

 | K_utype  : forall (d : Delta) (alpha : TV.T) (k : Kappa) (tau : Tau),
                   D.map d alpha = None -> 
                   K  (D.ctxt alpha k d) tau A ->
                   K d (utype alpha k tau) A.

Print K_ind.

Lemma first:
  forall (d : Delta) (alpha : TV.T) (k : Kappa) (tau : Tau), 
        K (D.ctxt alpha k d) tau k ->
        K d tau k.
Proof.
  intros d alpha k tau Kder.
  apply K_ind.
  admit. (* bug *)
  admit. (* bug *)
  admit. (* bug *)
Admitted.

Lemma second:
  forall (alpha : TV.T) (k : Kappa) (tau : Tau) (d : Delta),
        K (D.ctxt alpha k d) tau k ->
        K d tau k.
Proof.
  intros d alpha k tau Kder.
  apply (K_ind 
           (fun (d : Delta) (tau : Tau) (k : Kappa) =>
             K d tau k)).
  (* Show's bug but is solvable. *)
  intros.
  constructor.
  admit. (* bug *)
  admit. (* bug *)
  admit.
Admitted.


Definition K_ind2 := 
fun (P : Delta -> Tau -> Kappa -> Prop) 
    (f : forall d : Delta, P d cint B)
    (f0 : forall (d : Delta) (alpha : TV.T),
        D.map d alpha = Some B -> P d (tv_t alpha) B)
    (f1 : forall (d : Delta) (alpha : TV.T) (k : Kappa) (tau : Tau),
        D.map d alpha = None ->
        K (D.ctxt alpha k d) tau A ->
        P (D.ctxt alpha k d) tau A -> P d (utype alpha k tau) A) =>

fix F (d : Delta) (t : Tau) (k : Kappa) (k0 : K d t k) {struct k0} :
  P d t k :=
  match k0 in (K d0 t0 k1) return (P d0 t0 k1) with
  | K_int d0 => f d0
  | K_B d0 alpha e => f0 d0 alpha e
  | K_utype d0 alpha k1 tau e k2 =>
      f1 d0 alpha k1 tau e k2 (F (D.ctxt alpha k1 d0) tau A k2)
  end.

Check K_ind2
     : forall P : Delta -> Tau -> Kappa -> Prop,
       (forall d : Delta, P d cint B) ->
       (forall (d : Delta) (alpha : TV.T),
        D.map d alpha = Some B -> P d (tv_t alpha) B) ->
       (forall (d : Delta) (alpha : TV.T) (k : Kappa) (tau : Tau),
        D.map d alpha = None ->
        K (D.ctxt alpha k d) tau A ->
        P (D.ctxt alpha k d) tau A -> P d (utype alpha k tau) A) ->
       forall (d : Delta) (t : Tau) (k : Kappa), K d t k -> P d t k.


Require Import Coq.Logic.JMeq.
Require Import Coq.Program.Equality.

Lemma fourth:
  forall (d : Delta) (alpha : TV.T) (k : Kappa) (tau : Tau),
        K (D.ctxt alpha k d) tau k ->
        K d tau k.
Proof.
  intros d alpha k tau Kder.
  generalize_eqs Kder.
  dependent induction Kder; intros.

  constructor.

  simpl_one_JMeq.
  subst.
  pose proof H as H'.
  unfold D.ctxt in H.
  unfold D.map in H.
  fold D.map in H.
  case_eq(D.K_eq alpha0 alpha); intros; rewrite H0 in H.
  constructor; try assumption.
  admit. (* Duplication inversion ? *)
  constructor; try assumption.

  simpl_one_JMeq.
  subst.
  pose proof H as H'.
  unfold D.ctxt in H.
  unfold D.map in H.
  fold D.map in H.
  case_eq(D.K_eq alpha0 alpha); intros; rewrite H0 in H; try solve[inversion H].
  apply K_utype; try assumption.
  assert(Z: D.ctxt alpha0 k (D.ctxt alpha A d) ~= D.ctxt alpha A d).
  admit.
  apply IHKder in Z.
  admit. (* K r str *)
Admitted.
(* Cute but this requires Z which is false, so no applying the IH. *)


Goal forall n m:nat, ge (S n) m -> n >= m.
intros n m H.
generalize_eqs H.
generalize_eqs_vars H.
induction H.
Abort.

(* Bottom line, dependent induction does not work, I'll need to understand the
inductive hypothesis I need and see if can craft it. *)
