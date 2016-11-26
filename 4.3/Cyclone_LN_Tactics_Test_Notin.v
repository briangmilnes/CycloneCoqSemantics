(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION".   Daniel Grossman, August 2003 *)
(* Testing the notin solver as it's failing for on Lambda_JAR
  cases in my version but working in Arthur's. *)
(* Brian Milnes 2016 *)

Set Implicit Arguments.
Require Export Cyclone_Type_Substitution Cyclone_LN_FV Cyclone_LN_LC_Body Cyclone_LN_Open_Close Cyclone_LN_Tactics Cyclone_LN_FSET Cyclone_LN_Tactics.
Open Scope cyclone_scope.

(*
 Go through the pick_fresh types one by one and make sure
 I'm getting the right variable sets. And then setup a lemma
 proving false with one admit. If something fails the lemmas
 will fail.

 Testing through falsehood.
*)


Lemma test_notin_vars: 
  forall (a b : var),
    forall a',
      a' = \{a} \u \{b} ->
      False.
Proof.
  intros.
  pick_fresh y.
  assert(y \notin \{a}).
  intuition eauto.
  assert(y \notin \{b}).
  intuition eauto.
  assert(y \notin \{a} \u \{b}).
  intuition eauto.
  admit.
Qed.

Lemma test_notin_var:
  forall (a : var),
    a = a ->
    False.
Proof.
  intros.
  pick_fresh y.
  assert(y \notin \{a}).
  auto.
  admit.
Qed.

Lemma test_notin_t:
  forall (a : var) t,
    t = (ftvar a) ->
    False.
Proof.
  intros.
  pick_fresh y.
  assert(y \notin \{a}).
  auto.
  assert(y \notin ftv_t t).
  rewrite~ H.
  admit.
Qed.

Lemma test_notin_t_tm:
  forall (a b : var) t,
    t = (term_e
           (f_e (dfun (ftvar a) (ftvar a) (e_s (v_e (fevar b)))))) ->
    False.
Proof.
  intros.
  pick_fresh y.
  assert(y \notin \{a}).
  intuition eauto.
  assert(y \notin ftv_tm t).
  rewrite~ H.
  assert(y \notin fv_tm t).
  rewrite~ H.
  admit.
Qed.

Lemma test_notin_fv_delta_abstract:
  forall (alpha: var) (d : Delta),
    d = single alpha A ->
    False.
Proof.
  intros.
  pick_fresh z.
  assert(z \notin \{alpha}).
  auto.
  assert(z \notin (ftv_delta d)).
  auto.
  admit.
Qed.

Lemma test_notin_ftv_delta_concrete:
  forall (alpha: var) (d D : Delta),
    d = D & (single alpha A) ->
    False.
Proof.
  intros.
  pick_fresh z.
  assert(z \notin \{alpha}).
  auto.
  assert(z \notin (ftv_delta d)).
  auto.
  assert(z \notin (ftv_delta D)).
  auto.  
  admit.
Qed.

Lemma test_notin_fv_heap:
  forall (x y : var) (h : Heap),
    h = single x (v_e (fevar y)) ->
    False.
Proof.
  intros.
  pick_fresh z.
  assert(z \notin \{x}).
  auto.
  assert(z \notin fv_heap h).
  auto.

  admit.
Qed.

