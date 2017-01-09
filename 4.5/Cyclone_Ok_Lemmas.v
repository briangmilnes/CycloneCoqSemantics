(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Term Weakening 

*)

Set Implicit Arguments.
Require Export TLC.LibEnv.
Require Export Cyclone_Formal_Syntax Cyclone_LN_Env.
Close Scope list_scope.
Import LibEnvNotations.

Lemma ok_strength:
  forall d,
    ok d ->
    forall alpha,
      alpha \notin fv_delta d ->
      forall k,
        ok(d & alpha ~ k).
Proof.
  auto.
Qed.
Hint Resolve ok_strength.

Lemma ok_change_k:
  forall (d : env Kappa) alpha k,
    ok (d & alpha ~ k) ->
    forall k', 
      ok (d & alpha ~ k').
Proof.
  introv OKd. intros.
  constructor*.
  inversion OKd.
Admitted.
  