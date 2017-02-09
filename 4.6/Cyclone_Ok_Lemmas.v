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

Lemma ok_pop:
  forall A (d : env A) alpha k,
    ok (d & alpha ~ k) ->
    alpha # d.
Proof.
  introv okd.
  inversion okd.
  apply empty_push_inv in H0.
  inversion H0.
  apply eq_push_inv in H.
  inversions H.
  inversions* H3.
Qed.
Ltac ok_pop :=
  match goal with
  | H: ok (?d & ?alpha ~ ?k') |- ?alpha # ?d
   => apply ok_pop with (k:=k'); auto
  end.
Hint Extern 1 (_ # _) => try ok_pop.
  
Lemma ok_fresh:
  forall A (d : env A) alpha k,
    ok(d & alpha ~ k) ->
    alpha \notin dom d.
Proof.
  introv okd.
  induction d using env_ind.
  auto.
  apply ok_pop in okd; auto.
Qed.
Hint Resolve ok_fresh.