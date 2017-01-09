(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

   Some subset lemmas. 

*)

Set Implicit Arguments.
Require Export TLC.LibEnv.
Require Export Cyclone_LN_Tactics.

Close Scope list_scope.
Import LibEnvNotations.

Lemma subset_weakening:
  forall A (a : fset A) b c,
    a \c c ->
    a \c b \u c.
Proof.
  intros.
  unfolds.
  unfolds in H.
  intros.
  apply H in H0.
  rewrite in_union.
  right.
  auto.
Qed.

(* Bug: ask Arthur. *)
Lemma singleton_empty:
  forall A (v :A),
    \{v} = \{} -> False.
Proof.
  Locate Is_empty_eq.
  Locate is_empty_eq_from_in_empty_eq.
  About is_empty_eq_from_in_empty_eq.
Admitted. 

Lemma contained_in_empty:
  forall A (s : fset A),
    s \c \{} ->
    s = \{}.
Proof.
  intros.
  assert(\{} \c s); auto with fset.
  apply* fset_extens.
Qed.

Lemma subset_union_l:
  forall A (l1 l2 : fset A) r,
    l1 \c r ->
    l2 \c r ->
    l1 \u l2 \c r.
Proof.
  intros.
  apply subset_union_2 with (E1:= l1) (F1:= r) in H0; auto.
  rewrite union_same in H0; auto.
Qed.
Hint Extern 3 (_ \u _ \c _) => apply subset_union_l.

Lemma subset_remove_r:
  forall A (a : A) b c,
    a <> b ->
    \{a} \c \{b} \u c ->
    \{a} \c c.
Proof.
  intros.
  unfold subset.
  intros.
  unfold subset in H0.
  specialize (H0 x H1).
  rewrite in_union in H0.
  inversion H0.
  rewrite in_singleton in H2; subst.
  rewrite in_singleton in H1.
  subst.
  congruence.
  auto.
Qed.
Ltac subset_remove_r :=
  match goal with
    | H : ?a <> ?b, I: \{?a} \c \{?b} \u _ |-\{?a} \c ?c => apply subset_remove_r with (b:=b)
  end.
Hint Extern 1 (\{_} \u _) => subset_remove_r.

Lemma subset_remove_l_r:
  forall A (B : fset A) C D,
    B \u C \c D ->
    B \c D.
Proof.
  intros.
  unfold subset.
  unfold subset in H.
  intros.
  specialize (H x).
  applys H.
  rewrite in_union.
  left*.
Qed.

Lemma subset_remove_l_l:
  forall A (B : fset A) C D,
    B \u C \c D ->
    C \c D.
Proof.
  intros.
  unfold subset.
  unfold subset in H.
  intros.
  specialize (H x).
  applys H.
  rewrite in_union.
  right*.
Qed.

Lemma union_middle_r:
  forall A (B : fset A) C D,
    B \u C \u D = B \u D \u C.
Proof.
  intros.
  rewrite union_comm with (F:= D); auto.
Qed.

Lemma union_middle_shuffle:
  forall A (B : fset A) C D,
    B \u C \u D \u C = B \u D \u C.
Proof.
  intros.
  rewrite union_comm with (F:= D \u C).
  rewrite <- union_assoc.
  rewrite* union_same.
Qed.