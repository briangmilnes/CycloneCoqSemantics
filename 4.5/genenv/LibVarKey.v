(**************************************************************************
* TLC: A library for Coq                                                  *
* Keys for environment signature. 
**************************************************************************)

Set Implicit Arguments.
Require Import TLC.LibTactics TLC.LibList TLC.LibLogic TLC.LibNat TLC.LibEpsilon TLC.LibReflect TLC.LibFset.
Require Export LibKeyType.

Module VarKey <: KeyType.

Definition key := nat.

Lemma key_inhab : Inhab key.
Proof using. apply (prove_Inhab 0). Qed.

Lemma key_comp : Comparable key.
Proof using. apply nat_comparable. Qed.

Instance key_comparable : Comparable key := key_comp.

Definition keys := fset key.

Definition key_gen_list (l : list nat) :=
  1 + fold_right plus O l.

Lemma key_gen_list_spec : forall n l,
  n \in from_list l -> n < key_gen_list l.
Proof using.
  unfold key_gen_list. induction l; introv I.
  rewrite from_list_nil in I. false (in_empty_elim I).
  rewrite from_list_cons in I. rew_list.
   rewrite in_union in I. destruct I as [H|H].
     rewrite in_singleton in H. subst. nat_math.
     specializes IHl H. nat_math.
Qed.

Definition key_gen (E : keys) : key :=
  key_gen_list (epsilon (fun l => E = from_list l)).

Lemma key_gen_spec : forall E, (key_gen E) \notin E.
Proof using.
  intros. unfold key_gen. spec_epsilon as l.
  applys fset_finite. rewrite Hl. introv H.
  forwards M: key_gen_list_spec H. nat_math.
Qed.

Lemma key_fresh : forall (L : keys), { x : key | x \notin L }.
Proof using. intros L. exists (key_gen L). apply key_gen_spec. Qed.

Hint Extern 1 (fresh _ _ _ _) => simpl.
Lemma key_freshes : forall L n,
  { xs : list key | fresh key L n xs }.
Proof using. 
 intros. gen L. induction n; intros L.
  exists* (nil : list key).
  destruct (key_fresh L) as [x Fr].
   destruct (IHn (L \u \{x})) as [xs Frs].
   exists* (x::xs).
Qed.

End VarKey.
