(**************************************************************************
* TLC: A library for Coq                                                  *
* Keys for environment signature. 
**************************************************************************)

Set Implicit Arguments.
Require Import TLC.LibTactics TLC.LibList TLC.LibLogic TLC.LibNat TLC.LibEpsilon TLC.LibReflect TLC.LibFset.
Require Export LibKeyType LibVarPath LibFresh.
Require Export LibVarKey.
Module VarPathKey <: KeyType.

Definition key := varpath.

Fixpoint varpath_compare (x y : varpath) :=
  match x, y with
    | (x,xp), (y, yp) =>
      If x = y then
       (If xp = yp then true else false)
    else false
  end.

Instance key_comparable : Comparable varpath.
Proof using.
  applys (comparable_beq varpath_compare).
  induction x; destruct y; simpl; autos*; auto_false.
  destruct (classicT (a = v)); destruct (classicT (b = p)); split; 
  intros; subst; try solve [auto | inversion H | congruence].
Qed.

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

Print keys.
Print key.
Print varpath.
Print map.
Function to_list (E : keys) : list key :=
  match E with
  | empty => nil
  end.

Print map.
Print VarKey.keys.
Print VarKey.key.
(* Bug Annoying type opacity. *)
Definition key_gen (E : keys) : key :=
  let newvar := VarKey.key_gen (from_list (map fst (to_list E))) in
   (newvar,nil).

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

Instance key_inhab : Inhab varpath.
Proof using.
 intros. 
 lets P: (key_fresh \{}).
 inversion P.
 apply (prove_Inhab (x, (cons u_pe nil))).
Qed.

End VarPathKey.
