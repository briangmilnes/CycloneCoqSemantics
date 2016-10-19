Set Implicit Arguments.
Require Import LibTactics LibOption LibList LibProd LibLogic LibReflect LibNat LibEpsilon.
Require Import List.
Export ListNotations.
Require Export LibVar.
Generalizable Variable A.

Module Export VariablePath : VariablesType.

Check nat.

Inductive IPE: Type :=
 | zero_pe    
 | one_pe.

Inductive PE : Type := 
 | i_pe      : IPE -> PE
 | u_pe      : PE.

Definition Path : Type := list PE.

(* I'm making a new Var for this path and it ain't going to work. *)
Definition varpath := prod nat Path.
Definition var     := varpath.
Check (0, [i_pe zero_pe]) : var.

Lemma var_inhab : Inhab var.
Proof. apply (prove_Inhab (0, [i_pe zero_pe])). Qed.

Function beq_ipe (i i' : IPE) : bool := 
  match i, i' with
    | zero_pe, zero_pe => true
    | one_pe, one_pe => true
    | _, _ => false
  end.

Function beq_pe (p p' : PE) : bool :=
  match p, p' with
    | i_pe x, i_pe y => beq_ipe x y
    | u_pe, u_pe => true
    | _, _ => false
  end.

Function beq_path (p q : Path) : bool := 
  match p, q with
    | [], [] => true
    | x :: p', y :: q' => andb (beq_pe x y) (beq_path p' q')
    | _  , _ => false
  end.

Function varpath_compare (u u' : varpath) : bool := 
  match u, u' with
    | (x,p), (x', p') => If x = x' then beq_path p p' else false
  end.


Instance varpath_comparable : Comparable nat.
Proof.
  apply (comparable_varpath_compare varpath_compare).
  induction x; destruct y; simpl.
  auto*.
  auto_false.
  auto_false.
  asserts_rewrite ((S x = S y) = (x = y)).
    extens. iff; omega.
  auto*.
Qed.

Lemma varpath_comp : Comparable varpath.
Proof. apply varpath_comparable. Qed.

Instance var_comparable : Comparable var := var_comp.

Definition vars := fset var.

Definition var_gen_list (l : list nat) :=
  1 + fold_right plus O l.

Lemma var_gen_list_spec : forall n l,
  n \in from_list l -> n < var_gen_list l.
Proof.
  unfold var_gen_list. induction l; introv I.
  rewrite from_list_nil in I. false (in_empty_elim I).
  rewrite from_list_cons in I. rew_list.
   rewrite in_union in I. destruct I as [H|H].
     rewrite in_singleton in H. subst. nat_math.
     specializes IHl H. nat_math.
Qed.

Definition var_gen (E : vars) : var :=
  var_gen_list (epsilon (fun l => E = from_list l)).

Lemma var_gen_spec : forall E, (var_gen E) \notin E.
Proof.
  intros. unfold var_gen. spec_epsilon as l.
  applys fset_finite. rewrite Hl. introv H.
  forwards M: var_gen_list_spec H. nat_math.
Qed.

Lemma var_fresh : forall (L : vars), { x : var | x \notin L }.
Proof. intros L. exists (var_gen L). apply var_gen_spec. Qed.

End VariablePath.

