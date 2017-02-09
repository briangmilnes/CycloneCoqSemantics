(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION".   Daniel Grossman, August 2003 *)
(* Brian Milnes 2016 *)
(* Lemmas for get. *)

Set Implicit Arguments.
Require Import TLC.LibEnv LibVarPathEnv Cyclone_LN_Tactics Cyclone_Fset_Lemmas.
Require Import Cyclone_Admit_Environment.
Close Scope list_scope.
Import LibEnvNotations.
Import LVPE.LibVarPathEnvNotations.

Ltac get_empty:=
  match goal with
  | H: get _ empty = Some _ |- _ =>
    rewrite get_empty in H; inversion H
  end.

Ltac lvpe_get_empty:=
  match goal with
  | H: LVPE.V.get _ empty = Some _ |- _ =>
    rewrite LVPE.get_empty in H; inversion H
end.

Ltac simpl_get ::=
  (* idtac "simpl_get";*)
  trace_goal;
  timeout 2
  repeat
    match goal with
  | |- context [get ?a empty]           => trace_goal; rewrite~ get_empty
  | |- context [get ?a empty]           => trace_goal; rewrite~ get_empty  
  | |- context [get ?a empty]           => trace_goal; rewrite~ get_empty
  | |- context [get ?a (_ & (_ ~ _)) ]      => trace_goal;
    rewrite~ get_push; try repeat case_var~

  | |- context [get ?a ((?b ~ _) & _)] => trace_goal;
    rewrite~ get_concat; try repeat case_var~

  | |- context [get ?a _ = None] => trace_goal;
   apply* get_none

  | H: context[get _ empty = Some _] |- _ => 
    rewrite get_empty in H; inversion H
end.

Lemma get_fv_delta:
  forall v d k,
    get v d = Some k ->
    \{v} \c fv_delta d.
Proof.
  intros.
  unfold fv_delta.
  induction d using env_ind.
  rewrite get_empty in H.
  inversion H.
  rewrite get_push in H.
  case_var.
  inversion H.
  subst.
  rewrite dom_push.
  fset.
  apply IHd in H.
  rewrite dom_push.
  apply* subset_weakening.
Qed.
Ltac get_fv_delta :=
  match goal with 
  | H: get ?v ?d = Some ?k' |- \{?v} \c fv_delta ?d =>
    apply get_fv_delta with (k:= k'); assumption; auto with fset
end.                                                
Hint Extern 1 (\{_} \c fv_delta _) => get_fv_delta.
Hint Extern 1 (T.fv _ \c fv_delta _) => simpl; get_fv_delta.

Lemma get_dom:
  forall A alpha (d : env A)  k,
    get alpha d = Some k ->
    \{alpha} \c dom d.
Proof.
  intros.
  induction d using env_ind.
  rewrite get_empty in H.
  inversion H.
  destruct (classicT(alpha = x)).
  subst.
  rewrite dom_push.
  fset.
  rewrite get_push in H.
  rewrite* If_r in H.
  apply IHd in H.
  rewrite dom_push.
  apply* subset_weakening.
Qed.
Ltac get_dom :=
  match goal with
  | H: get ?a ?d = Some ?k' 
  |- \{?a} \c dom ?d =>
    apply get_dom with (k:= k')
  end.
Hint Extern 1 (\{_} \c dom _) => get_dom.

(* Arthur's binds theorems redone in get. *)

Section GetProperties.
Variable A B' : Type.
Implicit Types E F : env A.
Implicit Types x : var.
Implicit Types v : A.

(** Constructor forms *)

Lemma get_empty_inv : forall x v,
  get x empty = Some v -> False.
Proof using.
  introv H. rewrite get_empty in H. false.
Qed.

Lemma get_single_eq : forall x v,
  get x (x ~ v) = Some v.
Proof using.
  intros.  rewrite get_single. case_if~.
Qed.

Lemma get_single_inv : forall x1 x2 v1 v2,
  get x1 (x2 ~ v2) = Some v1 ->
  x1 = x2 /\ v1 = v2.
Proof using.
   introv H. rewrite get_single in H.
  case_if; inversions~ H.
Qed.

Lemma get_push_inv : forall x1 v1 x2 v2 E,
  get x1 (E & x2 ~ v2) = Some v1 ->
     (x1 = x2 /\ v1 = v2)
  \/ (x1 <> x2 /\ get x1 E = Some v1).
Proof using.
  introv H.  rewrite get_push in H. case_if.
  inverts~ H. auto.
Qed.

Lemma get_push_eq : forall x v E,
  get x (E & x ~ v) = Some v.
Proof using. intros.  rewrite get_push. case_if~. Qed.

Lemma get_push_eq_inv : forall x v1 v2 E,
  get x (E & x ~ v2) = Some v1 -> v1 = v2.
Proof using.
  introv H. forwards [|]: get_push_inv H. autos*. intros [? _]. false.
Qed.

Lemma get_push_neq_inv : forall x1 x2 v1 v2 E,
  get x1 (E & x2 ~ v2) = Some v1 -> x1 <> x2 -> get x1 E = Some v1.
Proof using.
  introv H. forwards [|]: get_push_inv H.
  intros [? ?] ?. false. autos*.
Qed.

Lemma get_tail : forall x v E,
  get x (E & x ~ v) = Some v.
Proof using. intros. rewrite get_push. cases_if~. Qed.

Lemma get_push_neq : forall x1 x2 v1 v2 E,
  get x1 E = Some v1 -> x1 <> x2 -> get x1 (E & x2 ~ v2) = Some v1.
Proof using.
  introv H N.  rewrite get_push. case_if~.
Qed.

Lemma get_concat_inv : forall x v E1 E2,
  get x (E1 & E2) = Some v ->
     (get x E2 = Some v)
  \/ (x # E2 /\ get x E1 = Some v).
Proof using.
  introv H. induction E2 using env_ind.
  rewrite~ concat_empty_r in H.
  rewrite concat_assoc in H.
   forwards [[? ?]|[? M]]: get_push_inv H.
     subst. left. apply get_tail.
     forwards [?|[? ?]]: IHE2 M.
       left. applys~ get_push_neq.
       right.
       auto.
Qed.

(* Typing env vs list issues. 
Lemma get_map : forall x v (f : A -> B) E,
  get x E = Some v -> get x (map f E) = Some (f v).
Proof using.
  introv H.  rew_env_defs.
  induction E as [|[x' v'] E']; simpls.
  false.
  cases_if~. inverts~ H.
Qed.
*)

Lemma get_func : forall x v1 v2 E,
  get x E = Some v1 -> get x E = Some v2 -> v1 = v2.
Proof using.
  introv H1 H2.
  induction E as [|E' x' v'] using env_ind.
  rewrite get_empty in H1. false.
  rewrite get_push in H1,H2. case_if~.
   inverts H1. inverts~ H2.
Qed.

Lemma get_fresh_inv : forall x v E,
  get x E = Some v -> x # E -> False.
Proof using.
  introv H F.
  induction E as [|E' x' v'] using env_ind.
  rewrite get_empty in H. false.
  rewrite get_push in H. case_if~. subst.
   simpl_dom; notin_false.
Qed.

(** Derived forms *)

Lemma get_single_eq_inv : forall x v1 v2,
  get x (x ~ v2) = Some v1 ->
  v1 = v2.
Proof using.
  introv H. rewrite get_single in H.
  case_if. inverts~ H.
Qed.

Lemma get_concat_left : forall x v E1 E2,
  get x E1 = Some v ->
  x # E2 ->
  get x (E1 & E2) = Some v.
Proof using.
  introv H F. induction E2 using env_ind.
  rewrite~ concat_empty_r.
  rewrite concat_assoc.
  applys~ get_push_neq.
  subst.
  simpl_dom.
  apply notin_union in F.
  inversion F.
  apply notin_singleton_r in H0; auto.
Qed.

Lemma get_concat_left_ok : forall x v E1 E2,
  ok (E1 & E2) ->
  get x E1 = Some v ->
  get x (E1 & E2) = Some v.
Proof using.
  introv O H. induction E2 using env_ind.
  rewrite~ concat_empty_r.
  rewrite concat_assoc in O|-*. lets [_ ?]: ok_push_inv O.
  applys~ get_push_neq. subst. 
  intro_subst.
  applys~ get_fresh_inv H.
Qed.

Lemma get_concat_left_inv : forall x v E1 E2,
  get x (E1 & E2) = Some v ->
  x # E2 ->
  get x E1 = Some v.
Proof using.
  introv H F. lets~ [M|[? ?]]: get_concat_inv H.
    false. applys~ get_fresh_inv M.
Qed.

Lemma get_concat_right : forall x v E1 E2,
  get x E2 = Some v ->
  get x (E1 & E2) = Some v.
Proof using.
  introv H. induction E2 using env_ind.
  false. apply get_empty_inv with (x:=x) (v:=v); auto.
  rewrite concat_assoc. lets [[? ?]|[? ?]]: get_push_inv H.
    subst. applys get_tail.
    applys* get_push_neq.
Qed.

Lemma get_concat_right_inv : forall x v E1 E2,
  get x (E1 & E2) = Some v ->
  x # E1 ->
  get x E2 = Some v.
Proof using.
  introv H F. lets~ [?|[? M]]: get_concat_inv H.
    false. applys~ get_fresh_inv M.
Qed.

Lemma get_middle_eq : forall x E1 E2 v,
  x # E2 ->
  get x (E1 & x ~ v & E2) = Some v.
Proof using.
  introv F. applys~ get_concat_left.
Qed.

(** Metatheory proof forms *)

(** Interaction between binds and the insertion of bindings.
  In theory we don't need this lemma since it would suffice
  to use the get_cases tactics, but since weakening is a
  very common operation we provide a lemma for it. *)

Lemma get_weaken : forall x a E F G,
  get x (E & G) = Some a -> ok (E & F & G) ->
  get x (E & F & G) = Some a.
Proof using.
  introv H O. lets [?|[? ?]]: get_concat_inv H.
    applys~ get_concat_right.
    applys~ get_concat_left. applys~ get_concat_left_ok.
Qed.

Lemma get_remove : forall E2 E1 E3 x v,
  get x (E1 & E2 & E3) = Some v ->
  x # E2 ->
  get x (E1 & E3) = Some v.
Proof using.
  introv H F. lets [?|[? M]]: get_concat_inv H.
    applys~ get_concat_right.
    forwards: get_concat_left_inv M; auto.
    applys~ get_concat_left.
Qed.

Lemma get_subst : forall x2 v2 x1 v1 E1 E2,
  get x1 (E1 & x2 ~ v2 & E2) = Some v1 ->
  x1 <> x2 ->
  get x1 (E1 & E2) = Some v1.
Proof using.
  introv H N.
  applys~ get_remove H. 
Qed.

Lemma get_middle_eq_inv : forall x E1 E2 v1 v2,
  get x (E1 & x ~ v2 & E2) = Some v1 ->
  ok (E1 & x ~ v2 & E2) ->
  v1 = v2.
Proof using.
  introv H O. lets [? ?]: ok_middle_inv O.
  forwards~ M: get_concat_left_inv H.
  applys~ get_push_eq_inv M.
Qed.

Lemma get_middle_inv : forall x1 v1 x2 v2 E1 E2,
  get x1 (E1 & x2 ~ v2 & E2) = Some v1 ->
     (get x1 E2 = Some v1)
  \/ (x1 # E2 /\ x1 = x2 /\ v1 = v2)
  \/ (x1 # E2 /\ x1 <> x2 /\ get x1 E1 = Some v1).
Proof using.
  introv H. lets [?|[? M]]: (get_concat_inv H).
    left~.
    right. lets [N|[? N]]: (get_concat_inv M).
      lets [? ?]: (get_single_inv N). subst~.
      right. simpl_dom. split~.
Qed.

Lemma get_not_middle_inv : forall x v E1 E2 E3,
  get x (E1 & E2 & E3) = Some v ->
  x # E2 ->
     (get x E3 = Some v)
  \/ (x # E3 /\ get x E1 = Some v).
Proof using.
  introv H F. lets [?|[? M]]: (get_concat_inv H).
    left~.
    right. forwards~ N: (get_concat_left_inv M).
Qed.

Lemma fv_in_values_get : forall y fv x v E,
  get x E = Some v -> y \notin fv_in_values fv E -> y \notin fv v.
Proof using.
  unfold fv_in_values. introv H.
  induction E using env_ind; introv M.
  false. apply get_empty_inv with (x:= x) (v:= v); auto.
  rewrite values_def in M,IHE.
  rewrite concat_def, single_def in M. rew_list in M. simpl in M.
  lets [[? ?]|[? ?]]: (get_push_inv H); subst~.
Qed.

End GetProperties.

Lemma ok_contradict:
  forall A (d : env A) alpha0 k' k, 
  ok (d & alpha0 ~ k') ->
  get alpha0 d  = Some k ->
  False.
Proof.
  introv okd getd.
  induction d using env_ind.
  rewrite get_empty in getd.
  inversion getd.
  destruct(classicT(x = alpha0)); subst.
  apply ok_push_inv  in okd.
  inversion okd.
  unfolds in H0.
  unfolds in H0.
  rewrite dom_push in H0.
  contradict H0.
  rewrite in_union.
  left.
  apply in_singleton_self.
  applys IHd; auto.
  rewrite get_push in getd.
  auto.
Qed.

Lemma get_strength:
  forall A alpha (d : env A) k, 
    get alpha d = Some k -> 
    forall alpha0 k',
      ok (d & alpha0 ~ k') ->
      get alpha (d & alpha0 ~ k') = Some k.
Proof.
  intros.
  inversion H0.
  apply empty_push_inv in H2.
  inversion H2.
  rewrite get_push.
  case_var*.
  apply eq_inversion_env in H1.
  inversions H1.
  inversions H5.
  apply ok_contradict with (k:= k) in H0; auto.
  inversion H0.
  apply eq_inversion_env in H1.
  inversions* H1.
Qed.
Ltac get_strength:=
  match goal with 
  | H: get ?alpha ?d = Some ?k |-
    get ?alpha (?d & _ ~ _) = Some ?k
    => apply* get_strength
end.
Hint Extern 2 (get _ (_ & _ ~ _) = Some _) => try get_strength.

Lemma get_middle_strength:
  forall A alpha0 (d : env A) alpha k d' k', 
    alpha0 <> alpha ->
    get alpha0 (d & alpha ~ k & d') = Some k' ->
    get alpha0 (d & d') = Some k'.
Admitted.

Lemma get_middle_k:
  forall A (d : env A) alpha k d',
    ok (d & alpha ~ k & d') ->
    forall k', 
      get alpha (d & alpha ~ k & d') = Some k' ->
      k = k'.
Admitted.

