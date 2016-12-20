(**************************************************************************
* TLC: A library for Coq                                                  *
* Environments for metatheory                                             *
* Adapted for xp var path environments, Upsilon.
**************************************************************************)

(* Questions:
  I could have generalized env to be (V : Type) (A : ValueType) but I didn't
 want to mess up automation on envs until I really understand it.
 
 Also I may need a different signature to get variables, not just variable paths
  out at different points.

  2 theorems failing but overloaded LTac which is not ideal.
 
  The theorems that fail are about freshness, which is to be expected, as I 
 have no idea what freshness issues we really need to solve on this context.

*)

Set Implicit Arguments.

Require Import TLC.LibTactics TLC.LibOption TLC.LibList TLC.LibProd TLC.LibLogic TLC.LibReflect.
Require Export TLC.LibVar.
Require Export LibVarPath.

Module LVPE.


(* ********************************************************************** *)
(** * Definition of environments and their basic operations *)

(** To avoid definitions being unfolded by [simpl] in an uncontrollable
    manner, we use a module signature to enforce abstraction *)


(* ---------------------------------------------------------------------- *)
(** ** Abstract definitions *)

Generalizable Variable A.

Definition varpathenv (A:Type) := list (varpath * A).
Definition varpaths := fset varpath.

Module Type VarPathEnvOpsSig.

Section Definitions.
Variable A B : Type.

Parameter empty : varpathenv A.
Parameter empty_def : empty = nil.

Parameter single : varpath -> A -> varpathenv A.
Parameter single_def :
  single = fun x v => (x,v)::nil.

Parameter concat : varpathenv A -> varpathenv A -> varpathenv A.
Parameter concat_def :
  concat = fun E F => F ++ E.

Parameter singles : list varpath -> list A -> varpathenv A.
Parameter singles_def :
  singles = fun xs vs =>
    fold_right (fun p acc => concat acc (single (fst p) (snd p))) empty (combine xs vs).

Parameter keys : varpathenv A -> list varpath.
Parameter keys_def :
  keys = map fst.

Parameter values : varpathenv A -> list A.
Parameter values_def :
  values = map snd.

Parameter fold_vars : (A -> varpaths) -> varpathenv A -> varpaths.
Parameter fold_vars_defs :
  fold_vars = fun fv E =>
    fold_right (fun v acc => fv v \u acc) \{} (values E).

Parameter dom : varpathenv A -> varpaths.
Parameter dom_def :
  dom = fold_right (fun p E => \{fst p} \u E) \{}.

Parameter dom' : varpathenv A -> vars.
Parameter dom'_def :
  dom' = fold_right (fun p E => \{fst (fst p)} \u E) \{}.

Parameter map : (A -> B) -> varpathenv A -> varpathenv B.
Parameter map_def :
  map = fun f E =>
    LibList.map (fun p => (fst p, f (snd p))) E.

Parameter map_keys : (varpath -> varpath) -> varpathenv A -> varpathenv A.
Parameter map_keys_def :
  map_keys = fun f E =>
    LibList.map (fun p => (f (fst p), snd p)) E.

Parameter get : varpath -> varpathenv A -> option A.
Fixpoint get_impl (k : varpath) (E : varpathenv A) {struct E} : option A :=
  match E with
  | nil => None
  | (x,v) :: E' => If k = x then Some v else get_impl k E'
  end.
Parameter get_def :
  get = get_impl.

End Definitions.

Implicit Arguments empty [A].

End VarPathEnvOpsSig.


(* ---------------------------------------------------------------------- *)
(** ** Concrete definitions *)

Module Export V : VarPathEnvOpsSig.

Section Concrete.
Variable A B : Type.

Definition empty : varpathenv A := nil.
Lemma empty_def : empty = nil.
Proof using. reflexivity. Qed.

Definition single x v : varpathenv A := (x,v)::nil.
Lemma single_def :
  single = fun x v => (x,v)::nil.
Proof using. reflexivity. Qed.

Definition concat (E F : varpathenv A) := F ++ E.
Lemma concat_def :
  concat = fun E F => F ++ E.
Proof using. reflexivity. Qed.

Definition singles (xs : list varpath) (vs : list A) : varpathenv A :=
  fold_right (fun p acc => concat acc (single (fst p) (snd p))) empty (combine xs vs).
Lemma singles_def :
  singles = fun xs vs =>
   fold_right (fun p acc => concat acc (single (fst p) (snd p))) empty (combine xs vs).
Proof using. reflexivity. Qed.

Definition keys : varpathenv A -> list varpath :=
  map fst.
Lemma keys_def :
  keys = map fst.
Proof using. reflexivity. Qed.

Definition values : varpathenv A -> list A :=
  map snd.
Lemma values_def :
  values = map snd.
Proof using. reflexivity. Qed.

Definition fold_vars (fv : A -> varpaths) (E : varpathenv A) :=
  fold_right (fun v acc => fv v \u acc) \{} (values E).
Lemma fold_vars_defs :
  fold_vars = fun fv E => fold_right (fun v acc => fv v \u acc) \{} (values E).
Proof using. reflexivity. Qed.

Definition map (f:A->B) (E:varpathenv A) :=
  LibList.map (fun p => (fst p, f (snd p))) E.
Lemma map_def :
  map = fun f E => LibList.map (fun p => (fst p, f (snd p))) E.
Proof using. reflexivity. Qed.

Definition map_keys (f:varpath->varpath) (E:varpathenv A) :=
  LibList.map (fun p => (f (fst p), snd p)) E.
Lemma map_keys_def :
  map_keys = fun f E => LibList.map (fun p => (f (fst p), snd p)) E.
Proof using. reflexivity. Qed.

Definition dom : varpathenv A -> varpaths :=
  fold_right (fun p E => \{fst p} \u E) \{}.
Lemma dom_def :
  dom = fold_right (fun p E => \{fst p} \u E) \{}.
Proof using. reflexivity. Qed.

Definition dom' : varpathenv A -> vars :=
  fold_right (fun p E => \{fst (fst p)} \u E) \{}.
Lemma dom'_def :
  dom' = fold_right (fun p E => \{fst (fst p)} \u E) \{}.
Proof using. reflexivity. Qed.

Fixpoint get_impl (k : varpath) (E : varpathenv A) {struct E} : option A :=
  match E with
  | nil => None
  | (x,v) :: E' => If k = x then Some v else get_impl k E'
  end.
Definition get := get_impl.
Lemma get_def :
  get = get_impl.
Proof using. reflexivity. Qed.

End Concrete.

Implicit Arguments empty [A].

End V.

(* ---------------------------------------------------------------------- *)
(** ** Notations *)
Module LibVarPathEnvNotations.

(** [x ~p a] is the notation for a singleton environment mapping x to a. *)

Notation "x '~p' a" := (single x a)
  (at level 7, left associativity) : env_scope.

(** [xs ~p* vs] is the notation for [single_iter xs vs]. *)

Notation "xs '~p*' vs" := (singles xs vs)
  (at level 27, left associativity) : env_scope.

(** [E p& F] is the notation for concatenation of E and F. *)

Notation "E '&p' F" := (concat E F)
  (at level 28, left associativity) : env_scope.

(** [x p# E] to be read x fresh from E captures the fact that
    x is unbound in E . *)

Notation "x '#p' E" := (x \notin (dom E)) (at level 67) : env_scope.

Bind Scope env_scope with varpathenv.
Delimit Scope env_scope with varpathenv.
Open Scope env_scope.
End LibVarPathEnvNotations. 
Import LibVarPathEnvNotations. 

(* ---------------------------------------------------------------------- *)
(** ** Additional definitions *)

Section MoreDefinitions.
Variable A : Type.
Implicit Types E F : varpathenv A.

(** Well-formed environments contains no duplicate bindings. *)

Inductive okp : varpathenv A -> Prop :=
  | okp_empty :
      okp empty
  | okp_push : forall E x v,
      okp E -> x #p E -> okp (E &p x ~p v).

(** An environment contains a binding from x to a iff the most recent
  binding on x is mapped to a *)

Definition binds x v E :=
  get x E = Some v.

(** Read the value associated to a bound variable *)

Definition get_or_arbitrary `{Inhab A} x (E:varpathenv A) :=
  unsome (get x E).

(** Inclusion of an environment in another one. *)

Definition extends E F :=
  forall x v, binds x v E -> binds x v F.

(** Gathering free variables contained in the keys of an environment *)

Definition fv_in_keys (fv: varpath ->vars) (E:varpathenv A) :=
  fold_right (fun v L => (fv v) \u L) \{} (keys E).

(** Gathering free variables contained in the values of an environment *)

Definition fv_in_values (fv:A->vars) (E:varpathenv A) :=
  fold_right (fun v L => (fv v) \u L) \{} (values E).

End MoreDefinitions.


(* ---------------------------------------------------------------------- *)
(** ** Basic Properties *)

Hint Rewrite empty_def single_def concat_def singles_def keys_def values_def
  dom_def map_def map_keys_def get_def : env_defs.

Ltac rew_env_defs := autorewrite with env_defs in *.

Section Properties.

Variable A B : Type.
Implicit Types k x : varpath.
Implicit Types v : A.
Implicit Types E F G : varpathenv A.
Implicit Types f : A -> B.
Implicit Types r : varpath -> varpath.

Lemma cons_to_push : forall x v E,
  (x, v) :: E = E &p x ~p v.
Proof using. intros. rew_env_defs. rew_app~. Qed.

Lemma env_ind : forall (P : varpathenv A -> Prop),
  (P empty) ->
  (forall E x v, P E -> P (E &p x ~p v)) ->
  (forall E, P E).
Proof using.
  rew_env_defs. induction E as [|(x,v)].
  auto. forwards*: H0 IHE.
Qed.

Lemma map_empty : forall f,
  map f empty = empty.
Proof using. intros. rew_env_defs. auto. Qed.
Lemma map_single : forall f x v,
  map f (x ~p v) = (x ~p (f v)).
Proof using. intros. rew_env_defs. auto. Qed.
Lemma map_concat : forall f E F,
  map f (E &p F) = (map f E) &p (map f F).
Proof using.
  intros. rew_env_defs.
  gen E. induction F as [|(x,v)]; intros.
  rew_list~.
  rew_list. fequals.
Qed.
Lemma map_push : forall f x v E,
  map f (E &p x ~p v) = (map f E) &p (x ~p (f v)).
Proof using. intros. rewrite map_concat, map_single. auto. Qed.

Lemma map_keys_empty : forall r,
  map_keys r (@empty A) = empty.
Proof using. intros. rew_env_defs. auto. Qed.
Lemma map_keys_single : forall r x v,
  map_keys r (x ~p v) = ((r x) ~p v).
Proof using. intros. rew_env_defs. auto. Qed.
Lemma map_keys_concat : forall r E F,
  map_keys r (E &p F) = map_keys r E &p map_keys r F.
Proof using.
  intros. rew_env_defs.
  gen E. induction F as [|(x,v)]; intros.
  rew_list~.
  rew_list. fequals.
Qed.
Lemma map_keys_push : forall r x v E,
  map_keys r (E &p x ~p v) = map_keys r E &p ((r x) ~p v).
Proof using. intros. rewrite map_keys_concat, map_keys_single. auto. Qed.

Lemma get_empty : forall k,
  get k (@empty A) = None.
Proof using. intros. rew_env_defs. auto. Qed.
Lemma get_single : forall k x v,
  get k (x ~p v) = If k = x
                    then Some v
                    else None.
Proof using. intros. rew_env_defs. unfold get_impl. auto. Qed.
Lemma get_concat : forall k E F,
  get k (E &p F) = match get k F with
                  | None => get k E
                  | Some v => Some v
                  end.
Proof using.
  intros. rew_env_defs. induction F as [|(x,v)].
  auto.
  simpl. case_if~.
Qed.

Lemma dom_empty :
  dom (@empty A) = \{}.
Proof using. rew_env_defs. auto. Qed.
Lemma dom_single : forall x v,
  dom (x ~p v) = \{x}.
Proof using.
  intros. rew_env_defs.
  rew_list. rewrite~ union_empty_r.
Qed.
Lemma dom_concat : forall E F,
  dom (E &p F) = dom E \u dom F.
Proof using.
  intros. rew_env_defs.
  gen E. induction F as [|(x,v)]; intros.
  rew_list. rewrite~ union_empty_r.
  rew_app. rewrite fold_right_cons. rewrite IHF.
   rewrite~ union_comm_assoc.
Qed.
Lemma dom_push : forall x v E,
  dom (E &p x ~p v) = \{x} \u dom E.
Proof using.
  intros. rewrite dom_concat. rewrite dom_single.
  rewrite~ union_comm.
Qed.

End Properties.

Section SinglesProperties.
Variable A B : Type.
Implicit Types x : varpath.
Implicit Types v : A.
Implicit Types xs : list varpath.
Implicit Types vs : list A.
Implicit Types E F : varpathenv A.

Lemma singles_nil :
  nil ~p* nil = (@empty A).
Proof using. intros. rew_env_defs. auto. Qed.

Lemma singles_cons : forall x v xs vs,
  (x::xs) ~p* (v::vs) = (xs ~p* vs) &p (x ~p v).
Proof using. intros. rew_env_defs. simpl. rew_env_defs. fequals. Qed.

Lemma singles_one : forall x v,
  (x::nil) ~p* (v::nil) = (x ~p v).
Proof using. intros. rew_env_defs. simpl. rew_env_defs. fequals. Qed.

Lemma singles_two : forall x1 x2 v1 v2,
  (x1::x2::nil) ~p* (v1::v2::nil) = (x2 ~p v2 &p x1 ~p v1).
Proof using. intros. rew_env_defs. simpl. rew_env_defs. fequals. Qed.

Lemma keys_singles : forall xs vs,
  length xs = length vs ->
  keys (xs ~p* vs) = xs.
Proof using.
  intros. rew_env_defs. gen vs. induction xs; introv E.
  rew_list~.
  destruct vs. false. simpl. rew_env_defs. rew_list. fequals.
   rew_list in E. applys IHxs. inverts E. auto.
Qed.

Lemma values_singles : forall xs vs,
  length xs = length vs ->
  values (xs ~p* vs) = vs.
Proof using.
  intros. rew_env_defs. gen vs.
  induction xs; destruct vs; introv E; tryfalse.
  auto.
  rew_list in E. simpl. rew_env_defs. rew_list. fequals.
   applys IHxs. inverts E. auto.
Qed.

Lemma dom_singles : forall xs vs,
  length xs = length vs ->
  dom (xs ~p* vs) = from_list xs.
Proof using.
  intros. rew_env_defs. gen vs.
  induction xs; destruct vs; introv E; tryfalse.
  simpl. rewrite~ from_list_nil.
  simpl. rew_env_defs. rew_list. rewrite from_list_cons. fequals.
   applys IHxs. inverts~ E.
Qed.

Lemma map_singles : forall (f : A -> B) xs vs,
  length xs = length vs ->
  map f (xs ~p* vs) = xs ~p* (LibList.map f vs).
Proof using.
  intros. rew_env_defs. gen vs.
  induction xs; destruct vs; introv E; tryfalse.
  rew_list~.
  rew_list. simpl. rew_list. fequals~.
Qed.

Lemma map_keys_singles : forall f xs vs,
  length xs = length vs ->
  map_keys f (xs ~p* vs) = (LibList.map f xs) ~p* vs.
Proof using.
  intros. rew_env_defs. gen vs.
  induction xs; destruct vs; introv E; tryfalse.
  rew_list~.
  rew_list. simpl. rew_list. fequals~.
Qed.

Lemma concat_singles : forall xs1 xs2 vs1 vs2,
  length xs1 = length vs1 ->
  length xs2 = length vs2 ->
  (xs2 ~p* vs2) &p (xs1 ~p* vs1) = (xs1 ++ xs2) ~p* (vs1 ++ vs2).
Proof using.
  introv E1 E2. rew_env_defs. gen vs1.
  induction xs1; destruct vs1; intros; tryfalse.
  rew_list~.
  rew_list. simpl. rew_list. fequals~.
Qed.

Lemma singles_keys_values : forall E,
  E = (keys E) ~p* (values E).
Proof using.
  intros. rew_env_defs. induction E as [|[x v] E'].
  auto.
  rew_list. simpl. rew_env_defs. rew_list. fequals.
Qed.

End SinglesProperties.

(* ---------------------------------------------------------------------- *)
(** ** Structural properties *)

Section StructProperties.

Variable A : Type.
Implicit Types x : varpath.
Implicit Types v : A.
Implicit Types E F : varpathenv A.

Lemma env_case : forall E,
  E = empty \/ exists x v E', E = E' &p x ~p v.
Proof using. intros. induction E using env_ind; autos*. Qed.

Lemma concat_empty_r : forall E,
  E &p empty = E.
Proof using. intros. rew_env_defs. rew_app~. Qed.

Lemma concat_empty_l : forall E,
  empty &p E = E.
Proof using. intros. rew_env_defs. rew_app~. Qed.

Lemma concat_assoc : forall E F G,
  E &p (F &p G) = (E &p F) &p G.
Proof using. intros. rew_env_defs. rew_app~. Qed.

Lemma empty_single_inv : forall x v,
  empty = x ~p v -> False.
Proof using. introv H. rew_env_defs. inverts H. Qed.

Lemma empty_concat_inv : forall E F,
  empty = E &p F -> empty = E /\ empty = F.
Proof using. introv H. rew_env_defs. forwards*: nil_eq_app_inv H. Qed.

Lemma empty_push_inv : forall E x v,
  empty = E &p x ~p v -> False.
Proof using. introv H. rew_env_defs. inverts H. Qed.

Lemma empty_middle_inv : forall E F x v,
  empty = E &p x ~p v &p F -> False.
Proof using. introv H. rew_env_defs. forwards* [_ ?]: nil_eq_app_inv H. false. Qed.

Lemma eq_single_inv : forall x1 x2 v1 v2,
  x1 ~p v1 = x2 ~p v2 ->
  x1 = x2 /\ v1 = v2.
Proof using. introv H. rew_env_defs. inverts~ H. Qed.

Lemma eq_push_inv : forall x1 x2 v1 v2 E1 E2,
  E1 &p x1 ~p v1 = E2 &p x2 ~p v2 ->
  x1 = x2 /\ v1 = v2 /\ E1 = E2.
Proof using. introv H. rew_env_defs. inverts~ H. Qed.

End StructProperties.

(* ---------------------------------------------------------------------- *)
(** ** More properties *)
Section MoreProperties.

Variable A : Type.
Implicit Types x : varpath.
Implicit Types v : A.
Implicit Types E F : varpathenv A.

Lemma dom_map : forall (B:Type) (f:A->B) E,
  dom (map f E) = dom E.
Proof using.
  induction E using env_ind.
  rewrite map_empty. do 2 rewrite dom_empty. auto.
  rewrite map_concat. rewrite map_single.
  rewrite_all dom_concat. rewrite_all dom_single. congruence.
Qed.

Lemma concat_assoc_map_push : forall f E F x v,
  E &p (map f (F &p x ~p v)) = (E &p map f F) &p x ~p (f v).
Proof using.
  intros. rewrite map_concat. rewrite map_single.
  rewrite~ concat_assoc.
Qed.

Lemma get_push : forall k x v E,
  get k (E &p x ~p v) =
    If k = x
      then Some v
      else get k E.
Proof using.
  intros. rewrite get_concat. rewrite get_single. case_if~.
Qed.

Ltac simpl_dom :=
  rewrite_all dom_push in *;
  rewrite_all dom_empty in *.

Lemma get_some : forall x E,
  x \in dom E -> exists v, get x E = Some v.
(* i.e.  [x \in dom E -> exists v, binds x v E] *)
Proof using. (* beautify *)
  unfold binds.
  introv H. rew_env_defs. induction E as [|[y v] E'].
  rew_list in H. rewrite* in_empty in H.
  unfold get_impl. case_if.
    eauto.
    rew_list in H. rewrite in_union in H. destruct H as [H|H].
     rewrite in_singleton in H. simpls. false.
     forwards* [v' ?]: IHE'.
Qed.

Lemma get_some_inv : forall x v E,
  get x E = Some v -> x \in dom E.
(* i.e.  [binds x v E -> x \in dom E] *)
Proof using. (* beautify *)
  unfold binds.
  introv H. rew_env_defs. unfolds get_impl. induction E as [|[y v'] E'].
  false.
  rew_list. rewrite in_union. simpl. case_if.
    inverts H. subst. left. rewrite~ in_singleton.
    forwards*: IHE'.
Qed.

(* Dont' need these. 
Lemma get_none : forall x E,
  x #p E -> get x E = None.
Proof using.
  induction E using env_ind; introv In.
  rewrite~ get_empty.
  rewrite~ get_push. case_if.
    simpl_dom. subst. 
    LV.lvpe_notin_false. simpl_dom. auto.
Qed.

Lemma get_none_inv : forall x E,
  get x E = None -> x #p E.
Proof using.
  induction E using env_ind; introv Eq.
  simpl_dom. auto.
  rewrite get_push in Eq. case_if~.
   simpl_dom. auto.
Qed.
*)

End MoreProperties.

(*
Lemma binds_get_or_arbitrary : forall `{Inhab A} x v (E:varpathenv A),
  binds x v E -> get_or_arbitrary x E = v.
Proof using. introv M. unfold get_or_arbitrary. rewrite~ M. Qed.

Definition indom_dec A (E:varpathenv A) x :=
  match get x E with None => false | Some _ => true end.

Global Instance indom_decidable : forall A (E:varpathenv A) x,
  Decidable (x \in dom E).
Proof using.
  intros. applys decidable_make (indom_dec E x).
  unfold indom_dec. cases (get x E) as C.
    lets: (get_some_inv C). rewrite~ isTrue_true.
    lets: (get_none_inv C). rewrite~ isTrue_false.
Qed.

(* ---------------------------------------------------------------------- *)
(** ** Hints and rewriting tactics *)

Hint Constructors okp.

Hint Rewrite dom_empty dom_single dom_concat : rew_env_dom.
Hint Rewrite map_empty map_single map_concat : rew_env_map.
Hint Rewrite map_keys_empty map_keys_single
 map_keys_concat : rew_env_map_keys.
Hint Rewrite get_empty get_single get_concat : rew_evn_get.

Hint Rewrite concat_empty_r concat_empty_l concat_assoc : rew_env_concat.

Tactic Notation "rew_env_concat" :=
  autorewrite with rew_env_concat.
Tactic Notation "rew_env_concat" "in" hyp(H) :=
  autorewrite with rew_env_concat in H.
Tactic Notation "rew_env_concat" "in" "*" :=
  autorewrite_in_star_patch ltac:(fun tt => autorewrite with rew_env_concat).
  (* autorewrite with rew_env_concat in *. *)

Ltac simpl_dom :=
  rewrite_all dom_map in *;
  rewrite_all dom_push in *;
  rewrite_all dom_concat in *;
  rewrite_all dom_single in *;
  rewrite_all dom_empty in *.

Hint Extern 1 (_ #p _) => simpl_dom; notin_solve.

(* ---------------------------------------------------------------------- *)
(** ** Properties of well-formedness and freshness *)
(*
Section OkpProperties.

Variable A B : Type.
Implicit Types k x : varpath.
Implicit Types v : A.
Implicit Types E F : varpathenv A.

Lemma okp_push_inv : forall E x v,
  okp (E &p x ~p v) -> okp E /\ x #p E.
Proof using.
  intros. inverts H as H1 H2.
  false (empty_push_inv H1).
  destructs 3 (eq_push_inv H). subst~.
Qed.

Lemma okp_push_inv_okp : forall E x v,
  okp (E &p x ~p v) -> okp E.
Proof using. introv H. destruct* (okp_push_inv H). Qed.

Lemma okp_concat_inv : forall E F,
  okp (E &p F) -> okp E /\ okp F.
Proof using.
  induction F using env_ind; rew_env_concat; introv Okp. auto.
  destruct (okp_push_inv Okp). 
  destruct~ IHF.
Qed.

Lemma okp_concat_inv_l : forall E F,
  okp (E &p F) -> okp E.
Proof using. introv H. lets*: okp_concat_inv H. Qed.

Lemma okp_concat_inv_r : forall E F,
  okp (E &p F) -> okp F.
Proof using. introv H. lets*: okp_concat_inv H. Qed.

Lemma okp_middle_change : forall E F x v1 v2,
  okp (E &p x ~p v1 &p F) -> okp (E &p x ~p v2 &p F).
Proof using.
  induction F using env_ind; introv; rew_env_concat; introv Okp.
  destruct* (okp_push_inv Okp).
  destruct* (okp_push_inv Okp).
Qed.

Lemma okp_middle_inv : forall E F x v,
  okp (E &p x ~p v &p F) -> x #p E /\ x #p F.
Proof using.
  induction F using env_ind; introv; rew_env_concat; intros Okp;
   destruct (okp_push_inv Okp).
  split~.
  forwards~ [? ?]: IHF H.
Qed.

Lemma okp_middle_inv_l : forall E F x v,
  okp (E &p x ~p v &p F) -> x #p E.
Proof using. introv H. forwards~ [? _]: okp_middle_inv H. Qed.

Lemma okp_middle_inv_r : forall E F x v,
  okp (E &p x ~p v &p F) -> x #p F.
Proof using. introv H. forwards~ [_ ?]: okp_middle_inv H. Qed.

Lemma okp_remove : forall F E G,
  okp (E &p F &p G) -> okp (E &p G).
Proof using.
  induction G using env_ind; rew_env_concat; introv Okp.
  lets*: okp_concat_inv Okp.
  lets*: okp_push_inv Okp.
Qed.

Lemma okp_map : forall E (f : A -> B),
  okp E -> okp (map f E).
Proof using.
  induction E using env_ind; introv;
   autorewrite with rew_env_map; rew_env_concat; intros Okp.
  auto. destruct* (okp_push_inv Okp).
Qed.

Lemma okp_concat_map: forall E F (f : A -> A),
  okp (E &p F) -> okp (E &p map f F).
Proof using.
  induction F using env_ind; introv;
   autorewrite with rew_env_map; rew_env_concat; intros Okp.
  auto. destruct* (okp_push_inv Okp).
Qed.

Fixpoint freshp (L : varpaths) (n : nat) (xs : list varpath) {struct xs} : Prop :=
  match xs, n with
  | nil, O => True
  | x::xs', S n' => x \notin L /\ freshp (L \u \{x}) n' xs'
  | _,_ => False
  end.

Hint Extern 1 (freshp _ _ _) => simpl.

Lemma okp_singles : forall n E xs (vs:list A),
  freshp (dom E) n xs ->
  length xs = length vs ->
  okp E ->
  okp (E &p xs ~p* vs).
Proof using.
  introv F EQ O. gen E n vs.
  induction xs; destruct vs; destruct n; intros; tryfalse.
  rewrite singles_nil. rewrite~ concat_empty_r.
  rew_length in EQ. inverts EQ.
(*
   simpl in F. destruct F as [Fr F']. lets [? M]: (fresh_union_r F').
   rewrite singles_cons. rewrite concat_assoc. applys okp_push.
     applys~p IHxs n.
     simpl_dom. rewrite~ dom_singles. lets~: fresh_single_notin M.
Qed.
 *)
Admitted.

(* LATER: not used
Lemma singles_okp : forall xs vs E,
  okp E ->
  fresh (dom E) (length xs) xs ->
  okp (E &p xs ~p* vs).
Proof using. ...
  induction xs; simpl; intros. auto.
  destruct H0. destruct Us; simpls. auto.
  rewrite iter_push_cons. rewrite* <- concat_assoc.
*)

(* LATER: not used;
   missing a precondition unless nil~p*vs returns nil
Lemma okp_concat_singles : forall n xs vs E,
  okp E ->
  fresh (dom E) n xs ->
  okp (E &p xs ~p* vs).
Proof using.
  intros. rew_env_defs. gen vs n E.
  induction xs; introv Okp Fr; destruct n; tryfalse.
  auto.
  destruct vs. simpl.
  rew_list in Fr. destruct Fr as [F Fr'].
  applys_to Fr notin_union_r...
Qed.
*)

(* LATER: not used
  Lemma okp_concat : forall E F,
    okp E -> okp F -> disjoint (dom E) (dom F) ->
    okp (E &p F).
*)

End OkpProperties.

Implicit Arguments okp_push_inv [A E x v].
Implicit Arguments okp_concat_inv [A E F].
Implicit Arguments okp_remove [A F E G].
Implicit Arguments okp_map [A E f].
Implicit Arguments okp_middle_inv_l [A E F x v].
Implicit Arguments okp_middle_inv_r [A E F x v].
Implicit Arguments okp_middle_inv [A E F x v].


(** Automation *)

Hint Resolve okp_middle_inv_l okp_map okp_concat_map okp_singles.

Hint Extern 1 (okp (?E &p ?G)) =>
  match goal with H: okp (E &p ?F &p G) |- _ =>
    apply (okp_remove H) end.

Hint Extern 1 (okp (?E)) =>
  match goal with H: okp (E &p _ ~p _) |- _ =>
    apply (okp_push_inv_okp H) end.

Hint Extern 1 (okp (?E)) =>
  match goal with H: okp (E &p _) |- _ =>
    apply (okp_concat_inv_l H) end.

Hint Extern 1 (okp (?E)) =>
  match goal with H: okp (_ &p E) |- _ =>
    apply (okp_concat_inv_r H) end.

(* not used
Hint Extern 1 (okp (_ &p ?xs ~p* ?vs)) =>
  match goal with H: fresh _ ?n xs |- _ =>
  match type of vs with list ?A =>
    apply (@okp_concat_singles A n)
  end end.
*)

*)

(* ---------------------------------------------------------------------- *)
(** ** Properties of the binds relation *)
(*
Section BindsProperties.
Variable A B : Type.
Implicit Types E F : varpathenv A.
Implicit Types x : varpath.
Implicit Types v : A.

Lemma binds_get : forall x v E,
  binds x v E -> get x E = Some v.
Proof using. auto. Qed.

(** Constructor forms *)

Lemma binds_empty_inv : forall x v,
  binds x v empty -> False.
Proof using.
  unfold binds. introv H. rewrite get_empty in H. false.
Qed.

Lemma binds_single_eq : forall x v,
  binds x v (x ~p v).
Proof using.
  intros. unfold binds. rewrite get_single. case_if~.
Qed.

Lemma binds_single_inv : forall x1 x2 v1 v2,
  binds x1 v1 (x2 ~p v2) ->
  x1 = x2 /\ v1 = v2.
Proof using.
  unfold binds. introv H. rewrite get_single in H.
  case_if; inversions~ H.
Qed.

Lemma binds_push_inv : forall x1 v1 x2 v2 E,
  binds x1 v1 (E &p x2 ~p v2) ->
     (x1 = x2 /\ v1 = v2)
  \/ (x1 <> x2 /\ binds x1 v1 E).
Proof using.
  introv H. unfolds binds. rewrite get_push in H. case_if.
  inverts~ H. auto.
Qed.

Lemma binds_push_eq : forall x v E,
  binds x v (E &p x ~p v).
Proof using. intros. unfolds binds. rewrite get_push. case_if~. Qed.

Lemma binds_push_eq_inv : forall x v1 v2 E,
  binds x v1 (E &p x ~p v2) -> v1 = v2.
Proof using.
  introv H. forwards [|]: binds_push_inv H. autos*. intros [? _]. false.
Qed.

Lemma binds_push_neq_inv : forall x1 x2 v1 v2 E,
  binds x1 v1 (E &p x2 ~p v2) -> x1 <> x2 -> binds x1 v1 E.
Proof using.
  introv H. forwards [|]: binds_push_inv H.
  intros [? ?] ?. false. autos*.
Qed.

Lemma binds_tail : forall x v E,
  binds x v (E &p x ~p v).
Proof using. intros. unfold binds. rewrite get_push. cases_if~. Qed.

Lemma binds_push_neq : forall x1 x2 v1 v2 E,
  binds x1 v1 E -> x1 <> x2 -> binds x1 v1 (E &p x2 ~p v2).
Proof using.
  introv H N. unfolds binds. rewrite get_push. case_if~.
Qed.

Lemma binds_concat_inv : forall x v E1 E2,
  binds x v (E1 &p E2) ->
     (binds x v E2)
  \/ (x #p E2 /\ binds x v E1).
Proof using.
  introv H. induction E2 using env_ind.
  rewrite~ concat_empty_r in H.
  rewrite concat_assoc in H.
   forwards [[? ?]|[? M]]: binds_push_inv H.
     subst. left. apply binds_tail.
     forwards [?|[? ?]]: IHE2 M.
       left. applys~ binds_push_neq.
       right~.
(*
Qed.
 *)
Admitted.

Lemma binds_map : forall x v (f : A -> B) E,
  binds x v E -> binds x (f v) (map f E).
Proof using.
  introv H. unfolds binds. rew_env_defs.
  induction E as [|[x' v'] E']; simpls.
  false.
  cases_if~. inverts~ H.
Qed.

(** Basic forms *)

Lemma binds_func : forall x v1 v2 E,
  binds x v1 E -> binds x v2 E -> v1 = v2.
Proof using.
  introv H1 H2. unfolds binds.
  induction E as [|E' x' v'] using env_ind.
  rewrite get_empty in H1. false.
  rewrite get_push in H1,H2. case_if~.
   inverts H1. inverts~ H2.
Qed.

Lemma binds_fresh_inv : forall x v E,
  binds x v E -> x #p E -> False.
Proof using.
  introv H F. unfolds binds.
  induction E as [|E' x' v'] using env_ind.
  rewrite get_empty in H. false.
  rewrite get_push in H. (*
case_if~. subst.
   simpl_dom; notin_false.
Qed.
                          *)
Admitted.

(** Derived forms *)

Lemma binds_single_eq_inv : forall x v1 v2,
  binds x v1 (x ~p v2) ->
  v1 = v2.
Proof using.
  introv H. unfolds binds. rewrite get_single in H.
  case_if. inverts~ H.
Qed.

Lemma binds_concat_left : forall x v E1 E2,
  binds x v E1 ->
  x #p E2 ->
  binds x v (E1 &p E2).
Proof using.
  introv H F. induction E2 using env_ind.
  rewrite~ concat_empty_r.
  rewrite concat_assoc. (*
applys~ binds_push_neq.
   simpl_dom. auto.
Qed.
                         *)
Admitted.

Lemma binds_concat_left_okp : forall x v E1 E2,
  okp (E1 &p E2) ->
  binds x v E1 ->
  binds x v (E1 &p E2).
Proof using.
  introv O H. induction E2 using env_ind.
  rewrite~ concat_empty_r.
  rewrite concat_assoc in O|-*. lets [_ ?]: okp_push_inv O.
  applys~ binds_push_neq. intro_subst. (*
applys~ binds_fresh_inv H.
Qed.
                                        *)
Admitted.

Lemma binds_concat_left_inv : forall x v E1 E2,
  binds x v (E1 &p E2) ->
  x #p E2 ->
  binds x v E1.
Proof using.
  introv H F. lets~ [M|[? ?]]: binds_concat_inv H.
    false. applys~ binds_fresh_inv M.
Qed.

Lemma binds_concat_right : forall x v E1 E2,
  binds x v E2 ->
  binds x v (E1 &p E2).
Proof using.
  introv H. induction E2 using env_ind.
  false. applys* binds_empty_inv.
  rewrite concat_assoc. lets [[? ?]|[? ?]]: binds_push_inv H.
    subst. applys binds_tail.
    applys~ binds_push_neq.
Qed.

Lemma binds_concat_right_inv : forall x v E1 E2,
  binds x v (E1 &p E2) ->
  x #p E1 ->
  binds x v E2.
Proof using.
  introv H F. lets~ [?|[? M]]: binds_concat_inv H.
    false. applys~ binds_fresh_inv M.
Qed.

Lemma binds_middle_eq : forall x E1 E2 v,
  x #p E2 ->
  binds x v (E1 &p x ~p v &p E2).
Proof using.
  introv F. applys~ binds_concat_left. applys binds_tail.
Qed.

(** Metatheory proof forms *)

(** Interaction between binds and the insertion of bindings.
  In theory we don't need this lemma since it would suffice
  to use the binds_cases tactics, but since weakening is a
  very common operation we provide a lemma for it. *)

Lemma binds_weaken : forall x a E F G,
  binds x a (E &p G) -> okp (E &p F &p G) ->
  binds x a (E &p F &p G).
Proof using.
  introv H O. lets [?|[? ?]]: binds_concat_inv H.
    applys~ binds_concat_right.
    applys~ binds_concat_left. applys~ binds_concat_left_okp.
Qed.

Lemma binds_remove : forall E2 E1 E3 x v,
  binds x v (E1 &p E2 &p E3) ->
  x #p E2 ->
  binds x v (E1 &p E3).
Proof using.
  introv H F. lets [?|[? M]]: binds_concat_inv H.
    applys~ binds_concat_right.
    forwards~: binds_concat_left_inv M. applys~ binds_concat_left.
Qed.

Lemma binds_subst : forall x2 v2 x1 v1 E1 E2,
  binds x1 v1 (E1 &p x2 ~p v2 &p E2) ->
  x1 <> x2 ->
  binds x1 v1 (E1 &p E2).
Proof using. introv H N. applys~ binds_remove H. 
(*

Qed.
 *)
Admitted.

Lemma binds_middle_eq_inv : forall x E1 E2 v1 v2,
  binds x v1 (E1 &p x ~p v2 &p E2) ->
  okp (E1 &p x ~p v2 &p E2) ->
  v1 = v2.
Proof using.
  introv H O. lets [? ?]: okp_middle_inv O.
  forwards~ M: binds_concat_left_inv H.
  applys~ binds_push_eq_inv M.
Qed.

Lemma binds_middle_inv : forall x1 v1 x2 v2 E1 E2,
  binds x1 v1 (E1 &p x2 ~p v2 &p E2) ->
     (binds x1 v1 E2)
  \/ (x1 #p E2 /\ x1 = x2 /\ v1 = v2)
  \/ (x1 #p E2 /\ x1 <> x2 /\ binds x1 v1 E1).
Proof using.
  introv H. lets [?|[? M]]: (binds_concat_inv H).
    left~.
    right. lets [N|[? N]]: (binds_concat_inv M).
      lets [? ?]: (binds_single_inv N). subst~.
      right. simpl_dom. split~.
(*

Qed.
 *)
Admitted.

Lemma binds_not_middle_inv : forall x v E1 E2 E3,
  binds x v (E1 &p E2 &p E3) ->
  x #p E2 ->
     (binds x v E3)
  \/ (x #p E3 /\ binds x v E1).
Proof using.
  introv H F. lets [?|[? M]]: (binds_concat_inv H).
    left~.
    right. forwards~ N: (binds_concat_left_inv M).
Qed.

Lemma fv_tm_in_values_binds : forall y fv x v E,
  binds x v E -> y \notin fv_tm_in_values fv E -> y \notin fv v.
Proof using
  in_values. introv H.
  induction E using env_ind; introv M.
  false. applys* binds_empty_inv.
  rewrite values_def in M,IHE.
  rewrite concat_def, single_def in M. rew_list in M. simpl in M.
(*
  lets [[? ?]|[? ?]]: (binds_push_inv H);  subst~. 
Qed.
 *)
Admitted.

(* unused -- requires a precondition on f
Lemma binds_keys : forall x v f E,
  binds x v E -> binds (f x) v (map_keys f E).
Proof using.
Qed.
*)

(* unused
Lemma binds_concat_inv_okp : forall x v E1 E2,
  okp (E1 &p E2) ->
  binds x v (E1 &p E2) ->
     (x #p E2 /\ binds x v E1)
  \/ (x #p E1 /\ binds x v E2).
Proof using.
  introv O H. induction E2 using env_ind.
  rewrite~ concat_empty_r in H.
  rewrite concat_assoc in O,H.
   forwards [[? ?]|[? M]]: binds_push_inv H.
     subst. left. apply conj_dup_r.
     split.
       apply binds_tail.
     forwards [?|[? ?]]: IHE2 M.
       left. applys~ binds_push_neq.
       right~....
Qed.

End BindsProperties.
(* ---------------------------------------------------------------------- *)
(** ** Tactics *)

Hint Resolve binds_push_eq binds_push_neq
  binds_map binds_concat_left binds_concat_right.

Tactic Notation "binds_mid" :=
  match goal with H: binds ?x ?v1 (_ &p ?x ~p ?v2 &p _) |- _ =>
    asserts: (v1 = v2); [ apply (binds_middle_eq_inv H) | subst; clear H ]
  end.
Tactic Notation "binds_mid" "~" :=
  binds_mid; auto_tilde.
Tactic Notation "binds_mid" "*" :=
  binds_mid; auto_star.

Tactic Notation "binds_push" constr(H) :=
  match type of H with binds ?x1 ?v1 (_ &p ?x2 ~p ?v2) =>
    destruct (binds_push_inv H) as [[? ?]|[? ?]]; [ subst x2 v2 | ]
  end.
Tactic Notation "binds_push" "~" constr(H) :=
  binds_push H; auto_tilde.
Tactic Notation "binds_push" "*" constr(H) :=
  binds_push H; auto_star.

(* ---------------------------------------------------------------------- *)
(** ** Properties of environment inclusion *)

Section ExtendsProperties.
Variable A : Type.
Implicit Types x : varpath.
Implicit Types v : A.
Implicit Types E F : varpathenv A.

Lemma extends_refl : forall E,
  extends E E.
Proof using. intros_all~. Qed.

Lemma extends_push : forall E x v,
  x #p E -> extends E (E &p x ~p v).
Proof using.
  introv Fr. intros x' v' B. unfolds binds.
  rewrite get_push. case_if~.
  lets: get_none Fr. false.
Qed.

Lemma extends_concat_l : forall E F,
  extends F (E &p F).
Proof using.
  introv B. unfolds binds.
  rewrite get_concat. rewrite~ B.
Qed.

Lemma extends_concat_r : forall E F,
  disjoint (dom E) (dom F) ->
  extends E (E &p F).
Proof using.
  introv D B. unfolds binds.
  lets: get_some_inv A B.
  forwards M: get_none A x F.
    applys~ disjoint_in_notin D.
  rewrite get_concat. rewrite~ M.
Qed.

(* not used
Lemma extends_push_reoccur : forall E x v,
  binds x v E -> extends E (E &p x ~p v).
*)

End ExtendsProperties.

Hint Resolve extends_refl extends_push.


(* ********************************************************************** *)
(** ** Tactics for case analysis on binding relations *)

(** [binds_get H as EQ] produces from an hypothesis [H] of
  the form [binds x a (E &p x ~p b &p F)] the equality [EQ: a = b]. *)

Ltac binds_get_nosubst_base H EQ :=
  match type of H with
  | binds ?x ?v1 (?E1 &p ?x ~p ?v2 &p ?E2) =>
    forwards EQ: (@binds_middle_eq_inv _ x E1 E2 v1 v2 H); [ auto | ]
  (* | binds ?x1 ?v1 (?E1 &p ?x2 ~p ?v2 &p ?E2) =>
     forwards EQ: (@binds_middle_inv _ x1 v1 x2 v2 E1 E2); [ | auto ] *)
  end.

Tactic Notation "binds_get_nosubst" constr(H) "as" ident(EQ) :=
  binds_get_nosubst_base H EQ.
Tactic Notation "binds_get_nosubst" constr(H) :=
  let EQ := fresh "EQ" in binds_get_nosubst H as EQ.

(** [binds_get H] expects an hypothesis [H] of the form
  [binds x a (E &p x ~p b &p F)] and substitute [a] for [b] in the goal. *)

Ltac binds_get H :=
  let EQ := fresh in binds_get_nosubst H as EQ;
  try match type of EQ with
  | ?f _ = ?f _ => inversions EQ
  | ?x = ?y => subst x end.

(** [binds_single H] derives from an hypothesis [H] of the form
  [binds x a (y ~p b)] the equalities [x = y] and [a = b], then
  it substitutes [x] for [y] in the goal or deduce a contradiction
  if [x <> y] can be found in the context. *)

Ltac binds_single H :=
  match type of H with binds ?x ?a (?y ~p ?b) =>
    let EQ := fresh "EQ" in
    destruct (binds_single_inv H) as [? EQ];
    try discriminate; try subst y;
    try match goal with N: ?x <> ?x |- _ =>
      false; apply N; reflexivity end end.

(** [binds_case H as B1 B2] derives from an hypothesis [H] of the form
  [binds x a (E &p F)] two subcases: [B1: binds x a E] (with a freshness
  condition [x #p F]) and [B2: binds x a F]. *)

Lemma binds_concat_inv' : forall A, forall x (v:A) E1 E2,
  binds x v (E1 &p E2) ->
     (x #p E2 /\ binds x v E1)
  \/ (binds x v E2).
Proof using. intros. forwards K: binds_concat_inv A H. destruct* K. Qed.

Tactic Notation "binds_case" constr(H) "as" ident(B1) ident(B2) :=
   let Fr := fresh "Fr" in
   destruct (binds_concat_inv' H) as [[Fr B1] | B2].

(** [binds_case H] makes a case analysis on an hypothesis [H] of the form
  [binds x a E] where E can be constructed using concatenation and
  singletons. It calls [binds_single] when reaching a singleton. *)

Ltac binds_cases H :=
  let go B := clear H;
    first [ binds_single B | binds_cases B | idtac ] in
  let B1 := fresh "B" in let B2 := fresh "B" in
  binds_case H as B1 B2; (*fix_env;*) [ go B1 | go B2 ].
  (* TODO: add support for binds_empty_inv *)

(* LATER: improve the above tactic using pattern matching
Ltac binds_cases_base H :=
  match H with
  | binds _ _ empty => false (binds_empty_inv H)
  | binds _ _ (_ &p _) =>
     let H1 := fresh "B" in
     destruct (binds_concat_inv H) as [H1|H1];
     clear H; binds_cases_base H1
  | binds _ _ (_ ~p _) =>
  | _ => idtac
  end.
*)
*)
*)

*)

End LVPE.
