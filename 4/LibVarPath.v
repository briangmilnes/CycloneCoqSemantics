(* Adapt xp, variable and path of nats from the thesis in the TLC style. *)

Set Implicit Arguments.
Require Import TLC.LibTactics TLC.LibReflect TLC.LibBool TLC.LibOperation TLC.LibRelation TLC.LibOrder  TLC.LibNat TLC.LibVar.

Require Export LibPath.

(* ********************************************************************** *)

Definition varpath := (prod var path).

(* Inhabited and comparable *)

Instance varpath_inhab : Inhab varpath.
Proof using.
 intros. 
 lets P: (var_fresh \{}).
 inversion P.
 apply (prove_Inhab (x, (cons 0 nil))).
Qed.

Fixpoint varpath_compare (x y : varpath) :=
  match x, y with
    | (x,xp), (y, yp) =>
      If x = y then
       (If xp = yp then true else false)
    else false
  end.

Instance varpath_comparable : Comparable varpath.
Proof using.
  applys (comparable_beq varpath_compare).
  induction x; destruct y; simpl; autos*; auto_false.
  destruct (classicT (a = v)); destruct (classicT (b = p)); split; 
  intros; subst; try solve [auto | inversion H | congruence].
Qed.

(* Not in Theorems and Tactics. *)

(* ********************************************************************** *)
(** ** Tactics for notin *)

(* Can I and must I generalize x here? *) 
(** For efficiency, we avoid rewrites by splitting equivalence. *)

Implicit Types x : varpath.

Lemma notin_singleton_r : forall x y,
  x \notin \{y} -> x <> y.
Proof using. intros. rewrite~ <- notin_singleton. Qed.

Lemma notin_singleton_l : forall x y,
  x <> y -> x \notin \{y}.
Proof using. intros. rewrite~ notin_singleton. Qed.

Lemma notin_singleton_swap : forall x y,
  x \notin \{y} -> y \notin \{x}.
Proof using.
  intros. apply notin_singleton_l.
  apply sym_not_eq. apply~ notin_singleton_r.
Qed.

Lemma notin_union_r : forall x E F,
  x \notin (E \u F) -> (x \notin E) /\ (x \notin F).
Proof using. intros. rewrite~ <- notin_union. Qed.

Lemma notin_union_r1 : forall x E F,
  x \notin (E \u F) -> (x \notin E).
Proof using. introv. rewrite* notin_union. Qed.

Lemma notin_union_r2 : forall x E F,
  x \notin (E \u F) -> (x \notin F).
Proof using. introv. rewrite* notin_union. Qed.

Lemma notin_union_l : forall x E F,
  x \notin E -> x \notin F -> x \notin (E \u F).
Proof using. intros. rewrite~ notin_union. Qed.

(* Bug.
Lemma notin_var_gen : forall E F,
  (forall x, x \notin E -> x \notin F) ->
  (var_gen E) \notin F.
Proof using. intros. autos~ var_gen_spec. Qed.
*)

Implicit Arguments notin_singleton_r    [x y].
Implicit Arguments notin_singleton_l    [x y].
Implicit Arguments notin_singleton_swap [x y].
Implicit Arguments notin_union_r  [x E F].
Implicit Arguments notin_union_r1 [x E F].
Implicit Arguments notin_union_r2 [x E F].
Implicit Arguments notin_union_l  [x E F].

(** Tactics to deal with notin.  *)

Ltac notin_solve_target_from x E H :=
  match type of H with
  | x \notin E => constr:(H)
  | x \notin (?F \u ?G) =>
     let H' :=
        match F with
        | context [E] => constr:(notin_union_r1 H)
        | _ => match G with
          | context [E] => constr:(notin_union_r2 H)
          | _ => fail 20
          end
        end in
     notin_solve_target_from x E H'
  end.

Ltac notin_solve_target x E :=
  match goal with
  | H: x \notin ?L |- _ =>
    match L with context[E] =>
      let F := notin_solve_target_from x E H in
      apply F
    end
  | H: x <> ?y |- _ =>
     match E with \{y} =>
       apply (notin_singleton_l H)
     end
  end.

Ltac notin_solve_one :=
  match goal with
  | |- ?x \notin \{?y} =>
     apply notin_singleton_swap;
     notin_solve_target y (\{x})
  | |- ?x \notin ?E =>
    notin_solve_target x E
  (* If x is an evar, tries to instantiate it.
     Problem: it might loop !
  | |- ?x \notin ?E =>
     match goal with y:var |- _ =>
       match y with
       | x => fail 1
       | _ =>
         let H := fresh in cuts H: (y \notin E);
         [ apply H | notin_solve_target y E ]
        end
     end
  *)
  end.

Ltac notin_simpl :=
  match goal with
  | |- _ \notin (_ \u _) => apply notin_union_l; notin_simpl
  | |- _ \notin (\{}) => apply notin_empty; notin_simpl
  | |- ?x <> ?y => apply notin_singleton_r; notin_simpl
  | |- _ => idtac
  end.

Ltac notin_solve_false :=
  match goal with
  | H: ?x \notin ?E |- _ =>
    match E with context[x] =>
      apply (@notin_same _ x);
      let F := notin_solve_target_from x (\{x}) H in
      apply F
    end
  | H: ?x <> ?x |- _ => apply H; reflexivity
  end.

Ltac notin_false :=
  match goal with
  | |- False => notin_solve_false
  | _ => intros_all; false; notin_solve_false
  end.

Ltac notin_from_fresh_in_context :=
  repeat (match goal with H: fresh _ _ _ |- _ =>
    progress (simpl in H; destructs H) end).

Ltac notin_solve :=
  notin_from_fresh_in_context;
  first [ notin_simpl; try notin_solve_one
        | notin_false ].

Hint Extern 1 (_ \notin _) => notin_solve.
Hint Extern 1 (_ <> _ :> var) => notin_solve.
Hint Extern 1 ((_ \notin _) /\ _) => splits.