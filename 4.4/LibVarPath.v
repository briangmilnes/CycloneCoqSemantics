(* Adapt xp, variable and path of nats from the thesis in the TLC style. *)

Set Implicit Arguments.
Require Import TLC.LibTactics TLC.LibReflect TLC.LibBool TLC.LibOperation TLC.LibRelation TLC.LibOrder  TLC.LibNat TLC.LibVar.

Require Export LibPath.


(* ********************************************************************** *)

Definition varpath := (prod var Path).

(* Inhabited and comparable *)

Instance varpath_inhab : Inhab varpath.
Proof using.
 intros. 
 lets P: (var_fresh \{}).
 inversion P.
 apply (prove_Inhab (x, (cons u_pe nil))).
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

(* I don't really care about sets of varpaths, only that I can get a var set from them.
(* Will I need these? *)
Lemma varpath_eq:
  forall (x x' : var) (p p': Path),
    x = x' ->
    p = p' ->
    (x,p) = (x',p').
Proof.
  intros.
  rewrite H.
  rewrite~ H0.
Qed.
*)

(* Varpath Automation *)

Ltac lvpe_case_if_eq_base_resolve_if E F H :=
  destruct (classicT (E = F)) as [H|H];
  [tryfalse; try subst E; try apply~ If_l | tryfalse; try apply~ If_r].

Tactic Notation "lvpe_case_if_eq_resolve_if" constr(E) constr(F) "as" ident(H) :=
  lvpe_case_if_eq_base_resolve_if E F H.
Tactic Notation "lvpe_case_if_eq_resolve_if" constr(E) constr(F) :=
  let C := fresh "C" in lvpe_case_if_eq_resolve_if E F as C.

Ltac lvpe_case_if_eq_resolve_if A B :=
  lvpe_case_if_eq_base_resolve_if A B.

Ltac lvpe_case_if_eq_varpath :=
  match goal with
    | H: context [classicT((?x,?y) = (?x',?y') :> varpath)] |- _ =>
      lvpe_case_if_eq_resolve_if (x,y) (x',y')
    | |- context [classicT((?x,?y) = (?x',?y') :> varpath)]      =>
      lvpe_case_if_eq_resolve_if (x,y) (x',y')
    | H: context [classicT(?x = ?y :> varpath)] |- _ =>
      lvpe_case_if_eq_resolve_if x y
  | |- context [classicT(?x = ?y :> varpath)]      => 
      lvpe_case_if_eq_resolve_if x y
  end.

Tactic Notation "case_varpath" := lvpe_case_if_eq_varpath; try solve [ notin_false ].
Tactic Notation "case_varpath" "~" := case_varpath; auto_tilde.
Tactic Notation "case_varpath" "*" := case_varpath; auto_star.

(*
Module LV.
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

(* Not used. -bgm 
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

Ltac lvpe_notin_solve_target_from x E H :=
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

Ltac lvpe_notin_solve_target x E :=
  match goal with
  | H: x \notin ?L |- _ =>
    match L with context[E] =>
      let F := lvpe_notin_solve_target_from x E H in
      apply F
    end
  | H: x <> ?y |- _ =>
     match E with \{y} =>
       apply (notin_singleton_l H)
     end
  end.

Ltac lvpe_notin_solve_one :=
  match goal with
  | |- ?x \notin \{?y} =>
     apply notin_singleton_swap;
     lvpe_notin_solve_target y (\{x})
  | |- ?x \notin ?E =>
    lvpe_notin_solve_target x E
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

Ltac lvpe_notin_simpl :=
  match goal with
  | |- _ \notin (_ \u _) => apply notin_union_l; notin_simpl
  | |- _ \notin (\{}) => apply notin_empty; notin_simpl
  | |- ?x <> ?y => apply notin_singleton_r; notin_simpl
  | |- _ => idtac
  end.

Ltac lvpe_notin_solve_false :=
  match goal with
  | H: ?x \notin ?E |- _ =>
    match E with context[x] =>
      apply (@notin_same _ x);
      let F := lvpe_notin_solve_target_from x (\{x}) H in
      apply F
    end
  | H: ?x <> ?x |- _ => apply H; reflexivity
  end.

Ltac lvpe_notin_false :=
  match goal with
  | |- False => lvpe_notin_solve_false
  | _ => intros_all; false; lvpe_notin_solve_false
  end.

Ltac lvpe_notin_from_fresh_in_context :=
  repeat (match goal with H: fresh _ _ _ |- _ =>
    progress (simpl in H; destructs H) end).

Ltac lvpe_notin_solve :=
  lvpe_notin_from_fresh_in_context;
  first [ lvpe_notin_simpl; try lvpe_notin_solve_one
        | lvpe_notin_false ].

(*
Hint Extern 1 (_ \notin _) => lvpe_notin_solve.
Hint Extern 1 (_ <> _ :> var) => lvpe_notin_solve.
Hint Extern 1 ((_ \notin _) /\ _) => splits.
*)

(*
LATER:
  | |- ?x \notin ?E =>
	progress (unfold x); notin_simpl
  | |- (var_gen ?x) \notin _ =>
        apply notin_var_gen; intros; notin_simpl
 *)
End LV.
*)