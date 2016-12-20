Require Import TLC.LibTactics TLC.LibOption TLC.LibList TLC.LibProd TLC.LibLogic TLC.LibReflect TLC.LibFset.
Require Import LibNotIn.

Fixpoint fresh (A: Type) (L : fset A) (n : nat) (xs : list A) {struct xs} : Prop :=
  match xs, n with
  | nil, O => True
  | x::xs', S n' => x \notin L /\ fresh A (L \u \{x}) n' xs'
  | _,_ => False
  end.

Hint Extern 1 (fresh _ _ _) => simpl.

Lemma fresh_union_r : forall (A : Type) xs L1 L2 n,
  fresh A (L1 \u L2) n xs -> fresh A L1 n xs /\ fresh A L2 n xs.
Proof using.
  induction xs; simpl; intros; destruct n;
  tryfalse*. auto.
  destruct H. split; split; auto.
  forwards*: (@IHxs (L1 \u \{a}) L2 n).
   rewrite union_comm.
   rewrite union_comm_assoc.
   rewrite* union_assoc.
  forwards*: (@IHxs L1 (L2 \u \{a}) n).
   rewrite* union_assoc.
Qed.

Lemma fresh_union_r1 : forall A xs L1 L2 n,
  fresh A (L1 \u L2) n xs -> fresh A L1 n xs.
Proof using. intros. forwards*: fresh_union_r. Qed.

Lemma fresh_union_r2 : forall A xs L1 L2 n,
  fresh A (L1 \u L2) n xs -> fresh A L2 n xs.
Proof using. intros. forwards*: fresh_union_r. Qed.

Lemma fresh_union_l : forall A xs L1 L2 n,
  fresh A L1 n xs -> fresh A L2 n xs -> fresh A (L1 \u L2) n xs.
Proof using.
  induction xs; simpl; intros; destruct n; tryfalse*. auto.
  destruct H. destruct H0. split~.
  forwards~ K: (@IHxs (L1 \u \{a}) (L2 \u \{a}) n).
  rewrite <- (union_same \{a}).
  rewrite union_assoc.
  rewrite <- (union_assoc L1).
  rewrite (union_comm L2).
  rewrite (union_assoc L1).
  rewrite* <- union_assoc.
Qed.

Lemma fresh_empty : forall A L n xs,
  fresh A L n xs -> fresh A \{} n xs.
Proof using.
  intros. rewrite <- (union_empty_r L) in H.
  destruct* (fresh_union_r _ _ _ _ _ H).
Qed.

Lemma fresh_length : forall A L n xs,
  fresh A L n xs -> n = length xs.
Proof using.
  intros. gen n L. induction xs; simpl; intros n L Fr;
    destruct n; tryfalse*.
  auto.
  rew_length. rewrite* <- (@IHxs n (L \u \{a})).
Qed.

Lemma fresh_resize : forall A L n xs,
  fresh A L n xs -> forall m, m = n -> fresh A L m xs.
Proof using.
  introv Fr Eq. subst~.
Qed.

Lemma fresh_resize_length : forall A L n xs,
  fresh A L n xs -> fresh A L (length xs) xs.
Proof using.
  introv Fr. rewrite* <- (fresh_length _ _ _ _ Fr).
Qed.

Implicit Arguments fresh_union_r [xs L1 L2 n].
Implicit Arguments fresh_union_r1 [xs L1 L2 n].
Implicit Arguments fresh_union_r2 [xs L1 L2 n].
Implicit Arguments fresh_union_l [xs L1 L2 n].
Implicit Arguments fresh_empty  [L n xs].
Implicit Arguments fresh_length [L n xs].
Implicit Arguments fresh_resize [L n xs].
Implicit Arguments fresh_resize_length [L n xs].

Lemma fresh_single_notin : forall A x xs n,
  fresh A \{x} n xs ->
  x \notin from_list xs.
Proof using.
  induction xs; destruct n; introv F; simpl in F; tryfalse.
  rewrite~ from_list_nil.
  destruct F as [Fr F']. lets [? ?]: (fresh_union_r _ F').
   specializes IHxs n. rewrite~ from_list_cons.
Qed.

Ltac fresh_solve_target_from E n xs H :=
  match type of H with
  | fresh E n xs => constr:(H)
  | fresh E ?m xs =>
      match n with
      | length xs => constr:(fresh_resize_length H)
      | _ =>
         match goal with
         | Eq: m = n |- _ => constr:(fresh_resize H _ (sym_eq Eq))
         | Eq: n = m |- _ => constr:(fresh_resize H _ Eq)
         end
      end
  | fresh (?F \u ?G) ?m xs =>
     let H' :=
        match F with
        | context [E] => constr:(fresh_union_r1 H)
        | _ => match G with
          | context [E] => constr:(fresh_union_r2 H)
          | _ => fail 20
          end
        end in
     fresh_solve_target_from E n xs H'
  end.

Ltac fresh_solve_target E n xs :=
  match goal with H: fresh ?L _ xs |- _ =>
    match L with context[E] =>
      let F := fresh_solve_target_from E n xs H in
      apply F
    end
  end.

Ltac fresh_solve_one :=
  match goal with
  | |- fresh ?E ?n ?xs =>
    fresh_solve_target E n xs
  | |- fresh \{} ?n ?xs =>
    match goal with H: fresh ?F ?m xs |- _ =>
      apply (fresh_empty H);
      fresh_solve_target F n xs
    end
  end.

Ltac fresh_simpl :=
  try match goal with |- fresh (_ \u _) _ _ =>
    apply fresh_union_l; fresh_simpl end.

Ltac fresh_solve_by_notins :=
  simpl; splits; try notin_solve.

Ltac fresh_solve :=
  fresh_simpl;
  first [ fresh_solve_one
        | fresh_solve_by_notins
        | idtac ].

Hint Extern 1 (fresh _ _ _) => fresh_solve.
