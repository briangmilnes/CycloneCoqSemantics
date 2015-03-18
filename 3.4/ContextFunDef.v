(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Finally a nice clean enough easy to use context functor.

*)
Set Implicit Arguments.
Require Export ContextDef.
Require Export BooleanEqualityDef.
Require Export BooleanEqualitySetFunDef.
Require Export VariableEqualityDef.
Require Export VariableEqualitySetFunDef.
Require Export CpdtTactics.
Require Import MoreTacticals.

(* Todo admit, fix or undo. *)
Module ContextFun(K': BooleanEquality) (T' : BooleanEquality). (* <: Context. *)
  Module K := BooleanEqualitySetFun(K').
  Module T := T'.

Inductive Context': Type :=
| dot  : Context' 
| ctxt :  K.elt -> T.t -> Context' -> Context' .

Definition Context := Context'.
Definition empty  := dot.

Function add (c : Context') (k: K.elt) (t : T.t)  : Context' :=
  match c with
    | dot => (ctxt k t (dot))
    | (ctxt k' t' c') =>
      match K.eqb k k' with
        | true  => (ctxt k  t  c')
        | false => (ctxt k' t' (add c' k t))
      end
  end.
Hint Unfold add. 

Function map (c : Context') (k : K.elt) : option T.t :=
  match c with
    | dot => None
    | (ctxt k' t' c') =>
      match K.eqb k k' with
        | true  => Some t'
        | false => (map c' k)
      end
  end.
Hint Unfold map.

Function delete (c : Context') (k : K.elt) : Context' :=
  match k, c with
    | k, dot => empty
    | k, (ctxt k' t' c') =>
      match K.eqb k k' with
        | true  => c'
        | false => (ctxt k' t' (delete c' k))
      end
  end.
Hint Unfold delete.

Function nodup (c : (Context')) : bool :=
  match c with
    | dot => true
    | (ctxt k' t' c') =>
      match map c' k' with
        | Some t  => false
        | None  => nodup c'
      end
end.
Hint Unfold nodup.

Function extends (c c' : Context') : bool :=
  match c with 
    | dot => true
    | ctxt k t c'' =>
      match map c' k with
       | Some t' => 
         match (T.eqb t t') with
           | true => extends c'' c' 
           | false => false
         end
       | None => false
      end
  end.
Hint Unfold extends.

Function equal (c c' : Context') : bool :=
  andb (extends c c') (extends c' c).
Hint Unfold equal.

Function concat (c c' : Context') {struct c'} : Context' :=
  match c' with
  | dot => c
  | (ctxt k v d) => (ctxt k v (concat c d))
  end.

Function dom (c : Context') : K.t :=
 match c with 
 | dot => K.empty
 | (ctxt k v c') => K.union (K.singleton k) (dom c')
 end.


(* Do I need this? is it being used by LN LibEnv.env? *)
Lemma Context'_ind': 
  forall (P : Context' -> Prop),
  (P empty) ->
  (forall E x v, P E -> P (concat E (ctxt x v empty))) ->
  (forall E, P E).
Proof.
  induction E; try solve[crush].
Qed.

(* Can I add k t to the front of c'? *)
Function extends1 (c : Context') (k : K.elt ) (t : T.t) (c' : Context') : bool :=
  match map c' k with
   | Some _ => false
   | None =>
     match map c k with
      | Some _ => false
      | None   => (equal (ctxt k t c) c')
     end
end.
Hint Unfold extends1.

Function extends1' (c : Context') (k : K.elt ) (t : T.t) (c' : Context') : bool :=
  match map c' k with
   | Some _ => false
   | None =>
     match map c k with
      | Some _ => false
      | None   => extends (ctxt k t c) c'
     end
end.
Hint Unfold extends1'.

Lemma map_empty_none: forall k, map empty k = None.
Proof.
   crush.
Qed.

Lemma nodup_empty: nodup empty = true.
Proof.
  crush.
Qed.

Ltac case_if e := 
  match goal with 
    | H: context [if e ?x ?y then _ else _] |- _ => case_eq(e x y); intros; subst
    | |- context [if e ?x ?y then _ else _] => case_eq(e x y); intros; subst
  end.

Lemma map_add: forall c k t, map (add c k t) k = Some t.
Proof.
  intros.
  induction c; crush.
  case_if K.eqb; crush.
Qed.

Lemma map_agreement:
  forall c k t,
    nodup c = true ->
    map c k = Some t ->
    forall t', 
      map c k = Some t' ->
      t = t'.
Proof.
 intros.
 induction c; crush.
Qed.

Lemma map_some_none_neq: 
  forall c k k', 
    map c k  = None ->
    forall t, 
      map c k' = Some t ->
      k <> k'.
Proof.
  induction c; crush.
Qed.

Ltac expand_cases :=
  repeat match goal with
          | [ H : (if ?x then _ else _) = Some _ |- _ ] => 
            destruct x ; try solve[inversion H]
          | [ H : (if ?x then _ else _) = None   |- _ ] => 
            destruct x ; try solve[inversion H]
          end.

Ltac invert_some_eq :=
  repeat match goal with
          | [ H : Some _ = Some _ |- _ ] => 
            inversion H; subst; clear H
         end.

Lemma map_some_none_beq_t_false:
  forall c k k', 
    map c k  = None ->
    forall t, 
      map c k' = Some t ->
      K.eqb k k' = false.
Proof.
  intros.
  induction c.
  crush.
  pose proof H as H'.
  pose proof H0 as H0'.
  unfold map in H.
  fold map in H.
  unfold map in H0.
  fold map in H0.

  Ltac rewrite_eq e :=
    match goal with
     | [ H : e ?a ?b = _ , 
         I : context[if e ?a ?b then _ else _ ]  |- _ ] =>
       rewrite H in I; try solve[inversion I]
    end.

Ltac case_if2 e := 
  match goal with 
    | H: context [if e ?x ?y then _ else _] |- _ => case_eq(e x y); intros; 
          rewrite_eq e
    | |- context [if e ?x ?y then _ else _] => case_eq(e x y); intros; 
          rewrite_eq e
  end.

(*  Much cleaner!  No variables, no context variables.  *)
  case_if2 K.eqb;   case_if2 K.eqb.

(*
  case_eq(K.eqb k e); case_eq(K.eqb k' e); intros;
  rewrite H1 in *; rewrite H2 in *; try solve [inversion H].
*)

  inversion H0.
  subst.
  case_eq(K.eqb k k'); intros; try reflexivity.
  apply K.eqb_to_eq in H3.
  subst.

  rewrite H1 in H2.
  inversion H2.
  apply IHc in H; try assumption.
Qed.

Lemma empty_extended_by_all:
  forall c, 
    extends empty c = true.
Proof.
  crush.
Qed.

Lemma empty_extends_only_empty:
  forall c, 
    extends c empty = true ->
    c = empty.
Proof.
  intros.
  induction c; crush.
Qed.

Lemma extends_r_str:
  forall c c', 
    extends c c' = true -> 
    forall v t, 
      nodup (ctxt v t c') = true ->
      extends c (ctxt v t c') = true.
Proof.
  intros c c'.
  functional induction (extends c c'); try solve[crush].
  intros.
  apply IHb with (v:= v) (t:= t0) in H.
  unfold extends.
  fold extends.
  case_eq(map (ctxt v t0 c') k); intros.
  case_eq(T.eqb t t1); intros; try assumption.
  pose proof H0 as H0'.
  unfold map in H1.
  fold map in H1.
  case_eq(K.eqb k v); intros; try rewrite H3 in H1.
  move t1 before t.
  unfold nodup in H0.
  fold nodup in H0.
  apply K.eqb_to_eq in H3.
  rewrite <- H3 in H0.
  rewrite e0 in H0.
  inversion H0.
  rewrite e0 in H1.
  crush.

  pose proof H1 as H1'.
  unfold map in H1.
  fold map in H1.
  case_eq(K.eqb k v); intros; rewrite H2 in H1.
  inversion H1.
  rewrite e0 in H1.
  inversion H1.
  assumption.
Qed.

Lemma extends1_to_equality:
  forall c v t c', 
    extends1 c v t c' = true -> 
    equal (ctxt v t c) c' = true.
Proof.
  intros.
  pose proof H as H'.
  unfold extends1 in H.
  case_eq(map c' v); intros; rewrite H0 in H; try solve[inversion H];
  case_eq(map c v); intros; try rewrite H1 in H; try solve[inversion H].
  assumption.
Qed.

Lemma extends1_r_str:
  forall c v t c', 
    extends1 c v t c' = true -> 
    forall v' t', 
      nodup (ctxt v t (ctxt v' t' c')) = true ->
      extends1 c v t (ctxt v' t' c') = true.
Proof.
  intros.
  induction c'; intros.
  unfold extends1 in H.
  fold extends1 in H.
  simpl in H.
  case_eq(map (ctxt v' t' (dot)) v); intros.

(* Stuck.
  intros c v t c'.
  functional induction (extends1 c v t c'); try solve[crush].
  intros.
  unfold extends1.
  case_eq(map (ctxt v' t' c') v); intros.
  unfold nodup in H0.
  fold nodup in H0.
  unfold map in H0.
  fold map in H0.
  case_eq(K.eqb v v'); intros; rewrite H2 in H0.
  inversion H0.
  rewrite e in H0.
  case_eq(map c' v'); intros; rewrite H3 in H0.
  inversion H0.
  unfold map in H1.
  fold map in H1.
  rewrite H2 in H1.
  rewrite H1 in e.
  inversion e.
  rewrite e0.
  unfold map in H1.
  case_eq(K.eqb v v'); intros; rewrite H2 in H1.
  inversion H1.
  fold map in H1.
  (* stuck *)
*)
Admitted.

(*
Lemma extends_refl_no_nodup:
  forall c, 
    extends c c = true.
Proof.
  intros.
  induction c; try solve [crush].
  unfold extends.
  fold extends.
  simpl.
  rewrite K.eqb_refl.
  rewrite T.beq_t_refl.
  unfold extends.
  fold extends.
Qed.
*)

Lemma extends_refl:
  forall c, 
    nodup c = true ->
    extends c c = true.
Proof.
  intros.
  induction c; try solve [crush].
  unfold extends.
  fold extends.
  simpl.
  rewrite K.eqb_refl.
  rewrite T.eqb_refl.
  apply extends_r_str; try assumption.
  unfold nodup in H.
  fold nodup in H.
  case_eq(map c e); intros; rewrite H0 in H.
  inversion H.
  apply IHc in H.
  assumption.
Qed.

Lemma extends_l_weak:
  forall c c' k,
    extends c c' = true -> 
    forall t,
      map c' k = Some t ->
      extends (ctxt k t c) c' = true.
Proof.
  intros.
  unfold extends.
  fold extends.
  unfold map.
  fold map.
  rewrite H0.
  rewrite T.eqb_refl.
  assumption.
Qed.

Lemma extends_l_weak_r_str:
  forall c c' k,
    extends c c' = true -> 
    map c' k = None  -> 
    forall t, 
      nodup c' = true ->
      extends (ctxt k t c) (ctxt k t c') = true.
Proof.
  intros.
  unfold extends.
  fold extends.
  unfold map.
  fold map.
  rewrite K.eqb_refl.
  rewrite T.eqb_refl.
  
  apply extends_r_str; try assumption.
  unfold nodup.
  fold nodup.
  rewrite H0.
  assumption.
Qed.

Lemma extends_l_str: 
  forall c c' k t, 
    extends (ctxt k t c) c' = true -> extends c c' = true.
Proof.
  intros.
  induction c; try solve[crush].
  unfold extends in H.
  fold extends in H.
  unfold extends.
  fold extends.
  case_eq(map c' k); intros; rewrite H0 in *; case_eq(map c' e); intros; try rewrite H1 in *; try solve[inversion H]; case_eq(T.eqb t t1); intros; try rewrite H2 in *; try inversion H. 
 case_eq(T.eqb t0 t2); intros; rewrite H4 in *; try inversion H; reflexivity.
Qed.

Lemma map_extends_none_agreement:
  forall c c',
   extends c c' = true -> 
   forall v, 
     map c' v = None -> 
     map c v  = None.
Proof.
  intros c c' ext.
  functional induction (extends c c'); try solve [crush].
  intros.
  apply IHb with (v:= v) in ext; try assumption.
  unfold map.
  fold map.
  case_eq (K.eqb v k); intros.
  apply K.eqb_to_eq in H0.
  subst.
  rewrite e0 in H.
  inversion H.
  assumption.
Qed.

Lemma equal_empty_empty:
  forall c,
    equal empty c = true ->
    c = empty.
Proof.
  intros.
  induction c; crush.
Qed.

Lemma K_eq_sym:  forall k k', K.eqb k k' = K.eqb k' k.
Proof.
  apply K.eqb_sym.
Qed.  

Lemma map_r_str:
  forall c k0 t0 k t,
    map (ctxt k0 t0 c) k = Some t -> 
    K.eqb k0 k = false -> 
    map c k = Some t.
Proof.
  intros.
  unfold map in H.
  fold map in H.
  rewrite K.eqb_sym in H0.
  rewrite H0 in H.
  assumption.
Qed.

Lemma map_r_str_add:
  forall c k0 t0 k t,
    map (add c k0 t0) k = Some t ->
    K.eqb k k0 = false -> 
    map c k = Some t.
Proof.
  intros.
  induction c.
  unfold add in H.
  unfold map in H.
  rewrite H0 in H.
  inversion H.

  unfold map.
  fold map.
  unfold add in H.
  fold add in H.
  case_eq(K.eqb k0 e); case_eq(K.eqb k e); intros; rewrite H2 in H.
  apply K.eqb_trans with (x:= k) in H1.
  apply K.eqb_to_eq in H1.
  subst.
  rewrite K.eqb_sym in H0.
  apply K.eqb_to_eq in H2.
  subst.
  rewrite K.eqb_refl in H0.
  inversion H0.

  apply K.eqb_refl.
  unfold map in H.
  fold map in H.
  rewrite H0 in H.
  assumption.

  unfold map in H.
  fold map in H.
  rewrite H1 in H.
  assumption.

  unfold map in H.
  fold map in H.
  rewrite H1 in H.
  apply IHc in H.
  assumption.
Qed.

Lemma nodup_add_none:
  forall c,
    nodup c = true ->
    forall k,
     map c k = None  ->
    forall t, 
      nodup (add c k t) = true.
Proof.
  induction c; try solve [crush].
  intros.
  unfold nodup in H.
  fold nodup in H.
  case_eq (map c e); intros; rewrite H1 in H; try inversion H.
  unfold map in H0.
  fold map in H0.
  case_eq (K.eqb k e); intros; rewrite H2 in H0.
  inversion H0.

  unfold add.
  fold add.
  rewrite H2.
  unfold nodup.
  fold nodup.
  rewrite H3.  
  case_eq (map (add c k t0) e); intros.
  apply map_r_str_add in H4; try assumption.
  rewrite H4 in H1.
  inversion H1.
  apply IHc with (k:= k) (t:= t1) in H; try assumption.
  rewrite K.eqb_sym in H2; try assumption.
  apply IHc with (k:= k) (t:= t0) in H3; try assumption.
Qed.

Lemma nodup_r_str:
  forall c,
    nodup c = true ->
    forall k,
     map c k = None  ->
    forall t, 
      nodup (ctxt k t c) = true.
Proof.
  induction c; try solve [crush].
Qed.

(* Perhaps I want this someday too. *)
(*
Lemma nodup_add_some:
  forall c,
    nodup c = true ->
    forall k t,
     map c k = Some t  ->
    forall t', 
      nodup (add c k t') = true.
*)

Lemma nodup_map_some_context_absurd:
  forall c k t t',
    map c k = Some t ->
    nodup (ctxt k t' c) = true
     -> False.
Proof.
  intros.
  induction c; try solve[crush].
  unfold map in H.
  fold map in H.
  case_eq(K.eqb k e); intros; rewrite H1 in H.
  inversion H; subst.
  apply K.eqb_to_eq in H1.
  rewrite H1 in H0.
  unfold nodup in H0.
  fold nodup in H0.
  simpl in H0.
  rewrite K.eqb_refl in H0.
  inversion H0.
  unfold nodup in H0.
  fold nodup in H0.
  simpl in H0.
  rewrite H1 in H0.
  rewrite H in H0.
  inversion H0.
Qed.  

Lemma map_extension_disagreement_absurd:
  forall c c',
    extends c c' = true ->
    forall v t, 
      map c v  = Some t ->
      map c' v = None ->
      False.
Proof.
  intros c c' ext.
  functional induction (extends c c'); try solve [crush].
  intros.
  apply IHb with (v:= v) (t:= t0) in ext; try assumption.
  unfold map in H.
  fold map in H.
  case_eq(K.eqb v k); intros; rewrite H1 in H; try assumption.
  apply K.eqb_to_eq in H1.
  subst.
  rewrite e0 in H0.
  inversion H0.
Qed.
  
Lemma map_add_recursion:
  forall c k t k',
    map (add c k' t) k = Some t ->
    K.eqb k k' = false ->
    map c k = Some t.
Proof.
  intros.
  induction c.
  simpl in H.
  rewrite H0 in H.
  inversion H.
  unfold map.
  fold map.
  case_eq(K.eqb k e); intros.
  apply K.eqb_to_eq in H1.
  subst.
  unfold add in H.
  fold add in H.
  rewrite K.eqb_sym in H0.
  rewrite H0 in H.
  unfold map in H.
  fold map in H.
  rewrite K.eqb_refl in H.
  assumption.
  unfold add in H.
  fold add in H.
  case_eq(K.eqb k' e); intros; rewrite H2 in H.
  unfold map in H.
  fold map in H.
  rewrite H0 in H.
  assumption.
  unfold map in H.
  fold map in H.
  rewrite H1 in H.
  apply IHc in H.
  assumption.
Qed.

Lemma extends_r_weak:
  forall c c' k t, 
    extends c (ctxt k t c') = true -> 
    nodup (ctxt k t c') = true ->
    map c k = None -> 
    extends c c' = true.
Proof.
  intros.
  induction c; try solve[crush].
  unfold extends in H.
  fold extends in H.
  unfold extends.
  fold extends.
  case_eq(map c' e); intros;
  case_eq(map (ctxt k t c') e); intros; rewrite H3 in H; try solve[inversion H].
  case_eq(T.eqb t0 t1); intros; try rewrite H4 in *; try solve[inversion H].
  case_eq(T.eqb t0 t2); intros;rewrite H5 in H; try solve[inversion H].
  unfold map in H1.
  fold map in H1.
  case_eq(K.eqb k e); intros; rewrite H6 in H1; try inversion H1.
  apply IHc in H; try assumption.
  case_eq(T.eqb t0 t2); intros; rewrite H5 in H; try solve[inversion H].
  apply T.eqb_to_eq in H5.
  subst.
  unfold map in H3.
  fold map in H3.
  unfold map in H1.
  fold map in H1.
  case_eq(K.eqb k e); intros.
  rewrite K.eqb_sym in H3.
  rewrite H5 in *.
  inversion H1.

  rewrite K.eqb_sym in H5.
  rewrite H5 in *.
  apply T.eqb_to_neq in H4.
  rewrite H2 in H3.
  inversion H3.
  crush.
(*  apply T.eqb_to_eq in H4.
  subst. *)
  unfold map in H3.
  fold map in H3.
  unfold map in H1.
  fold map in H1.
  case_eq(K.eqb e k); intros.
  rewrite K.eqb_sym in H1.
  rewrite H4 in *.
  inversion H1.

  rewrite K.eqb_sym in H1.
  rewrite H4 in *.
  rewrite H2 in H3.
  inversion H3.
Qed.

Lemma map_disagreement_absurd:
  forall c k t,
    nodup c = true -> 
    map c k = Some t ->
    forall k' t', 
    map (ctxt  k' t' c) k = None ->
  False.
Proof.  
  intros.
  assert (Z: extends c (ctxt k' t' c) = true).
  assert (Y: extends c c = true).
  apply extends_refl; try assumption.
  apply extends_r_str with (v:= k') (t:= t') in Y; try assumption.
  unfold nodup.
  fold nodup.
  case_eq(map c k'); intros; try assumption.
  unfold map in H1.
  fold map in H1.
  case_eq(K.eqb k k'); intros; rewrite H3 in H1; try solve [inversion H1].
  rewrite H1 in H0.
  inversion H0.
  apply map_extension_disagreement_absurd with (v:= k) (t:= t) in Z; try assumption.
Qed.

Lemma map_add_disagreement_absurd:
  forall c k t,
    map c k = Some t ->
    forall k' t', 
    map (add c k' t') k = None ->
  False.
Proof.  
  intros c.
  induction c; try solve [crush].
  intros.
  unfold map in H.
  fold map in H.
  unfold add in H0.
  fold add in H0.
  case_eq(K.eqb k e); case_eq(K.eqb k' e); intros; rewrite H1 in H0; rewrite H2 in H.
  apply K.eqb_trans with (x:= k') in H1.
  apply K.eqb_to_eq in H2.
  subst.
  unfold map in H0.
  fold map in H0.
  rewrite K.eqb_sym in H1.
  apply K.eqb_to_eq in H1.
  subst.
  rewrite K.eqb_refl in H0.
  inversion H0.
  apply K.eqb_refl.  
  apply K.eqb_to_eq in H2.
  subst.
  unfold map in H0.
  fold map in H0.
  rewrite K.eqb_refl in H0.
  inversion H0.
  unfold map in H0.
  fold map in H0.
  case_eq (K.eqb k k'); intros; rewrite H3 in H0.
  inversion H0.
  rewrite H0 in H.
  inversion H0.
  inversion H.
  unfold map in H0.
  fold map in H0.
  rewrite H2 in H0.
  apply IHc with (k':= k') (t':= t') in H; try assumption.
Qed.

Lemma map_add_some_agreement:
  forall c k t,
    map c k = Some t ->
    forall k0 t0,
      K.eqb k k0 = false ->
      map (add c k0 t0) k = Some t.
Proof.
  intros.
  functional induction (add c k0 t0); try solve [crush].
  unfold map.
  fold map.
  rewrite H0.
  apply K.eqb_to_eq in e0.
  subst.
  unfold map in H.
  fold map in H.
  rewrite H0 in H.
  assumption.

  unfold map in H.
  fold map in H.
  unfold map.
  fold map.
  case_eq(K.eqb k k'); intros; rewrite H1 in H.
  assumption.

  apply IHc0 in H; try assumption.
Qed.

Lemma extends_r_str_add:
  forall c c', 
    extends c c' = true -> 
    forall k t, 
      map c k = None -> 
      extends c (add c' k t) = true.
Proof.
  (* extends *)
  intros c c'.
  functional induction (extends c c'); try solve [crush].
  intros.
  pose proof e1 as e1'.
  apply T.eqb_to_eq in e1.
  subst.
  unfold map in H0.
  fold map in H0.
  case_eq(K.eqb k0 k); intros; rewrite H1 in H0.
  inversion H0.
  apply IHb with (k:= k0) (t:= t0) in H; try assumption.
  apply extends_l_weak; try assumption.
  apply map_add_some_agreement; try assumption.
  rewrite K.eqb_sym in H1.
  assumption.
Qed.

Lemma map_extends_some_agreement:
  forall c v t, 
    map c v  = Some t ->
    nodup c = true ->
    forall c',
      extends c c' = true -> 
      nodup c' = true ->
      map c' v = Some t.
Proof.
  intros.
  functional induction (extends c c'); try solve [crush].
  unfold map in H.
  fold map in H.
  unfold nodup in H0.
  fold nodup in H0.
  case_eq(K.eqb v k); intros; rewrite H3 in H.
  inversion H.
  subst.
  case_eq(map c'' k); intros; rewrite H4 in H0.
  inversion H0.
  clear H.
  apply K.eqb_to_eq in H3.
  apply T.eqb_to_eq in e1.
  subst.
  assumption.
  case_eq(map c'' k); intros; rewrite H4 in H0.
  inversion H0.
  apply IHb in H; try assumption.
Qed.

Lemma map_none_r_str:
  forall c v v',
   map c v  = None ->
   map c v' = None ->
   K.eqb v' v = false ->
   forall t, 
     map (ctxt v t c) v' = None.
Proof.
  intros.
  induction c.
  unfold map.
  fold map.
  rewrite H1.
  reflexivity.
  refold map.
  refold_in map H.
  refold_in map H0.
  case_eq(K.eqb v e); intros; rewrite H2 in *;
  case_eq(K.eqb v' e); intros; rewrite H3 in *;
  case_eq(K.eqb v' v); intros; rewrite H4 in *;
  try solve[inversion H];
  try solve[inversion H0];
  try solve[inversion H1].
  apply IHc in H; try assumption.
Qed.

Lemma map_none_r_weak:
  forall k k' t c,
    map (ctxt k t c) k' = None ->
    K.eqb k' k = false ->
    map c k' = None.
Proof.
  intros.
  unfold map in H.
  fold map in H.
  rewrite H0 in H.
  assumption.
Qed.

Lemma extends_trans:
  forall c c' c'',
    nodup c = true ->
    extends c  c'  = true ->
    nodup c' = true ->
    extends c' c'' = true ->
    nodup c'' = true ->
    extends c  c'' = true.
Proof.
  (* triple induction *)
  intros c c' c'' nodupc extendscc' nodupc' extendsc'c'' nodupc''.
  induction c; try solve [crush]; induction c'; try solve [crush]; induction c''; try solve [crush].
  move extendscc' after IHc''.
  move extendsc'c'' after extendscc'.
  pose proof extendscc' as H'.
  apply extends_l_str in extendscc'.
  inversion nodupc.
  case_eq (map c e); intros; rewrite H in H0; try solve[inversion H0].
  rewrite H0.
  apply IHc in H0; try assumption.
  apply extends_l_weak with (k:= e) (t:= t).
  assumption.

  unfold map.
  fold map.
  case_eq (K.eqb e e1); intros.
  apply K.eqb_to_eq in H1.
  rewrite <- H1 in extendsc'c''.
  rewrite <- H1 in H0.
  rewrite <- H1 in nodupc''.

(* Naming mess up. 
  assert (Z: map (ctxt t t0 c) t = Some t0).
  simpl.
  rewrite K.eqb_refl.
  reflexivity.

  apply map_extends_some_agreement with (v:= k) (t:= t) in H'; try assumption.
  apply map_extends_some_agreement with (v:= k) (t:= t) in extendsc'c'';
    try assumption.
  unfold map in extendsc'c''.
  fold map in extendsc'c''.
  rewrite K.eqb_refl in extendsc'c''.
  assumption.

  assert (Z: map (ctxt k t c) k = Some t).
  unfold map.
  fold map.
  rewrite K.eqb_refl.
  reflexivity.
  apply map_extends_some_agreement with (v:= k) (t:= t) in H';
    try assumption.
  apply map_extends_some_agreement with (v:= k) (t:= t) in extendsc'c'';
    try assumption.
  unfold map in extendsc'c''.
  fold map in extendsc'c''.
  rewrite H1 in extendsc'c''.
  assumption.
*)
Admitted.

Lemma equal_refl:
  forall c,
    nodup c = true ->
    equal c c = true.
Proof.
  intros.
  unfold equal.
  apply andb_true_iff.
  split.
  apply extends_refl; try assumption.
  apply extends_refl; try assumption.
Qed.

Lemma equal_sym:
  forall c c',
    equal c c' = equal c' c.
Proof.
  intros.
  unfold equal.
  crush.
Qed.

Lemma equal_trans:
  forall c c' c'',
    nodup c = true ->
    equal c  c'  = true ->
    nodup c' = true ->
    equal c' c'' = true ->
    nodup c'' = true ->
    equal c  c'' = true.
Proof.
  intros c c' c'' nodupc equalcc' nodupc' equalc'c'' nodupc''.
  unfold equal in equalcc'.
  apply andb_true_iff in equalcc'.
  inversion equalcc'.
  unfold equal in equalc'c''.
  apply andb_true_iff in equalc'c''.
  inversion equalc'c''.
  unfold equal.
  apply andb_true_iff.

  split.
  intros.
  apply extends_trans with (c:= c) (c':= c') (c'':= c'') in H; try assumption.
  apply extends_trans with (c:= c'') (c':= c') (c'':= c) in H0; try assumption.
Qed.

Lemma equal_implies_extends:
  forall d d',
    equal d d' = true ->
    extends d d' = true.
Proof.
  unfold equal.
  intros.
  apply andb_true_iff in H.
  inversion H.
  assumption.
Qed.

(* It would be nice if these were true but they're not unless I cannonicalize. *)
Lemma equal_eq:
  forall c c',
    equal c c' = true ->
    c = c'.
Admitted.

Lemma equal_neq:
  forall c c',
    equal c c' = false ->
    c <> c'.
Admitted.

Lemma equal_empty_only_empty:
  forall c,
    equal empty c = true ->
    c = empty.
Proof.
  intros.
  unfold equal in H.
  apply andb_true_iff in H.
  inversion H.
  apply empty_extends_only_empty in H1.
  assumption.
Qed.

Lemma equal_if_map_some:
  forall c c',
    nodup c  = true ->
    nodup c' = true->
    equal c c' = true ->
    (forall k t, map c k = Some t -> map c' k = Some t).
Proof.
  intros c c'.
  functional induction (equal c c').
  intros.
  apply andb_true_iff in H1.
  inversion H1.
  apply map_extends_some_agreement with (c':= c') in H2; try assumption.
Qed.

Lemma equal_iff_map_some:
  forall c c',
    nodup c  = true ->
    nodup c' = true ->
    equal c c' = true ->
    (forall k t, map c k = Some t <-> map c' k = Some t).
Proof.
  intros.

  split.
  intros.
  apply equal_if_map_some with (c:= c) (c':= c') (k:= k) (t:= t) in H; try assumption.
  
  intros.
  rewrite equal_sym in H1.
  apply equal_if_map_some with (c:= c') (c':= c) (k:= k) (t:= t) in H; try assumption.
Qed.

(* Admitting alpha conversion in the most specific ways:
    that x is not in a context and that
    x is not equal to x'. *)
Lemma admit_alpha_conversion_context:
  forall v c,
    map v c = None.
Admitted.

Lemma admit_alpha_conversion_beq_t:
  forall k k',
    K.eqb k k' = false.
Admitted.

End ContextFun.