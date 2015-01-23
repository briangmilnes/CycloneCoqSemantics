(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  An attempt at a full context model, no modules. 

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.
Require Import Coq.Init.Logic.
Require Import Coq.Bool.Bool.

Require Export CpdtTactics.
Require Export Case.
Require Export TacticNotations.

Set Implicit Arguments.

Lemma beq_nat_sym : forall (n m : nat),
                      beq_nat n m = beq_nat m n.
Proof.
  apply NPeano.Nat.eqb_sym.
Qed.

(* Why is this not in a standard library? *)
Lemma beq_nat_trans : 
  forall n1 n2 n3, 
    beq_nat n1 n2 = true ->
    beq_nat n2 n3 = true -> 
    beq_nat n1 n3 = true.
Proof.
  induction n1; destruct n2;
  induction n3; simpl; auto. intros. inversion H.
  apply IHn1.
Qed.

Inductive TVar : Type :=
 | tvar   : nat -> TVar.

Function beq_tvar (x y : TVar) : bool :=
   match x, y with
     | (tvar x'), (tvar y') => beq_nat x' y'
  end.

Lemma beq_tvar_refl:
 forall (alpha : TVar),
   beq_tvar alpha alpha = true.
Proof.
  intros.
  destruct alpha.
  unfold beq_tvar.
  apply eq_sym.
  apply beq_nat_refl.
Qed.
Hint Resolve beq_tvar_refl.

Lemma beq_tvar_sym : forall x y : TVar, beq_tvar x y = beq_tvar y x.
Proof.
  intros.
  destruct x.
  destruct y.
  unfold beq_tvar.
  rewrite beq_nat_sym.
  reflexivity.
Qed.
Hint Immediate beq_tvar_sym.

Lemma beq_tvar_trans : 
  forall x y z,
    beq_tvar x y = true -> beq_tvar y z = true -> beq_tvar x z = true.
Proof.
   destruct x.
   destruct y.
   destruct z.
   apply beq_nat_trans.
Qed.
Hint Resolve beq_tvar_trans.

Lemma beq_tvar_eq:
  forall (alpha beta : TVar),
    beq_tvar alpha beta = true ->
    alpha = beta.
Proof.
  destruct alpha. 
  destruct beta.
  simpl.
  intros.
  symmetry in H.
  apply beq_nat_eq in H.
  rewrite H.
  reflexivity.
Qed.
Hint Resolve beq_tvar_eq.

Lemma beq_tvar_neq:
  forall (alpha beta : TVar),
    beq_tvar alpha beta = false ->
    alpha <> beta.
Proof.
  intros.
  case_eq (beq_tvar alpha beta).
  intros.
  destruct alpha; destruct beta.
  unfold beq_tvar in H.
  unfold beq_tvar in H0.
  apply beq_nat_false in H.
  congruence.
  intros.
  destruct alpha; destruct beta.  
  unfold beq_tvar in H.
  fold beq_tvar in H.
  apply beq_nat_false in H.
  congruence.
Qed.  
Hint Resolve beq_tvar_neq.

Inductive Tau : Type :=
 | tv_t   : TVar -> Tau                             
 | cint   : Tau
 | cross  : Tau -> Tau -> Tau.

Tactic Notation "Tau_ind_cases" tactic(first) ident(c) :=
 first;
[ Case_aux c "(tv_t t)"
| Case_aux c "cint"
| Case_aux c "(cross t t0)"
].

Function beq_tau (t t' : Tau) : bool :=
 match t, t' with
 | tv_t alpha, tv_t beta => beq_tvar alpha beta
 | cint, cint => true
 | (cross t0 t1), (cross t0' t1') => andb (beq_tau t0 t0') (beq_tau t1 t1')
 | _ , _ => false
end.

Lemma beq_tau_refl:
 forall (t : Tau),
   beq_tau t t = true.
Proof.
  intros.
  induction t; crush.
Qed.
Hint Resolve beq_tau_refl.

Lemma beq_tau_sym : forall x y, beq_tau x y = beq_tau y x.
Proof.
  induction x; induction y; try solve [crush].
Qed.
Hint Immediate beq_tau_sym.

Lemma beq_tau_trans : 
  forall x y z, 
    beq_tau x y = true -> beq_tau y z = true -> beq_tau x z = true.
Proof.
  induction x; induction y; induction z; intros; try solve [inversion H]; try solve [inversion H0].
  inversion H. inversion H0.
  crush.
  apply beq_tvar_trans with (x:= t) (y:= t0) (z:= t1) in H2; try assumption.
  reflexivity.
  unfold beq_tau.
  fold beq_tau.
  unfold beq_tau in H.
  fold beq_tau in H.
  unfold beq_tau in H0.
  fold beq_tau in H0.
  apply andb_true_iff in H.
  apply andb_true_iff in H0.
  inversion H.
  inversion H0.
  apply andb_true_iff.
  apply IHx1 with (z:= z1)in H1; try assumption.
  apply IHx2 with (z:= z2)in H2; try assumption.
  split; try assumption.
Qed.
Hint Resolve beq_tau_trans.

Lemma beq_tau_eq:
  forall t0 t1, beq_tau t0 t1 = true -> t0 = t1.
Proof.
  induction t0; induction t1; intros; try solve [inversion H].
  inversion H.
  apply beq_tvar_eq in H1.
  rewrite H1.
  reflexivity.
  reflexivity.
  clear IHt1_1.
  clear IHt1_2.
  unfold beq_tau in H.
  fold beq_tau in H.
  apply andb_true_iff in H.
  inversion H.
  apply IHt0_1 in H0.
  apply IHt0_2 in H1.
  subst.
  reflexivity.
Qed.

Lemma beq_tau_neq:
  forall t0 t1, beq_tau t0 t1 = false -> t0 <> t1.
Proof.
  induction t0; induction t1; intros; try solve [inversion H]; try solve [discriminate].
  apply beq_tvar_neq in H.
  crush.
  unfold beq_tau in H.
  fold beq_tau in H.
  apply andb_false_iff in H.
  destruct H.
  apply IHt0_1 in H.
  crush.
  apply IHt0_2 in H.
  crush.
Qed.  

Definition K    := TVar.
Definition K_eq := beq_tvar.
Definition T    := Tau.
Definition T_eq := beq_tau.

Inductive Context (K : Type) (T : Type) : Type :=
| Ctxt_dot  : Context K T
| Ctxt      : K -> T -> Context K T -> Context K T.

Tactic Notation "Context_ind_cases" tactic(first) ident(c) :=
 first;
[ Case_aux c "(Ctxt_dot K T)"
| Case_aux c "(Ctxt k t c)"
].

Definition empty  := Ctxt_dot K T.

Function add (c : Context K T) (k: K) (t : T)  : Context K T :=
  match c with
    | Ctxt_dot => (Ctxt k t (Ctxt_dot K T))
    | (Ctxt k' t' c') =>
      match K_eq k k' with
        | true  => (Ctxt k  t  c')
        | false => (Ctxt k' t' (add c' k t))
      end
  end.

Function map (c : Context K T) (k: K) : option T :=
  match c with
    | Ctxt_dot => None
    | (Ctxt k' t' c') =>
      match K_eq k k' with
        | true  => Some t'
        | false => (map c' k)
      end
  end.

Functional Scheme map_ind2 := Induction for map Sort Prop.

Function map' (c : Context K T) (k: K) : option T :=
  match k, c with
    | k'', (Ctxt k' t' c') =>
      if K_eq k'' k'
      then Some t'
      else (map' c' k)
    | _, Ctxt_dot => None
  end.

Function nodup (c : (Context K T)) : bool :=
  match c with
    | Ctxt_dot => true
    | (Ctxt k' t' c') =>
      match map c' k' with
        | Some t  => false
        | None  => nodup c'
      end
end.

Function nodup' (c : (Context K T)) : bool :=
  match c with
    | Ctxt_dot => true
    | (Ctxt k' t' c') =>
      match map' c' k' with
        | Some t  => false
        | None  => nodup' c'
      end
end.

Function extends (c c' : Context K T) : bool :=
  match c with 
    | Ctxt_dot => true
    | Ctxt k t c'' =>
      match map c' k with
       | Some t => extends c'' c' 
       | None => false
      end
  end.

Function extends' (c c' : Context K T) : bool :=
  match c with 
    | Ctxt_dot => true
    | Ctxt k t c'' =>
      match map' c' k with
       | Some t => extends' c'' c' 
       | None => false
      end
  end.

Function equal (c c' : Context K T) : bool :=
  andb (extends c c') (extends c' c).

Lemma map_empty_none: forall k, map empty k = None.
Proof.
  crush.
Qed.

Lemma NoDup_empty: nodup empty = true.
Proof.
  crush.
Qed.

Lemma map_add: forall c k t, map (add c k t) k = Some t.
Proof.
  intros.
  induction c.
  Case "Ctxt_dot".
   crush.
   rewrite beq_tvar_refl.
   reflexivity.
  Case "(Ctxt k0 t0 c)".
   crush.
   case_eq (K_eq k k0).
   SCase "K_eq k k0 = true".
    intros.
    unfold map.
    rewrite beq_tvar_refl.
    reflexivity.
   SCase "K_eq k k0 = false".
    intros.
    unfold map.
    rewrite H.
    fold map.
    assumption.
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

(* I'm not checking the correctness of c' but it works. *)
Lemma extends_r_strengthen:
  forall c c', 
    extends c c' = true -> 
    forall v t, 
      extends c (Ctxt v t c') = true.
Proof.
  intros c c' ext; induction c; try solve [crush].
  intros.
  unfold extends.
  fold extends.
  unfold map.
  fold map.
  unfold extends in ext.
  fold extends in ext.
  unfold map in ext.
  fold map in ext.
  case_eq(map c' k); case_eq(K_eq k v); intros; rewrite H0 in ext.
  apply IHc with (v:=v) (t:= t0) in ext; try assumption.  
  apply IHc with (v:=v) (t:= t0) in ext; try assumption.
  inversion ext.
  inversion ext.
Qed.

Lemma extends_refl:
  forall c, extends c c = true.
Proof.
  intros.
  induction c; try solve [crush].
  unfold extends.
  fold extends.
  simpl.
  rewrite beq_tvar_refl.
  apply extends_r_strengthen; try assumption.
Qed.

Lemma extends_l_weaken:
  forall c c' k,
    extends c c' = true -> 
    forall t,
      map c' k = Some t ->
      extends (Ctxt k t c) c' = true.
Proof.
  intros.
  unfold extends.
  fold extends.
  unfold map.
  fold map.
  rewrite H0.
  assumption.
Qed.

Lemma extends_l_weaken_r_strengthen:
  forall c c' k,
    extends c c' = true -> 
    map c' k = None  -> 
    forall t, 
      extends (Ctxt k t c) (Ctxt k t c') = true.
Proof.
  intros.
  unfold extends.
  fold extends.
  unfold map.
  fold map.
  rewrite beq_tvar_refl.
  apply extends_r_strengthen; try assumption.
Qed.

Lemma extends_l_strengthen: 
  forall c c' k t, 
    extends (Ctxt k t c) c' = true -> extends c c' = true.
Proof.
 intros.
 Context_ind_cases(induction c) Case; try solve [crush].
 Case  "(Ctxt k t c)".
  unfold extends in H.
  fold extends in H.
  case_eq (map c' k); intros.
  SCase "map c' v = Some t".
   intros.
   rewrite H0 in H.
   case_eq (map c' k0).
   SSCase "map c' k0 = Some t2".
    intros.
    rewrite H1 in H.
    unfold extends.
    rewrite H1.
    fold extends.
    assumption.
   SSCase "map c' k0 = None".
    intros.
    rewrite H1 in H.
    inversion H.
  SCase "map c' k0 = None".
   intros.
   rewrite H0 in H.
   inversion H.
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
  case_eq (K_eq v k); intros.
  apply beq_tvar_eq in H0.
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

Lemma K_eq_sym:  forall k k', K_eq k k' = K_eq k' k.
Proof.
  apply beq_tvar_sym.
Qed.  

Lemma map_r_strengthen_context:
  forall c k0 t0 k t,
    map (Ctxt k0 t0 c) k = Some t -> 
    K_eq k0 k = false -> 
    map c k = Some t.
Proof.
  intros.
  unfold map in H.
  fold map in H.
  rewrite K_eq_sym in H0.
  rewrite H0 in H.
  assumption.
Qed.

Lemma map_r_strengthen_add:
  forall c k0 t0 k t,
    map (add c k0 t0) k = Some t ->
    K_eq k k0 = false -> 
    map c k = Some t.
Proof.
  (* c, map add *)
(* map , stuck 
  intros.
  functional induction (map (add c k0 t0) k).
  inversion H.
*)  
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
  case_eq(K_eq k0 k1); case_eq(K_eq k k1); intros; rewrite H2 in H.
  apply beq_tvar_trans with (x:= k) in H1.
  apply beq_tvar_eq in H1.
  subst.
  rewrite beq_tvar_sym in H0.
  apply beq_tvar_eq in H2.
  subst.
  rewrite beq_tvar_refl in H0.
  inversion H0.

  apply beq_tvar_refl.
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

Lemma nodup_add:
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
  case_eq (map c k); intros; rewrite H1 in H; try inversion H.
  unfold map in H0.
  fold map in H0.
  case_eq (K_eq k0 k); intros; rewrite H2 in H0.
  inversion H0.
  unfold add.
  fold add.
  rewrite H2.
  unfold nodup.
  fold nodup.
  rewrite H3.  
  case_eq (map (add c k0 t0) k); intros.
  apply map_r_strengthen_add in H4; try assumption.
  rewrite H4 in H1.
  inversion H1.
  apply IHc with (k:= k0) (t:= t0) in H; try assumption.
  rewrite beq_tvar_sym in H2; try assumption.
  apply IHc with (k:= k0) (t:= t0) in H; try assumption.
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
  apply IHb with (v:= v) (t:= t1) in ext; try assumption.
  unfold map in H.
  fold map in H.
  case_eq(K_eq v k); intros; rewrite H1 in H; try assumption.
  apply beq_tvar_eq in H1.
  subst.
  rewrite e0 in H0.
  inversion H0.
Qed.
  
Lemma extends_r_weaken:
  forall c c' k t, 
    extends c (Ctxt k t c') = true -> 
    map c k = None -> 
    extends c c' = true.
Proof.
  intros c.
  induction c; try solve [crush].
  intros.
  specialize (IHc c' k0 t0).
  unfold extends in H.
  fold extends in H.
  unfold extends.
  fold extends.
  case_eq(map c' k); case_eq (map (Ctxt k0 t0 c') k); intros.
  rewrite H1 in H.
  apply IHc in H; try assumption.
  unfold map in H0.
  fold map in H0.
  case_eq (K_eq k0 k); intros.
  rewrite H3 in H0.
  inversion H0.
  rewrite H3 in H0; try assumption.
  rewrite H1 in H.
  inversion H.
  rewrite H1 in H.
  unfold map in H1.
  fold map in H1.
  case_eq(K_eq k k0); intros.
  rewrite H3 in H1.
  unfold map in H0.
  fold map in H0.
  rewrite K_eq_sym in H3.
  rewrite H3 in H0.
  inversion H0.
  rewrite H3 in H1.
  rewrite H1 in H2.
  inversion H2.
  rewrite H1 in H.
  inversion H.
Qed.

Lemma map_disagreement_absurd:
  forall c k t,
    map c k = Some t ->
    forall k' t', 
    map (Ctxt  k' t' c) k = None ->
  False.
Proof.  
  intros.
  assert (Z: extends c (Ctxt k' t' c) = true).
  assert (Y: extends c c = true).
  apply extends_refl.
  apply extends_r_strengthen with (v:= k') (t:= t') in Y; try assumption.
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
  case_eq(K_eq k0 k); case_eq(K_eq k' k); intros; rewrite H1 in H0; rewrite H2 in H.
  apply beq_tvar_trans with (x:= k') in H1.
  apply beq_tvar_eq in H2.
  subst.
  unfold map in H0.
  fold map in H0.
  rewrite beq_tvar_sym in H1.
  apply beq_tvar_eq in H1.
  subst.
  rewrite beq_tvar_refl in H0.
  inversion H0.
  apply beq_tvar_refl.  
  apply beq_tvar_eq in H2.
  subst.
  unfold map in H0.
  fold map in H0.
  rewrite beq_tvar_refl in H0.
  inversion H0.
  unfold map in H0.
  fold map in H0.
  case_eq (K_eq k0 k'); intros; rewrite H3 in H0.
  inversion H0.
  rewrite H0 in H.
  inversion H0.
  inversion H.
  unfold map in H0.
  fold map in H0.
  rewrite H2 in H0.
  apply IHc with (k':= k') (t':= t') in H; try assumption.
Qed.

Lemma extends_r_strengthen_add: 
  forall c c', 
    extends c c' = true -> 
    forall k t, 
      extends c (add c' k t) = true.
Proof.
  intros c c'.
  functional induction (extends c c'); try solve [crush].
  intros.
  apply IHb with (k:= k0) (t:= t1) in H.
  unfold extends.
  fold extends.
  case_eq (map (add c' k0 t1) k); intros; try assumption.
  apply map_add_disagreement_absurd with (k':= k0) (t':= t1)in e0; try assumption.
  inversion e0.
Qed.  

Lemma map_extends_some_agreement:
  forall c c',
   extends c c' = true -> 
   nodup c = true ->
   nodup c' = true ->
   forall v t, 
     map c v  = Some t ->
     map c' v = Some t.
Admitted.

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
  apply extends_l_strengthen in extendscc'.
  inversion nodupc.
  case_eq (map c k); intros; rewrite H in H0; try solve[inversion H0].
  rewrite H0.
  apply IHc in H0; try assumption.
  apply extends_l_weaken with (k:= k) (t:= t).
  assumption.

  unfold map.
  fold map.
  case_eq (K_eq k k1); intros.
  apply beq_tvar_eq in H1.
  rewrite <- H1 in extendsc'c''.
  rewrite <- H1 in H0.
  rewrite <- H1 in nodupc''.
  assert (Z: map (Ctxt k t c) k = Some t).
  simpl.
  rewrite beq_tvar_refl.
  reflexivity.
  apply map_extends_some_agreement with (v:= k) (t:= t) in H'; try assumption.
  apply map_extends_some_agreement with (v:= k) (t:= t) in extendsc'c'';
    try assumption.
  unfold map in extendsc'c''.
  fold map in extendsc'c''.
  rewrite beq_tvar_refl in extendsc'c''.
  assumption.

  assert (Z: map (Ctxt k t c) k = Some t).
  unfold map.
  fold map.
  rewrite beq_tvar_refl.
  reflexivity.
  apply map_extends_some_agreement with (v:= k) (t:= t) in H';
    try assumption.
  apply map_extends_some_agreement with (v:= k) (t:= t) in extendsc'c'';
    try assumption.
  unfold map in extendsc'c''.
  fold map in extendsc'c''.
  rewrite H1 in extendsc'c''.
  assumption.
Qed.

Lemma equal_refl:
  forall c,
    equal c c = true.
Proof.
  intros.
  unfold equal.
  apply andb_true_iff.
  split.
  apply extends_refl.
  apply extends_refl.
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

(* It would be nice if these were true but they're not. *)
(* jrw I'd have to introduce ordering to get these, do I reall need it? *)
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

Lemma equal_if_map:
  forall c c',
    nodup c = true ->
    nodup c' = true ->
    equal c c' = true ->
    (forall k o, map c k = o -> map c' k = o).
Proof.
  (* c, c', c&c', equal won't work but extends, map also. *)
  intros.
  functional induction (map c k).
  apply equal_empty_only_empty in H.
  rewrite H.
  rewrite <- H0.
  reflexivity.

  apply beq_tvar_eq in e0.
  subst.
  unfold equal in H.
  apply andb_true_iff in H.
  inversion H.
  assert (Z: map (Ctxt k' t' c'0) k' = Some t').
  simpl.
  (* jrw why won't it simplify using K_eq as tvar_beq_refl? *)
  rewrite beq_tvar_refl.
  reflexivity.
  apply map_extends_some_agreement with (v:= k') (t:= t') in H0; try assumption.
  (* strengthen with nodup. *)
  admit.
  admit.
  unfold equal in H.
  apply andb_true_iff in H.
  inversion H.
  apply extends_l_strengthen in H1.
  (* apply map_extends_some_agreement with (v:= ) (t:= ) in H1; try assumption. *)
  (* close but perhaps not there. *)
Admitted.

Lemma equal_iff_map:
  forall c c',
    equal c c' = true ->
    (forall k o, map c k = o <-> map c' k = o).
Proof.
  intros.

  split.
  intros.
  apply equal_if_map with (k:= k) (o:= o) in H; try assumption.
  
  intros.
  rewrite equal_sym in H.
  apply equal_if_map with (k:= k) (o:= o) in H; try assumption.
Qed.

(* If I can't get map agreement with extends as a function, I have to go
 back to relations for extensions. *)
Lemma m:
  forall c v t,
    map' c v  = Some t ->
    nodup' c = true ->
    forall c',
      nodup' c' = true ->
      extends' c c' = true -> 
      map' c' v = Some t.
Proof.
  intros c v t.
  functional induction (map' c v).
  Case "Some k0 = k0".
   intros.
   apply beq_tvar_eq in e1.
   inversion H.
   subst.
   inversion H2.
   case_eq (map' c'0 k'); intros; rewrite H3 in H4.
   admit.
   inversion H4.
  Case "getD d' alpha = Some k".
   intros.
   inversion H0.
   inversion H2.
   case_eq(map' c' k'); case_eq (map' c'0 k'); intros; rewrite H3 in H5; rewrite H6 in H4.
   inversion H4.
   inversion H4.
   admit.
   admit.
  Case "None = Some".
  intros.
  inversion H.
Admitted.

Lemma map_extends_some_agreement_map:
  forall c v t,
    map c v  = Some t ->
    nodup c = true ->
    forall c',
      extends c c' = true -> 
      nodup c' = true ->
      map c' v = Some t.
Proof.
  intros c v t.
  intros.
  pose proof H as H'.
  functional induction (map c v).
  inversion H.

  apply extends_l_strengthen with (k:= k') (t:= t') in H1.
  unfold nodup in H0.
  fold nodup in H0.
  case_eq(map c'0 k'); intros; rewrite H3 in H0.
  inversion H0.
  apply beq_tvar_eq in e0.
  subst.
  (* Nothing to work on, need a map to invert with. *)
  (* I should have map c'0 k' = Some t, to invert against
     mapc'0 k' = None. *)
  (* but it gets rewritten by the induction even if I save it. *)
  assert (Z: map c'0 k' = Some t).
  admit. 
  rewrite H3 in Z.
  inversion Z.

  apply extends_l_strengthen with (k:= k') (t:= t') in H1.
  unfold nodup in H0.
  fold nodup in H0.
  case_eq(map c'0 k'); intros; rewrite H3 in H0.
  inversion H0.
  apply IHo in H; try assumption.
Qed.


(* Try with a functional scheme. *)
Lemma map_extends_some_agreement_map_ind2:
  forall c v t,
    map c v  = Some t ->
    nodup c = true ->
    forall c',
      extends c c' = true -> 
      nodup c' = true ->
      map c' v = Some t.
Proof.
  intros c v t.
  intros.
  pose proof H as H'.
  pattern c, v, (map c v).
  apply map_ind2.
  intros.
  (* disconnected, hence unprovable. *)
  admit.
  intros.
  admit.
  intros.
  admit.
Qed.

Lemma map_extends_some_agreement_fun_ind:
  forall c c',
   extends c c' = true -> 
   nodup c = true ->
   nodup c' = true ->
   forall v t, 
     map c v  = Some t ->
     map c' v = Some t.
Proof.
 (* map *)
  intros c c' ext nodupc nodupc' v t.
  functional induction (map c v); try solve [crush].
  intros.
  inversion H.
  apply beq_tvar_eq in e0.
  subst.

  admit. (* Don't see how to prove this. *)
(*  
  intros.
  pose proof nodupc as Z.
  unfold nodup in nodupc.
  fold nodup in nodupc.
  case_eq (map c'0 k'); intros; rewrite H0 in nodupc.
  inversion nodupc.
  

 (* c, ext, map *)
  intros c c' ext.
  functional induction (extends c c'); try solve [crush].
  intros.
  apply IHb with (v:= v) (t:= t1) in ext; try assumption.
  unfold nodup in H.
  fold nodup in H.
  case_eq (map c'' k); intros; rewrite H2 in H.
  inversion H.
  assumption.
  pose proof H1 as H1'.
  unfold map in H1.
  fold map in H1.
  case_eq(K_eq v k); intros; rewrite H2 in H1.
  inversion H1.
  subst.
  unfold nodup in H.
  fold nodup in H.
  case_eq (map c'' k); intros; rewrite H3 in H.
  inversion H.
  apply beq_tvar_eq in H2.
  subst.
  admit. (* It's just not invalidatable. *)
  assumption.
*)
(* c 
  intros c.
  induction c; try solve [crush].

  intros.
  unfold extends in H.
  fold extends in H.
  unfold map in H2.
  fold map in H2.
  inversion H0.
  case_eq (map c k); intros;  rewrite H3 in H4; try inversion H4.
  case_eq(map c' k); 
  case_eq(K_eq v k); 
  intros; rewrite H5 in H2; rewrite H7 in H;
  try solve [inversion H];
  apply IHc with (t:= t0) (v:= v) in H; 
  try assumption.

  apply beq_tvar_eq in H5.
  subst.
  inversion H2.
  subst.
  admit. (* Can't invalidate, Stuck *)
*)

Admitted.


Fixpoint map'' (c : Context K T) (k: K) : option T :=
  match k, c with
    | k'', (Ctxt k' t' c') =>
      if K_eq k'' k'
      then Some t'
      else (map'' c' k)
    | _, Ctxt_dot => None
  end.

Functional Scheme map''_ind := Induction for map'' Sort Prop.

Function extends'' (c c' : Context K T) : bool :=
  match c with 
    | Ctxt_dot => true
    | Ctxt k t c'' =>
      match map'' c' k with
       | Some t => extends'' c'' c' 
       | None => false
      end
  end.

Fixpoint nodup'' (c : (Context K T)) : bool :=
  match c with
    | Ctxt_dot => true
    | (Ctxt k' t' c') =>
      match map'' c' k' with
        | Some _  => false
        | None  => nodup'' c'
      end
end.

Lemma map_extends_some_agreement_fschem_ind:
  forall c c',
   extends'' c c' = true -> 
   nodup'' c = true ->
   nodup'' c' = true ->
   forall v t, 
     map'' c v  = Some t ->
     map'' c' v = Some t.
Proof.
  intros c c' ext nodupc nodupc' v t map''cv.
  functional induction (map'' c v).
  admit.
  admit. (* bad *)
  admit. (* ? *)
Admitted.

Lemma map_extends_some_agreement_fschem_ind_diff_order:
  forall c v t, 
   map'' c v  = Some t ->
   nodup'' c = true ->
   forall c',
     extends'' c c' = true -> 
     nodup'' c' = true ->
     map'' c' v = Some t.
Proof.
  intros.
  functional induction (map'' c v).
  admit.
  admit. (* bad *)
  admit. (* ? *)
Admitted.


(* https://stackoverflow.com/questions/20554493/coq-induction-over-functions-without-losing-information *)

Lemma map''_extends_some_agreement_remember:
  forall c v t, 
   map'' c v  = Some t ->
   nodup'' c = true ->
   forall c',
     extends'' c c' = true -> 
     nodup'' c' = true ->
     map'' c' v = Some t.
Proof.
  intros.
  remember (map'' c v) as F.
  functional induction (map'' c v). 
  admit. (* bad *)
  admit. (* bad *)
  admit. (* ? *)
Admitted.

Lemma map_extends_some_agreement_remember:
  forall c v t, 
   map c v  = Some t ->
   nodup c = true ->
   forall c',
     extends c c' = true -> 
     nodup c' = true ->
     map c' v = Some t.
Proof.
  intros.
  remember (map c v) as F.
  induction F.
  admit. (* bad *)
  admit. (* bad *)
Admitted.

Lemma map_extends_some_agreement_remember_as:
  forall c v t, 
   map c v  = Some t ->
   nodup c = true ->
   forall c',
     extends c c' = true -> 
     nodup c' = true ->
     map c' v = Some t.
Proof.
  intros.
  (* pose (Z := (map c v)). No *)
  set (map c v).
  functional induction (map c v).
  admit. (* bad *)
  admit. (* bad *)
  admit. (* ? *)
Admitted.

Lemma map_extends_some_agreement_remember_revert:
  forall c v t, 
   map c v  = Some t ->
   nodup c = true ->
   forall c',
     extends c c' = true -> 
     nodup c' = true ->
     map c' v = Some t.
Proof.
  intros.
  remember (map c v = Some t) as Fn.
  functional induction (map c v).
  admit. (* bad *)
  admit. (* bad *)
  admit. (* ? *)
Admitted.

Lemma map_extends_some_agreement_1:
  forall c v t, 
   map c v  = Some t ->
   nodup c = true ->
   forall c',
     extends c c' = true -> 
     nodup c' = true ->
     map c' v = Some t.
Proof.
  intros.
  destruct (map c v).
  admit. (* bad *)
  admit. (* bad *)
Admitted.

Lemma map_extends_some_agreement_2:
  forall c v t, 
   map c v  = Some t ->
   nodup c = true ->
   forall c',
     extends c c' = true -> 
     nodup c' = true ->
     map c' v = Some t.
Proof.
  intros.
  induction c, v, (map c v) using map_ind.
  admit. (* bad *)
  admit. (* bad *)
  admit.
Admitted.


Function map3 (k: K) (c : Context K T) : option T :=
  match k, c with
    | k'', (Ctxt k' t' c') =>
      match K_eq k'' k' with 
      | true => Some t'
      | false => (map3 k c')
      end
    | _, Ctxt_dot => None
end.


Function extends3 (c c' : Context K T) : bool :=
  match c with 
    | Ctxt_dot => true
    | Ctxt k t c'' =>
      match map3 k c'  with
       | Some t => extends'' c'' c' 
       | None => false
      end
  end.

Function nodup3 (c : (Context K T)) : bool :=
  match c with
    | Ctxt_dot => true
    | (Ctxt k' t' c') =>
      match map3 k' c' with
        | Some _  => false
        | None  => nodup3 c'
      end
end.

Lemma map_extends_some_agreement_3:
  forall c v t, 
   map3 v c = Some t ->
   nodup3 c = true ->
   forall c',
     extends3 c c' = true -> 
     nodup3 c' = true ->
     map3 v c' = Some t.
Proof.
  intros.
  functional induction (map3 v c).
  admit. (* bad. *)
  admit. (* good, is it argument order or the match ? *)
  admit.
Admitted.

Lemma map_extends_some_agreement_4:
  forall c v t, 
   map3 v c = Some t ->
   nodup3 c = true ->
   forall c',
     extends3 c c' = true -> 
     nodup3 c' = true ->
     map3 v c' = Some t.
Proof.
  intros.
  remember (map3 v c) as HailMary.
  induction v, c, HailMary using map3_ind.
  admit. (* ? *)
  admit. (* ? *)
  admit.
Admitted.

Lemma map_extends_some_agreement_5:
  forall c v t, 
   map c v = Some t ->
   nodup c = true ->
   forall c',
     extends c c' = true -> 
     nodup c' = true ->
     map c' v = Some t.
Proof.
  intros c v t.
  remember (map c v = Some t) as mapcv.
  induction c, v, mapcv using map_ind.
  intros.
  rewrite Heqmapcv in H.
  inversion H.

  intros.
  rewrite Heqmapcv in H.
  move H after H2.
  move H1 after H2.
  move e0 after H2.
  move H0 after c'0.
  apply beq_tvar_eq in e0.
  rewrite e0.
  rewrite e0 in H.
  clear e.
  clear Heqmapcv.
  clear e0.
  pose proof H as H'.
  unfold map in H'.
  fold map in H'.
  rewrite beq_tvar_refl in H'.
  inversion H'.
  subst.
  clear H'.

  induction c'0.
  

  admit. (* Still stuck. *)

(*
  intros.
  apply extends_l_strengthen with (k:= k') (t:= t') in H1.
  unfold nodup in H0.
  fold nodup in H0.
  case_eq(map c' k'); intros.
  rewrite H3 in H0.
  inversion H0.
  unfold map in Heqmapcv.
  fold map in Heqmapcv.
  rewrite e0 in Heqmapcv.
  rewrite H3 in H0.
  apply IHmapcv with (c'0:= c'0) in Heqmapcv; try assumption.
*)
Admitted.


Lemma map_extends_some_agreement_6:
  forall c v o t,
   map c v = o ->
   nodup c = true ->
   o = Some t ->
   forall c',
     extends c c' = true -> 
     nodup c' = true ->
     map c' v = o.
Proof.
  intros c v o t.
  functional induction (map c v).
  admit. (* bad *)
  admit. (* bad *)
  admit. (* bad *)
Qed.


Lemma map_extends_some_agreement_7:
  forall c v t, 
   map c v = Some t ->
   nodup c = true ->
   forall c',
     extends c c' = true -> 
     nodup c' = true ->
     map c' v = Some t.
Proof.
  intros c v t.
  functional induction (map c v); try solve [crush].
  intros.
  inversion H.
  apply beq_tvar_eq in e0.
  subst.

Lemma map_extends_some_agreement_8_extends:
  forall c v t,
    map c v = Some t ->
    forall c', 
      extends c c' = true -> 
      nodup c = true ->
      nodup c' = true ->
      map c' v = Some t.
Proof.
  intros c v t mapcvt c'.
  pose proof mapcvt as X.
  functional induction (extends c c'); try solve [crush].
  intros.
  inversion H0.
  case_eq(map c'' k); intros; rewrite H2 in H3.
  inversion H3.

  unfold map in mapcvt.
  fold map in mapcvt.
  case_eq(K_eq v k); intros; rewrite H4 in mapcvt.
  apply beq_tvar_eq in H4.
  subst.
  inversion mapcvt.
  subst.
  admit. (* need to invert but the context is consistent. *)

  apply IHb in mapcvt; try assumption.
Qed.  


Lemma map_extends_some_agreement_8_map':
  forall c c',
    extends' c c' = true -> 
    nodup' c = true ->
    nodup' c' = true ->
    forall v t, 
      map' c v = Some t ->
      map' c' v = Some t.
Proof.
  intros c c'.
  functional induction (extends' c c'); try solve [crush].
  intros.
  inversion H0.
  case_eq(map' c'' k); intros; rewrite H3 in H4.
  inversion H4.

  apply IHb with (v:= v) (t:= t1) in H; try assumption.
  case_eq(K_eq v k); intros.
  apply beq_tvar_eq in H5.
  subst.
  admit. (* need to invert but the context is consistent. *)

  unfold map' in H2.
  fold map' in H2.
  rewrite H5 in H2.
  assumption.
Qed.  


Inductive maptr: (Context K T) -> K -> T -> Prop :=
  | maptr1: 
      forall c k t,
        map c k = Some t ->
        maptr c k t.

Function maptf (c : Context K T) (k: K) (t : T): bool := 
  match c with
    | Ctxt_dot => false
    | (Ctxt k' t' c') =>
      match K_eq k k' with
        | true  => beq_tau t t'
        | false => (maptf c' k t)
      end
  end.

Lemma map_extends_some_agreement_9_maptf:
  forall c v t,
   maptf c v t = true ->
   nodup c = true ->
   forall c',
     extends c c' = true -> 
     nodup c' = true ->
     map c' v = Some t.
Proof.
  intros c v t.
  remember (maptf c v t = true) as X.
  functional induction (maptf c v t); try solve [crush].
  intros.
  admit.  (* bad *)
  admit. 
Admitted.

(* Totally useless. *)
Lemma map_extends_some_agreement_10_maptr:
  forall c v  t,
   maptr c v t ->
   nodup c = true ->
   forall c',
     extends c c' = true -> 
     nodup c' = true ->
     map c' v = Some t.
Proof.
  intros c v t maptrder.
  induction maptrder.
Admitted.

(* The last approach is to build the map relation, prove it equivalent
and induct on it. *)

Inductive mapits: (Context K T) -> K -> T -> Prop :=
  | mapits_top     : forall c k t,
                       mapits (Ctxt k t c) k t
  | mapits_recurse : forall k' c k t t',
                       mapits c k t ->
                       mapits (Ctxt k' t' c) k t.

Lemma map_extends_some_agreement_11_mapits:
  forall c v  t,
   mapits c v t ->
   nodup c = true ->
   forall c',
     extends c c' = true -> 
     nodup c' = true ->
     map c' v = Some t.
Proof.
  intros c v t mapitder.
  induction mapitder.
  intros.
  admit.
  intros.
  (* perhaps *)
Admitted.

(* Or I can go the way that worked for getD, functional induction but
 an extends relation. *)

Inductive extendsr : (Context K T) -> (Context K T) -> Prop := 
  | extendsr_empty   : forall c,
                         extendsr empty c
  | extendsr_left  : 
      forall c c' k t,
        map c' k = Some t ->
        extendsr c c' ->
        extendsr (Ctxt k t c) c'.

(* Is it really NoDup that has to be a relation also? *)
Lemma map_extends_some_agreement_12_extendsr:
  forall c k  t,
   map c k = Some t ->
   nodup c = true ->
   forall c',
     nodup c' = true ->
     extendsr c c' -> 
     map c' k = Some t.
Proof.
  intros c k t.
  functional induction (map c k).
  intros.
  inversion H.
  Case "Some k0 = k0".
   intros.
   inversion H.
   clear H.
   pose proof e0 as e0'.
   apply beq_tvar_eq in e0.
   subst.
   inversion H2.
   assumption.
  Case "getD d' alpha = Some k".
   intros.
   inversion H0. 
   inversion H2.
   subst.
   apply IHo with (c'0 := c'0) in H; try assumption.
   case_eq(map c' k'); intros; rewrite H3 in H4.
   inversion H4.
   assumption.
Qed.

Lemma map_extends_some_agreement_12_functional_inversion_on_extends:
  forall c k  t,
   map c k = Some t ->
   nodup c = true ->
   forall c',
     extends c c' = true -> 
     nodup c' = true ->
     map c' k = Some t.
Proof.
  intros c v t.
  intros.
  pose proof H as H'.
  functional induction (map c v).
  inversion H.

  apply beq_tvar_eq in e0.
  inversion H'.
  subst.
  clear H'.
  clear H.
  functional inversion H1.
  subst.

  admit.

(*
  assert (Z: map c'0 k' = Some t).
  admit. 
  rewrite H3 in Z.
  inversion Z.
*)

  apply extends_l_strengthen with (k:= k') (t:= t') in H1.
  unfold nodup in H0.
  fold nodup in H0.
  case_eq(map c'0 k'); intros; rewrite H3 in H0.
  inversion H0.
  apply IHo in H; try assumption.
Admitted.



