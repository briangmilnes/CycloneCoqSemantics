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

Function nodup (c : (Context K T)) : bool :=
  match c with
    | Ctxt_dot => true
    | (Ctxt k' t' c') =>
      match map c' k' with
        | Some _  => false
        | None  => nodup c'
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
  forall c v v', 
    map c v  = None ->
    forall t, 
      map c v' = Some t ->
      v <> v'.
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

Lemma equal_iff_map:
  forall c c',
    equal c c' = true ->
    (forall k o, map c k = o <-> map c' k = o).
Proof.
  intros.
  unfold equal in H.
  apply andb_true_iff in H.
  inversion H.
  (* induction c; induction c'; try solve [crush]. Yucko last goal. *)
Admitted.

Lemma map_extends_some_agreement:
  forall c c',
   extends c c' = true -> 
   nodup c = true ->
   nodup c' = true ->
   forall v t, 
     map c v  = Some t ->
     map c' v = Some t.
Proof.
  intros c.
  induction c; try solve [crush].

  intros.
  unfold extends in H.
  fold extends in H.
  unfold map in H2.
  fold map in H2.
  case_eq(map c' k); case_eq(K_eq v k); intros; rewrite H3 in H2; rewrite H4 in H.
  apply beq_tvar_eq in H3.
  inversion H2.
  subst.
  admit.
  


  (* c, c', ext, map *)

(*
(* c  *)
  intros c.
  induction c; try solve [crush].

  intros.
  inversion H0.
  unfold extends in H.
  fold extends in H.
  case_eq(map c' k); intros; rewrite H3 in H; try solve [inversion H].
  unfold nodup in H0.
  fold nodup in H0.
  case_eq(ink c k); intros;  rewrite H5 in *; try solve [inversion H4]; try solve [inversion H0].
  apply IHc with (v:= v) (t:= t0) in H; try assumption.
  pose proof H2 as H2'.
  unfold map in H2.
  fold map in H2.
  case_eq(K_eq v k); intros; rewrite H6 in H2; try assumption.
  apply beq_tvar_eq in H6.
  subst.

  (* Seems stuck. *)
*)

(*
(* ext. *)
  intros c c' ext nodupc nodupc'.
  functional induction (extends c c'); try solve [crush].

  intros.
  unfold nodup in nodupc.
  fold nodup in nodupc.
  case_eq(ink c'' k); intros; rewrite H0 in nodupc; try inversion nodupc.
  pose proof H as H'.
  unfold map in H.
  fold map in H.
  case_eq (K_eq v k); intros; rewrite H1 in H.
  inversion H.
  apply beq_tvar_eq in H1.
  subst.
  admit. (* Stuck. *)
  apply IHb with (v:= v) (t:= t1) in nodupc; try assumption.
*)

(* (* c'  *)
  intros c'.
  induction c'.
  intros.
  apply empty_extends_only_empty in H1.
  subst.
  inversion H2.

  intros.
  inversion H0.
  unfold map.
  fold map.
*)

(*  map. 
  intros.
  functional induction (map c v); try solve [crush].
  (* stuck. *)
*)

Admitted.


