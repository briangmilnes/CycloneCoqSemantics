(*
Inductive In (k : K) : Context K T ->  Prop := 
| In_hd : forall k' t' c, K_eq k k' = true -> In k (Ctxt k' t' c)
| In_tl : forall k' t' c, K_eq k k' = false -> In k c -> In k (Ctxt k' t' c).
Hint Constructors In.

Inductive  NoDup : Context K T -> Prop :=
| NoDup_dot  : NoDup (Ctxt_dot K T)
| NoDup_ctxt : forall k t c,
                 NoDup c ->
                 ~In k c ->
                 NoDup (Ctxt k t c).
Hint Constructors NoDup.

Function ink (c : Context K T) (k: K) : bool :=
  match c with
    | Ctxt_dot => false
    | (Ctxt k' t' c') =>
      match K_eq k k' with
        | true  => true
        | false => (ink c' k)
      end
  end.
*)


(*

Function inkt (c : Context K T) (k: K) (t : T) : bool :=
  match c with
    | Ctxt_dot => false
    | (Ctxt k' t' c') =>
      match K_eq k k' with
        | true => match T_eq t t' with | true => true | false => (inkt c' k t) end
        | false => (inkt c' k t)
      end
  end.

Function extends (c c' : Context K T) : bool :=
  match c with 
    | Ctxt_dot => true
    | Ctxt k t c'' =>
      if inkt c' k t 
      then extends c'' c' 
      else false
  end.

*)


Lemma NoDup_inkt_absurd:
  forall k t t' c,
    NoDup (Ctxt k t c) ->
    inkt c k t' = true ->
    False.
Proof.
  intros k t t' c NoDupder inktder.
  functional induction (inkt c k t').
  inversion inktder.
  apply beq_tvar_eq in e0.
  subst.
  inversion NoDupder; try assumption.
  crush.
  apply beq_tvar_eq in e0.
  subst.
  inversion NoDupder; try assumption.
  crush.
  apply IHb in inktder.
  inversion inktder.
  inversion NoDupder.
  subst.
  constructor; try assumption.
  inversion H1; try assumption.
  inversion NoDupder.
  subst.
  crush.
Qed.

Lemma inkt_t_weakening:
  forall c k t, inkt c k t = true -> ink c k = true.
Proof.
  intros.
  Context_ind_cases(induction c) Case.
 Case  "(Ctxt_dot K T)".
  crush.
 Case  "(Ctxt k t c)".
  crush.
  case_eq (K_eq k k0).
  SCase " K_eq k k0 = true".
   intros.
   reflexivity.
  SCase " K_eq k k0 = false".
   intros.
   rewrite H0 in H.
   apply IHc in H.
   assumption.
Qed.

Lemma map_some_weakening: 
  forall c c' t v,  map c v = Some t -> extends c c' = true ->  map c' v = Some t.
Proof.
  intros.
  functional induction (map c v).
  inversion H.
  inversion H.
  subst.
  apply beq_tvar_eq in e0.
  subst.
  unfold extends in H0.
  fold extends in H0.
  case_eq (inkt c' k' t).
  intros.
  rewrite H1 in H0.
  apply inkt_map_agreement; try assumption.
  intros.
  rewrite H1 in H0.
  inversion H0.
  apply IHo in H; try assumption.
  unfold extends in H0.
  fold extends in H0.
  case_eq (inkt c' k' t').
  intros.
  rewrite H1 in H0; try assumption.
  intros.
  rewrite H1 in H0; try assumption.
  inversion H0.
Qed.


Functional Scheme map_ind2 := Induction for map Sort Prop.

Function map' (c : Context K T) (k: K) : option T :=
  match k, c with
    | k'', (Ctxt k' t' c') =>
      if K_eq k'' k'
      then Some t'
      else (map' c' k)
    | _, Ctxt_dot => None
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



Function extends' (c c' : Context K T) : bool :=
  match c with 
    | Ctxt_dot => true
    | Ctxt k t c'' =>
      match map' c' k with
       | Some t => extends' c'' c' 
       | None => false
      end
  end.


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


Lemma extends_iff_extendsr:
  forall c c',
    extendsr c c' <-> extends c c' = true.
Proof.
  intros c c'.
  split.
  intros extendsrder.
  induction extendsrder.
  apply empty_extended_by_all.
  unfold extends.
  fold extends.
  rewrite H.
  assumption.

(*
  intros extendsder.
  functional induction (extends c c').
  constructor.
  apply IHb in extendsder.
  constructor; try assumption.
  admit.
  inversion extendsder.
*)
  induction c.
  intros.
  constructor.
  intros.
  unfold extends in H.
  fold extends in H.
  case_eq(map c' k); intros; rewrite H0 in H.
  apply IHc in H.
  constructor.
  admit.
  assumption.
  inversion H.
Qed.


Lemma extends_r_strengthen_add: 
  forall c c', 
    nodup c = true ->
    extends c c' = true -> 
    forall k t, 
      nodup (add c'k t) = true ->
      extends c (add c' k t) = true.
Proof.
  intros c c'.
  functional induction (extends c c'); try solve [crush].
  intros.
  pose proof H0 as H0'.
  unfold nodup in H0.
  fold nodup in H0.
  pose proof H as H'.
  unfold nodup in H.
  fold nodup in H.
  case_eq(map c'' k); intros; rewrite H2 in H; try solve[inversion H].
  unfold extends.
  fold extends.
  case_eq(map (add c' k0 t0) k); intros.
  case_eq(T_eq t t1); intros.
  apply IHb with (k:= k0) (t:= t0) in H; try assumption.
  apply beq_tau_eq in e1.
  subst.
  case_eq(K_eq k0 k); intros.
  apply beq_tvar_eq in H5.
  subst.  
  
  admit.
  move e0 after H3.
(*
  apply beq_tau_eq in e1.
  subst.
  case_eq(K_eq k0 k); intros.
  apply beq_tvar_eq in H4.
  subst.
  rewrite e0 in H1.
  inversion H1.
*)
  admit.


(* before nodup 
  intros c c'.
  functional induction (extends c c'); try solve [crush].
  intros.
  apply IHb with (k:= k0) (t:= t) in H.
  unfold extends.
  fold extends.
  case_eq (map (add c' k0 t0) k); intros; try assumption.
  apply map_add_disagreement_absurd with (k':= k0) (t':= t1) in e0; try assumption.
  inversion e0.
  apply beq_tau_eq in e1.
  subst.
  admit. (* Just looks false, probably need a nodup. *)
  case_eq(K_eq k0 k); intros.
  apply beq_tvar_eq in H1.
  subst.
  (* H0 should invert. *)
  admit.
  apply beq_tau_eq in e1.
  subst.
  (* e0 and H0 should invert. *)
*)
Admitted.

Lemma extends_r_strengthen_add': 
  forall c c', 
    nodup c = true ->
    nodup c' = true ->
    extends c c' = true -> 
    forall k t, 
      map c' k = None ->
      extends c (add c' k t) = true.
Proof.
  intros c c'.
  functional induction (extends c c'); try solve [crush].
  intros.
  unfold nodup in H.
  fold nodup in H.
  case_eq(map c'' k); intros; rewrite H3 in H; try solve[inversion H].
  apply IHb with (k:= k0) (t:= t0) in H; try assumption.
  unfold extends.
  fold extends.
  case_eq(map (add c' k0 t0) k); intros.
  case_eq(T_eq t t1); intros.
  apply beq_tau_eq in e1.
  subst.
  admit.
  apply beq_tau_eq in e1.
  subst.
  admit.
  move e0 before H4.
  admit.
Admitted.

Lemma extends_r_strengthen_add'': 
  forall c c', 
    nodup c = true ->
    nodup c' = true ->
    extends c c' = true -> 
    forall k t, 
      map c' k = None ->
      extends c (add c' k t) = true.
Proof.
  intros c.
  induction c; try solve [crush].
  intros.
  pose proof H as H'.
  unfold nodup in H.
  fold nodup in H.
  case_eq(map c k); intros; rewrite H3 in *; try inversion H.
  unfold extends in H1.
  fold extends in H1.
  case_eq(map c' k); intros; rewrite H4 in H1; try solve[inversion H1].
  case_eq(T_eq t t1); intros; rewrite H6 in H1; try solve[inversion H1].
  unfold extends.
  fold extends.
  case_eq(map (add c' k0 t0) k); intros.
  case_eq(T_eq t t2); intros.
  specialize (IHc c' H H0 H1 k0 t0 H2).
  rewrite H5.
  assumption.
  (* two invalidations. *)
  case_eq(K_eq k0 k); intros.
  unfold nodup in H'.
  fold nodup in H'.
  rewrite H3 in H'.
  admit.
  admit.
Admitted.
