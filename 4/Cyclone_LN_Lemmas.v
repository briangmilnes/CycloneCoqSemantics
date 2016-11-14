(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION".   Daniel Grossman, August 2003 *)
(* Lemmas for LN infrastructure *)
(* Brian Milnes 2016 *)

Set Implicit Arguments.
Require Export Cyclone_Type_Substitution Cyclone_LN_FV Cyclone_LN_LC_Body Cyclone_LN_Open_Close Cyclone_LN_Tactics.

(* Opening type variables in types. *)
Lemma open_rec_tau_core:
  forall t i j u v,
    i <> j ->
      (open_rec_tau j v t) = (open_rec_tau i u (open_rec_tau j v t)) ->
      t = (open_rec_tau i u t).
Proof.
  induction t; introv Neq Equ; inversion* Equ; simpls; fequals*.
  case_nat*.
  case_nat*.
Qed.

(* Opening type variables in terms. *)

Lemma open_rec_tau_term_v_core:
  forall t i j  u v,
    i <> j ->
      (open_rec_tau_term_v j v t) = (open_rec_tau_term_v i u (open_rec_tau_term_v j v t)) ->
      t = (open_rec_tau_term_v i u t).
Proof.
  induction t; introv Neq Equ; inversion* Equ; simpls*.
Qed.

Ltac inversion_on_matching_terms :=
  match goal with
    | H: (?C _) = (?C _) |- _ => inversion H
    | H: (?C _ _) = (?C _ _) |- _ => inversion H
    | H: (?C _ _ _) = (?C _ _ _) |- _ => inversion H                                           
  end.

Lemma open_rec_tau_term_st_core:
  forall t i j u v,
    i <> j ->
    (open_rec_tau_term_st j v t) = (open_rec_tau_term_st i u (open_rec_tau_term_st j v t)) ->
    t = (open_rec_tau_term_st i u t).
Proof.
  apply (St_ind_mutual 
           (fun t : St => 
              forall i j u v,
                i <> j ->
                (open_rec_tau_term_st j v t) = (open_rec_tau_term_st i u (open_rec_tau_term_st j v t)) ->
                t = (open_rec_tau_term_st i u t))
           (fun t : E  => 
              forall i j u v,
                i <> j ->
                (open_rec_tau_term_e j v t) = (open_rec_tau_term_e i u (open_rec_tau_term_e j v t)) ->
                t = (open_rec_tau_term_e i u t))
           (fun t : F  => 
              forall i j u v,
                i <> j ->
                (open_rec_tau_term_f j v t) = (open_rec_tau_term_f i u (open_rec_tau_term_f j v t)) ->
                t = (open_rec_tau_term_f i u t)));
  intros;
  simpl in *;
  fequals*;
  simpl in *;
  try inversion_on_matching_terms;
  try solve[fequals*];
  try apply open_rec_tau_term_v_core with (j:= j) (v:= v0); try assumption;
  apply open_rec_tau_core with (j:= j) (v:= v); try assumption.
Qed.


Lemma open_rec_tau_term_e_core:
  forall t i j u v,
    i <> j ->
    (open_rec_tau_term_e j v t) = (open_rec_tau_term_e i u (open_rec_tau_term_e j v t)) ->
    t = (open_rec_tau_term_e i u t).
Proof.
  apply (E_ind_mutual 
           (fun t : St => 
              forall i j u v,
                i <> j ->
                (open_rec_tau_term_st j v t) = (open_rec_tau_term_st i u (open_rec_tau_term_st j v t)) ->
                t = (open_rec_tau_term_st i u t))
           (fun t : E  => 
              forall i j u v,
                i <> j ->
                (open_rec_tau_term_e j v t) = (open_rec_tau_term_e i u (open_rec_tau_term_e j v t)) ->
                t = (open_rec_tau_term_e i u t))
           (fun t : F  => 
              forall i j u v,
                i <> j ->
                (open_rec_tau_term_f j v t) = (open_rec_tau_term_f i u (open_rec_tau_term_f j v t)) ->
                t = (open_rec_tau_term_f i u t)));
  intros;
  simpl in *;
  fequals*;
  simpl in *;
  try inversion_on_matching_terms;
  try solve[fequals*];
  try apply open_rec_tau_term_v_core with (j:= j) (v:= v0); try assumption;
  apply open_rec_tau_core with (j:= j) (v:= v); try assumption.
Qed.

Lemma open_rec_tau_term_f_core:
  forall t i j u v,
    i <> j ->
    (open_rec_tau_term_f j v t) = (open_rec_tau_term_f i u (open_rec_tau_term_f j v t)) ->
    t = (open_rec_tau_term_f i u t).
Proof.
  apply (F_ind_mutual 
           (fun t : St => 
              forall i j u v,
                i <> j ->
                (open_rec_tau_term_st j v t) = (open_rec_tau_term_st i u (open_rec_tau_term_st j v t)) ->
                t = (open_rec_tau_term_st i u t))
           (fun t : E  => 
              forall i j u v,
                i <> j ->
                (open_rec_tau_term_e j v t) = (open_rec_tau_term_e i u (open_rec_tau_term_e j v t)) ->
                t = (open_rec_tau_term_e i u t))
           (fun t : F  => 
              forall i j u v,
                i <> j ->
                (open_rec_tau_term_f j v t) = (open_rec_tau_term_f i u (open_rec_tau_term_f j v t)) ->
                t = (open_rec_tau_term_f i u t)));
  intros;
  simpl in *;
  fequals*;
  simpl in *;
  try inversion_on_matching_terms;
  try solve[fequals*];
  try apply open_rec_tau_term_v_core with (j:= j) (v:= v0); try assumption;
  apply open_rec_tau_core with (j:= j) (v:= v); try assumption.
Qed.

Lemma open_rec_term_core:
  forall t i j u v,
    i <> j ->
    (open_rec_tau_term j v t) = (open_rec_tau_term i u (open_rec_tau_term j v t)) ->
    t = (open_rec_tau_term i u t).
Proof.
  induction t; introv neq equ;
  simpl;
  fequals*;
  inversion equ.
  apply open_rec_tau_term_st_core with (j:= j) (v:= v); assumption.
  apply open_rec_tau_term_e_core with (j:= j) (v:= v); assumption.
  apply open_rec_tau_term_f_core with (j:= j) (v:= v); assumption.
Qed.

Lemma open_rec_term_v_core:
  forall t i j  u v,
    i <> j ->
      (open_rec_term_v j v t) = (open_rec_term_v i u (open_rec_term_v j v t)) ->
      t = (open_rec_term_v i u t).
Proof.
  induction t; introv Neq Equ; inversion* Equ; simpls*.
  case_nat*.
  case_nat*.
Qed.

Lemma open_rec_term_p_core:
  forall t i j  u v,
    i <> j ->
      (open_rec_term_p j v t) = (open_rec_term_p i u (open_rec_term_p j v t)) ->
      t = (open_rec_term_p i u t).
Proof.
  induction t; introv Neq Equ; inversion* Equ; simpls*.
  case_nat*.
  case_nat*.
Qed.

Lemma open_rec_term_st_core:
  forall t i j u v,
    i <> j ->
    (open_rec_term_st j v t) = (open_rec_term_st i u (open_rec_term_st j v t)) ->
    t = (open_rec_term_st i u t).
Proof.
  apply (St_ind_mutual 
           (fun t : St => 
              forall i j u v,
                i <> j ->
                (open_rec_term_st j v t) = (open_rec_term_st i u (open_rec_term_st j v t)) ->
                t = (open_rec_term_st i u t))
           (fun t : E  => 
              forall i j u v,
                i <> j ->
                (open_rec_term_e j v t) = (open_rec_term_e i u (open_rec_term_e j v t)) ->
                t = (open_rec_term_e i u t))
           (fun t : F  => 
              forall i j u v,
                i <> j ->
                (open_rec_term_f j v t) = (open_rec_term_f i u (open_rec_term_f j v t)) ->
                t = (open_rec_term_f i u t)));
  try solve[intros;
            simpl in *;
            inversion_on_matching_terms;
            fequals*;
            try apply open_rec_term_v_core with (j:= j) (v:= v0); auto;
            try apply open_rec_term_p_core with (j:= j) (v:= v0); auto].
Qed.

Lemma open_rec_term_e_core:
  forall t i j u v,
    i <> j ->
    (open_rec_term_e j v t) = (open_rec_term_e i u (open_rec_term_e j v t)) ->
    t = (open_rec_term_e i u t).
Proof.
  apply (E_ind_mutual 
           (fun t : St => 
              forall i j u v,
                i <> j ->
                (open_rec_term_st j v t) = (open_rec_term_st i u (open_rec_term_st j v t)) ->
                t = (open_rec_term_st i u t))
           (fun t : E  => 
              forall i j u v,
                i <> j ->
                (open_rec_term_e j v t) = (open_rec_term_e i u (open_rec_term_e j v t)) ->
                t = (open_rec_term_e i u t))
           (fun t : F  => 
              forall i j u v,
                i <> j ->
                (open_rec_term_f j v t) = (open_rec_term_f i u (open_rec_term_f j v t)) ->
                t = (open_rec_term_f i u t)));
  try solve[intros;
            simpl in *;
            inversion_on_matching_terms;
            fequals*;
            try apply open_rec_term_v_core with (j:= j) (v:= v0); auto;
            try apply open_rec_term_p_core with (j:= j) (v:= v0); auto].
Qed.

Lemma open_rec_term_f_core:
  forall t i j u v,
    i <> j ->
    (open_rec_term_f j v t) = (open_rec_term_f i u (open_rec_term_f j v t)) ->
    t = (open_rec_term_f i u t).
Proof.
  apply (F_ind_mutual 
           (fun t : St => 
              forall i j u v,
                i <> j ->
                (open_rec_term_st j v t) = (open_rec_term_st i u (open_rec_term_st j v t)) ->
                t = (open_rec_term_st i u t))
           (fun t : E  => 
              forall i j u v,
                i <> j ->
                (open_rec_term_e j v t) = (open_rec_term_e i u (open_rec_term_e j v t)) ->
                t = (open_rec_term_e i u t))
           (fun t : F  => 
              forall i j u v,
                i <> j ->
                (open_rec_term_f j v t) = (open_rec_term_f i u (open_rec_term_f j v t)) ->
                t = (open_rec_term_f i u t)));
  try solve[intros;
            simpl in *;
            inversion_on_matching_terms;
            fequals*;
            try apply open_rec_term_v_core with (j:= j) (v:= v0); auto;
            try apply open_rec_term_p_core with (j:= j) (v:= v0); auto].
Qed.

(* Bug bindings of names of LibVar vs LibVarPath. *)
Lemma lc__open_rec_tau_identity:
  forall t,
    lc_tau t -> forall k u, t = (open_rec_tau k u t).
Proof.
  introv lct.
  induction lct; try intros k u; simpl; auto; try solve[congruence].

  (* The two binding cases. *)
  (* Automation failing, BUG beats me why. *)
  introv. fequals.  pick_fresh alpha.
  lets: open_rec_tau_core.
  specialize (H1 t0 (S k0) 0 u (ftvar alpha)).
  applys H1.
  apply Nat.neq_succ_0.
  applys H0.
  LibVar.notin_solve.

  introv. fequals.  pick_fresh alpha.
  lets: open_rec_tau_core.
  specialize (H1 t0 (S k0) 0 u (ftvar alpha)).
  applys H1.
  auto.
  applys H0.
  LibVar.notin_solve.
Qed.

Ltac inversion_on_lc :=
  match goal with
    | H : lc_tau_term_st _ |- _ => inversions H
    | H : lc_tau_term_e  _ |- _ => inversions H
    | H : lc_tau_term_f  _ |- _ => inversions H                                        
  end.

Lemma lc_tau_term_st__open_rec_tau_st_identity:
  forall t,
    lc_tau_term_st t -> forall k u, t = (open_rec_tau_term_st k u t).
Proof.
  apply (St_ind_mutual 
           (fun t : St => 
              lc_tau_term_st t -> forall k u, t = (open_rec_tau_term_st k u t))
           (fun t : E  => 
              lc_tau_term_e t -> forall k u, t = (open_rec_tau_term_e k u t))
           (fun t : F  => 
              lc_tau_term_f t -> forall k u, t = (open_rec_tau_term_f k u t)));
  try solve[intros;
  inversion_on_lc;
  simpl;
  fequals*;
  try solve[apply* lc__open_rec_tau_identity]].
Qed.
        
Lemma lc_tau_term_e__open_rec_tau_st_identity:
  forall t,
    lc_tau_term_e t -> forall k u, t = (open_rec_tau_term_e k u t).
  apply (E_ind_mutual 
           (fun t : St => 
              lc_tau_term_st t -> forall k u, t = (open_rec_tau_term_st k u t))
           (fun t : E  => 
              lc_tau_term_e t -> forall k u, t = (open_rec_tau_term_e k u t))
           (fun t : F  => 
              lc_tau_term_f t -> forall k u, t = (open_rec_tau_term_f k u t)));
  try solve[intros;
  inversion_on_lc;
  simpl;
  fequals*;
  try solve[apply* lc__open_rec_tau_identity]].
Qed.

Lemma lc_tau_term_f__open_rec_tau_st_identity:
  forall t,
    lc_tau_term_f t -> forall k u, t = (open_rec_tau_term_f k u t).
Proof.
  apply (F_ind_mutual 
           (fun t : St => 
              lc_tau_term_st t -> forall k u, t = (open_rec_tau_term_st k u t))
           (fun t : E  => 
              lc_tau_term_e t -> forall k u, t = (open_rec_tau_term_e k u t))
           (fun t : F  => 
              lc_tau_term_f t -> forall k u, t = (open_rec_tau_term_f k u t)));
  try solve[intros;
  inversion_on_lc;
  simpl;
  fequals*;
  try solve[apply* lc__open_rec_tau_identity]].
Qed.

Lemma lc_tau_term__open_rec_tau_identity:
  forall t,
    lc_tau_term t -> forall k u, t = (open_rec_tau_term k u t).
Proof.
  destruct t; intros; simpl; fequals*; inversion H.
  apply* lc_tau_term_st__open_rec_tau_st_identity.
  apply* lc_tau_term_e__open_rec_tau_st_identity.
  apply* lc_tau_term_f__open_rec_tau_st_identity.
Qed.


(* Substitution identity given fresh variables. *)

Lemma subst_tau_fresh : forall x t u, 
  x \notin ftyv_tau t ->  t = (subst_tau u x t).
Proof.
  intros.
  induction t; simpls*;
  first [try solve[case_var*];
         try solve[apply LibVar.notin_union_r in H;
                   inversion H;
                   fequals*];
         try solve[f_equal*]].
Qed.

Lemma subst_tau_v_fresh : forall x t u, 
  x \notin ftyv_v t ->  t = (subst_tau_v u x t).
Proof.
  induction t; simpls*.
Qed.

Lemma subst_tau_st_fresh : forall t x u, 
  x \notin ftyv_st t ->  t = (subst_tau_st u x t).
Proof.
  apply (St_ind_mutual 
           (fun t : St => 
              forall x u,
              x \notin ftyv_st t ->  t = (subst_tau_st u x t))
           (fun t : E  => 
              forall x u,
              x \notin ftyv_e t ->  t = (subst_tau_e u x t))
           (fun t : F  => 
              forall x u,
              x \notin ftyv_f t ->  t = (subst_tau_f u x t)));
  intros;
  simpls*;
  f_equal.
  (* have to break out all of the \notins to individuals *)
  try solve[apply H; try assumption];
  try solve[apply H0; try assumption].





simpls*; introv free; fequals; try solve [applys* subst_tau_v_fresh].
  try first [destruct st | destruct e | destruct f].
  simpl in free.
  simpl.
  fequals*.
  admit.
  admit.
























































Qed.

(** Substitution for a fresh name is identity. *)

Lemma subst_fresh : forall x t u, 
  x \notin fv t ->  [x ~> u] t = t.
Proof.
  intros. induction t; simpls; f_equal*. case_var*. 
Qed.

(** Substitution distributes on the open operation. *)

Lemma subst_open : forall x u t1 t2, term u -> 
  [x ~> u] (t1 ^^ t2) = ([x ~> u]t1) ^^ ([x ~> u]t2).
Proof.
  intros. unfold open. generalize 0.
  induction t1; intros; simpl; f_equal*.
  case_nat*. case_var*. apply* open_rec_term.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma subst_open_var : forall x y u e, y <> x -> term u ->
  ([x ~> u]e) ^ y = [x ~> u] (e ^ y).
Proof.
  introv Neq Wu. rewrite* subst_open.
  simpl. case_var*.
Qed.

(** Opening up an abstraction of body t with a term u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma subst_intro : forall x t u, 
  x \notin (fv t) -> term u ->
  t ^^ u = [x ~> u](t ^ x).
Proof.
  introv Fr Wu. rewrite* subst_open.
  rewrite* subst_fresh. simpl. case_var*.
Qed.

(** Tactic to permute subst and open var *)

Ltac cross := 
  rewrite subst_open_var; try cross.

Tactic Notation "cross" "*" := 
  cross; auto_star.

(* ********************************************************************** *)
(** ** Terms are stable through substitutions *)

(** Terms are stable by substitution *)

Lemma subst_term : forall t z u,
  term u -> term t -> term ([z ~> u]t).
Proof.
  induction 2; simpls*.
  case_var*.
  apply_fresh term_abs as y. rewrite* subst_open_var.
Qed.

Lemma subst_body : forall z u t,
  body t -> term u -> body ([z ~> u]t).
  unfold body. introv [L H]. exists (L \u \{z}).
  intros. rewrite~ subst_open_var. apply* subst_term.
Qed.

Hint Resolve subst_term subst_body.


(* ********************************************************************** *)
(** ** Terms are stable through open *)

(** Conversion from locally closed abstractions and bodies *)

Lemma term_abs_to_body : forall t1, 
  term (trm_abs t1) -> body t1.
Proof.
  intros. unfold body. inversion* H.
Qed.

Lemma body_to_term_abs : forall t1, 
  body t1 -> term (trm_abs t1).
Proof.
  intros. inversion* H.
Qed.

Hint Resolve term_abs_to_body body_to_term_abs.

(** ** Opening a body with a term gives a term *)

Lemma open_term : forall t u,
  body t -> term u -> term (t ^^ u).
Proof.
  intros. destruct H. pick_fresh y. rewrite* (@subst_intro y).
Qed.

Hint Resolve open_term.


(* ********************************************************************** *)
(** ** Additional results on primitive operations *)

(** Open_var with fresh names is an injective operation *)

Lemma open_var_inj : forall x t1 t2, 
  x \notin (fv t1) -> x \notin (fv t2) -> 
  (t1 ^ x = t2 ^ x) -> (t1 = t2).
Proof.
  intros x t1. unfold open. generalize 0.
  induction t1; intro k; destruct t2; simpl; intros; inversion H1;
  try solve [ f_equal* 
  | |-  do 2 try case_nat; inversions* H1; try notin_false ].
Qed.

(** Close var commutes with open with some freshness conditions,
  this is used in the proofs of [close_var_body] and [close_var_open] *)

Lemma close_var_rec_open : forall x y z t1 i j,
  i <> j -> y <> x -> y \notin (fv t1) ->
    {i ~> trm_fvar y} ({j ~> trm_fvar z} (close_var_rec j x t1) )
  = {j ~> trm_fvar z} (close_var_rec j x ({i ~> trm_fvar y}t1) ).
Proof.
  induction t1; simpl; intros; try solve [ f_equal* ].
  do 2 (case_nat; simpl); try solve [ case_var* | case_nat* ]. 
  case_var*. simpl. case_nat*. 
Qed.

(** Close var is an operation returning a body of an abstraction *)

Lemma close_var_fresh : forall x t,
  x \notin fv (close_var x t).
Proof.
  introv. unfold close_var. generalize 0.
  induction t; intros k; simpls; notin_simpl; auto.
  case_var; simpls*.
Qed.

(** Close var is an operation returning a body of an abstraction *)

Lemma close_var_body : forall x t,
  term t -> body (close_var x t).
Proof.
  introv W. exists \{x}. intros y Fr.
  unfold open, close_var. generalize 0. gen y.
  induction W; intros y Fr k; simpls.
  case_var; simpls*. case_nat*.
  auto_star.
  apply_fresh* term_abs as z.
   unfolds open. rewrite* close_var_rec_open.
Qed.

(** Close var is the right inverse of open_var *)

Lemma close_var_open : forall x t,
  term t -> t = (close_var x t) ^ x.
Proof.
  introv W. unfold close_var, open. generalize 0.
  induction W; intros k; simpls; f_equal*.
  case_var*. simpl. case_nat*.
  let L := gather_vars in match goal with = ?t => 
    destruct (var_fresh (L \u fv t)) as [y Fr] end.
  apply* (@open_var_inj y).
  unfolds open. rewrite* close_var_rec_open.
Qed.
 
(** An abstract specification of close_var, which packages the
  result of the operation and all the properties about it. *)

Lemma close_var_spec : forall t x, term t -> 
  exists u, t = u ^ x /\ body u /\ x \notin (fv u).
Proof.
  intros. exists (close_var x t). splits 3.
  apply* close_var_open.
  apply* close_var_body.
  apply* close_var_fresh.
Qed. 
