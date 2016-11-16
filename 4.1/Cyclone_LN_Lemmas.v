(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION".   Daniel Grossman, August 2003 *)
(* Lemmas for LN infrastructure *)
(* Brian Milnes 2016 *)

Set Implicit Arguments.
Require Export Cyclone_Type_Substitution Cyclone_LN_FV Cyclone_LN_LC_Body Cyclone_LN_Open_Close Cyclone_LN_Tactics.

(* TODO: 
     TOC
     more reasonable lemma naming.
     notation
     applys- why did this get dropped? what does it do?
     all: tactic.
     ltac:(some_tactic) - gallina expression evaluates to the terms from the tactic.     
     Think about variable only substitution for some of the lemmas.
*)

(* Opening type variables in types. *)
Lemma open_rec_t_core:
  forall t i j u v,
    i <> j ->
      (open_rec_t_t j v t) = (open_rec_t_t i u (open_rec_t_t j v t)) ->
      t = (open_rec_t_t i u t).
Proof.
  induction t; introv Neq Equ; inversion* Equ; simpls; fequals*.
  case_nat*.
  case_nat*.
Qed.

(* Opening type variables in terms. *)

Lemma open_rec_t_tm_v_core:
  forall t i j  u v,
    i <> j ->
      (open_rec_t_tm_v j v t) = (open_rec_t_tm_v i u (open_rec_t_tm_v j v t)) ->
      t = (open_rec_t_tm_v i u t).
Proof.
  induction t; introv Neq Equ; inversion* Equ; simpls*.
Qed.

Ltac inversion_on_matching_terms :=
  match goal with
    | H: (?C _) = (?C _) |- _ => inversion H
    | H: (?C _ _) = (?C _ _) |- _ => inversion H
    | H: (?C _ _ _) = (?C _ _ _) |- _ => inversion H                                           
  end.

Ltac open_rec_t_tm_x_core j' v0' v' :=
  intros; 
  simpl in *;
  fequals*;
  simpl in *;
  try inversion_on_matching_terms;
  try solve[fequals*];
  try apply open_rec_t_tm_v_core with (j:= j') (v:= v0'); try assumption;
  apply open_rec_t_core with (j:= j') (v:= v'); try assumption.
  
(* BUG why can't I put this into the induction without j being bound? *)

(* 
Definition Q :=
             (fun t : St => 
              forall i j u v,
                i <> j ->
                (open_rec_t_tm_st j v t) =
                (open_rec_t_tm_st i u (open_rec_t_tm_st j v t)) ->
                t = (open_rec_t_tm_st i u t)).

Lemma open_rec_t_tm_st_core':
  forall t i j u v,
    i <> j ->
    (open_rec_t_tm_st j v t) = (open_rec_t_tm_st i u (open_rec_t_tm_st j v t)) ->
    t = (open_rec_t_tm_st i u t).
Proof.
  apply (St_ind_mutual 
             (fun t : St => 
              forall i j u v,
                i <> j ->
                (open_rec_t_tm_st j v t) =
                (open_rec_t_tm_st i u (open_rec_t_tm_st j v t)) ->
                t = (open_rec_t_tm_st i u t))
           (fun t : E  => 
              forall i j u v,
                i <> j ->
                (open_rec_t_tm_e j v t) =
                (open_rec_t_tm_e i u (open_rec_t_tm_e j v t)) ->
                t = (open_rec_t_tm_e i u t))
           (fun t : F  => 
              forall i j u v,
                i <> j ->
                (open_rec_t_tm_f j v t) = 
                (open_rec_t_tm_f i u (open_rec_t_tm_f j v t)) ->
                t = (open_rec_t_tm_f i u t)));
  open_rec_t_tm_x_core j v0 v.
Qed.

*)

Lemma open_rec_t_tm_st_core:
  forall t i j u v,
    i <> j ->
    (open_rec_t_tm_st j v t) = (open_rec_t_tm_st i u (open_rec_t_tm_st j v t)) ->
    t = (open_rec_t_tm_st i u t).
Proof.
  apply (St_ind_mutual 
             (fun t : St => 
              forall i j u v,
                i <> j ->
                (open_rec_t_tm_st j v t) =
                (open_rec_t_tm_st i u (open_rec_t_tm_st j v t)) ->
                t = (open_rec_t_tm_st i u t))
           (fun t : E  => 
              forall i j u v,
                i <> j ->
                (open_rec_t_tm_e j v t) =
                (open_rec_t_tm_e i u (open_rec_t_tm_e j v t)) ->
                t = (open_rec_t_tm_e i u t))
           (fun t : F  => 
              forall i j u v,
                i <> j ->
                (open_rec_t_tm_f j v t) = 
                (open_rec_t_tm_f i u (open_rec_t_tm_f j v t)) ->
                t = (open_rec_t_tm_f i u t)));
  open_rec_t_tm_x_core j v0 v.
Qed.

Lemma open_rec_t_tm_e_core:
  forall t i j u v,
    i <> j ->
    (open_rec_t_tm_e j v t) = (open_rec_t_tm_e i u (open_rec_t_tm_e j v t)) ->
    t = (open_rec_t_tm_e i u t).
Proof.
  apply (E_ind_mutual 
           (fun t : St => 
              forall i j u v,
                i <> j ->
                (open_rec_t_tm_st j v t) = (open_rec_t_tm_st i u (open_rec_t_tm_st j v t)) ->
                t = (open_rec_t_tm_st i u t))
           (fun t : E  => 
              forall i j u v,
                i <> j ->
                (open_rec_t_tm_e j v t) = (open_rec_t_tm_e i u (open_rec_t_tm_e j v t)) ->
                t = (open_rec_t_tm_e i u t))
           (fun t : F  => 
              forall i j u v,
                i <> j ->
                (open_rec_t_tm_f j v t) = (open_rec_t_tm_f i u (open_rec_t_tm_f j v t)) ->
                t = (open_rec_t_tm_f i u t)));
  open_rec_t_tm_x_core j v0 v.
Qed.

Lemma open_rec_t_tm_f_core:
  forall t i j u v,
    i <> j ->
    (open_rec_t_tm_f j v t) = (open_rec_t_tm_f i u (open_rec_t_tm_f j v t)) ->
    t = (open_rec_t_tm_f i u t).
Proof.
  apply (F_ind_mutual 
           (fun t : St => 
              forall i j u v,
                i <> j ->
                (open_rec_t_tm_st j v t) = (open_rec_t_tm_st i u (open_rec_t_tm_st j v t)) ->
                t = (open_rec_t_tm_st i u t))
           (fun t : E  => 
              forall i j u v,
                i <> j ->
                (open_rec_t_tm_e j v t) = (open_rec_t_tm_e i u (open_rec_t_tm_e j v t)) ->
                t = (open_rec_t_tm_e i u t))
           (fun t : F  => 
              forall i j u v,
                i <> j ->
                (open_rec_t_tm_f j v t) = (open_rec_t_tm_f i u (open_rec_t_tm_f j v t)) ->
                t = (open_rec_t_tm_f i u t)));
  open_rec_t_tm_x_core j v0 v.
Qed.

Lemma open_rec_v_tm_core:
  forall t i j u v,
    i <> j ->
    (open_rec_t_tm j v t) = (open_rec_t_tm i u (open_rec_t_tm j v t)) ->
    t = (open_rec_t_tm i u t).
Proof.
  induction t; introv neq equ;
  simpl;
  fequals*;
  inversion equ.
  apply open_rec_t_tm_st_core with (j:= j) (v:= v); assumption.
  apply open_rec_t_tm_e_core with (j:= j) (v:= v); assumption.
  apply open_rec_t_tm_f_core with (j:= j) (v:= v); assumption.
Qed.

Lemma open_rec_v_tm_v_core:
  forall t i j  u v,
    i <> j ->
      (open_rec_v_tm_v j v t) = (open_rec_v_tm_v i u (open_rec_v_tm_v j v t)) ->
      t = (open_rec_v_tm_v i u t).
Proof.
  induction t; introv Neq Equ; inversion* Equ; simpls*.
  case_nat*.
  case_nat*.
Qed.

Lemma open_rec_v_tm_p_core:
  forall t i j  u v,
    i <> j ->
      (open_rec_v_tm_p j v t) = (open_rec_v_tm_p i u (open_rec_v_tm_p j v t)) ->
      t = (open_rec_v_tm_p i u t).
Proof.
  induction t; introv Neq Equ; inversion* Equ; simpls*.
  case_nat*.
  case_nat*.
Qed.

Ltac open_rec_v_tm_x_core j v0:=
  try solve[intros;
            simpl in *;
            inversion_on_matching_terms;
            fequals*;
            try apply open_rec_v_tm_v_core with (j:= j) (v:= v0); auto;
            try apply open_rec_v_tm_p_core with (j:= j) (v:= v0); auto].

Lemma open_rec_v_tm_st_core:
  forall t i j u v,
    i <> j ->
    (open_rec_v_tm_st j v t) = (open_rec_v_tm_st i u (open_rec_v_tm_st j v t)) ->
    t = (open_rec_v_tm_st i u t).
Proof.
  apply (St_ind_mutual 
           (fun t : St => 
              forall i j u v,
                i <> j ->
                (open_rec_v_tm_st j v t) = (open_rec_v_tm_st i u (open_rec_v_tm_st j v t)) ->
                t = (open_rec_v_tm_st i u t))
           (fun t : E  => 
              forall i j u v,
                i <> j ->
                (open_rec_v_tm_e j v t) = (open_rec_v_tm_e i u (open_rec_v_tm_e j v t)) ->
                t = (open_rec_v_tm_e i u t))
           (fun t : F  => 
              forall i j u v,
                i <> j ->
                (open_rec_v_tm_f j v t) = (open_rec_v_tm_f i u (open_rec_v_tm_f j v t)) ->
                t = (open_rec_v_tm_f i u t)));
  open_rec_v_tm_x_core j v0.
Qed.

Lemma open_rec_v_tm_e_core:
  forall t i j u v,
    i <> j ->
    (open_rec_v_tm_e j v t) = (open_rec_v_tm_e i u (open_rec_v_tm_e j v t)) ->
    t = (open_rec_v_tm_e i u t).
Proof.
  apply (E_ind_mutual 
           (fun t : St => 
              forall i j u v,
                i <> j ->
                (open_rec_v_tm_st j v t) = (open_rec_v_tm_st i u (open_rec_v_tm_st j v t)) ->
                t = (open_rec_v_tm_st i u t))
           (fun t : E  => 
              forall i j u v,
                i <> j ->
                (open_rec_v_tm_e j v t) = (open_rec_v_tm_e i u (open_rec_v_tm_e j v t)) ->
                t = (open_rec_v_tm_e i u t))
           (fun t : F  => 
              forall i j u v,
                i <> j ->
                (open_rec_v_tm_f j v t) = (open_rec_v_tm_f i u (open_rec_v_tm_f j v t)) ->
                t = (open_rec_v_tm_f i u t)));
  open_rec_v_tm_x_core j v0.
Qed.

Lemma open_rec_v_tm_f_core:
  forall t i j u v,
    i <> j ->
    (open_rec_v_tm_f j v t) = (open_rec_v_tm_f i u (open_rec_v_tm_f j v t)) ->
    t = (open_rec_v_tm_f i u t).
Proof.
  apply (F_ind_mutual 
           (fun t : St => 
              forall i j u v,
                i <> j ->
                (open_rec_v_tm_st j v t) = (open_rec_v_tm_st i u (open_rec_v_tm_st j v t)) ->
                t = (open_rec_v_tm_st i u t))
           (fun t : E  => 
              forall i j u v,
                i <> j ->
                (open_rec_v_tm_e j v t) = (open_rec_v_tm_e i u (open_rec_v_tm_e j v t)) ->
                t = (open_rec_v_tm_e i u t))
           (fun t : F  => 
              forall i j u v,
                i <> j ->
                (open_rec_v_tm_f j v t) = (open_rec_v_tm_f i u (open_rec_v_tm_f j v t)) ->
                t = (open_rec_v_tm_f i u t)));
  open_rec_v_tm_x_core j v0.
Qed.

(* Bug bindings of names of LibVar vs LibVarPath. *)
Lemma lc__open_rec_t_identity:
  forall t,
    lc_t t -> forall k u, t = (open_rec_t_tk u t).
Proof.
  introv lct.
  induction lct; try intros k u; simpl; auto; try solve[congruence];

  introv;
  fequals*;
  pick_fresh alpha;
  (* lets: (open_rec_t_core t0). Lets is failing here. Bummer. *)
  lets L: open_rec_t_core;
  specialize (L t0 (S k0) 0 u (ftvar alpha));
  auto.
Qed.

Ltac inversion_on_lc :=
  match goal with
    | H : lc_t_tm_st _ |- _ => inversions H
    | H : lc_t_tm_e  _ |- _ => inversions H
    | H : lc_t_tm_f  _ |- _ => inversions H                                        
  end.

Ltac lc_t_tm_x__open_rec_t_x_identity:=
  try solve[intros;
  inversion_on_lc;
  simpl;
  fequals*;
  try solve[apply* lc__open_rec_t_identity]].


Lemma lc_t_tm_st__open_rec_t_st_identity:
  forall t,
    lc_t_tm_st t -> forall k u, t = (open_rec_t_tm_st k u t).
Proof.
  apply (St_ind_mutual 
          (fun t : St => 
              lc_t_tm_st t -> forall k u, t = (open_rec_t_tm_st k u t))
           (fun t : E  => 
              lc_t_tm_e t -> forall k u, t = (open_rec_t_tm_e k u t))
           (fun t : F  => 
              lc_t_tm_f t -> forall k u, t = (open_rec_t_tm_f k u t)));
  lc_t_tm_x__open_rec_t_x_identity.
Qed.
        
Lemma lc_t_tm_e__open_rec_t_st_identity:
  forall t,
    lc_t_tm_e t -> forall k u, t = (open_rec_t_tm_e k u t).
  apply (E_ind_mutual 
           (fun t : St => 
              lc_t_tm_st t -> forall k u, t = (open_rec_t_tm_st k u t))
           (fun t : E  => 
              lc_t_tm_e t -> forall k u, t = (open_rec_t_tm_e k u t))
           (fun t : F  => 
              lc_t_tm_f t -> forall k u, t = (open_rec_t_tm_f k u t)));
  lc_t_tm_x__open_rec_t_x_identity.
Qed.

Lemma lc_t_tm_f__open_rec_t_st_identity:
  forall t,
    lc_t_tm_f t -> forall k u, t = (open_rec_t_tm_f k u t).
Proof.
  apply (F_ind_mutual 
           (fun t : St => 
              lc_t_tm_st t -> forall k u, t = (open_rec_t_tm_st k u t))
           (fun t : E  => 
              lc_t_tm_e t -> forall k u, t = (open_rec_t_tm_e k u t))
           (fun t : F  => 
              lc_t_tm_f t -> forall k u, t = (open_rec_t_tm_f k u t)));
  lc_t_tm_x__open_rec_t_x_identity.
Qed.

Lemma lc_t_tm__open_rec_t_identity:
  forall t,
    lc_t_tm t -> forall k u, t = (open_rec_t_tm k u t).
Proof.
  destruct t; intros; simpl; fequals*; inversion H.
  apply* lc_t_tm_st__open_rec_t_st_identity.
  apply* lc_t_tm_e__open_rec_t_st_identity.
  apply* lc_t_tm_f__open_rec_t_st_identity.
Qed.

(* Substitution identity given fresh variables. *)

Lemma subst_t_tv_t_fresh : forall x t u, 
  x \notin ftv_t t ->  t = (subst_t_tv_t u x t).
Proof.
  intros.
  induction t; simpls*;
  fequals*;
  case_var*.
Qed.

Lemma subst_t_tv_t_v_fresh : forall x t u, 
  x \notin ftv_tm_v t ->  t = (subst_t_tv_t_v u x t).
Proof.
  induction t; simpls*.
Qed.

Ltac subst_t_tv_t_x_fresh :=
  lets: subst_t_tv_t_v_fresh;
  lets: subst_t_tv_t_fresh;
  intros;
  simpls*;
  fequals*.

Lemma subst_t_tv_t_st_fresh : forall x u t, 
  x \notin ftv_tm_st t ->  t = (subst_t_tv_t_st u x t).
Proof.
  intros x u.
  apply (St_ind_mutual 
           (fun t : St => 
              x \notin ftv_tm_st t ->  t = (subst_t_tv_t_st u x t))
           (fun t : E  => 
              x \notin ftv_tm_e t ->  t = (subst_t_tv_t_e u x t))
           (fun t : F  => 
              x \notin ftv_tm_f t ->  t = (subst_t_tv_t_f u x t)));
    subst_t_tv_t_x_fresh.
Qed.

Lemma subst_t_tv_t_e_fresh : forall x u t, 
  x \notin ftv_tm_e t ->  t = (subst_t_tv_t_e u x t).
Proof.
  intros x u.
  apply (E_ind_mutual 
           (fun t : St => 
              x \notin ftv_tm_st t ->  t = (subst_t_tv_t_st u x t))
           (fun t : E  => 
              x \notin ftv_tm_e t ->  t = (subst_t_tv_t_e u x t))
           (fun t : F  => 
              x \notin ftv_tm_f t ->  t = (subst_t_tv_t_f u x t)));
    subst_t_tv_t_x_fresh.
Qed.

Lemma subst_t_tv_t_f_fresh : forall x u t, 
  x \notin ftv_tm_f t ->  t = (subst_t_tv_t_f u x t).
Proof.
  intros x u.
  apply (F_ind_mutual 
           (fun t : St => 
              x \notin ftv_tm_st t ->  t = (subst_t_tv_t_st u x t))
           (fun t : E  => 
              x \notin ftv_tm_e t ->  t = (subst_t_tv_t_e u x t))
           (fun t : F  => 
              x \notin ftv_tm_f t ->  t = (subst_t_tv_t_f u x t)));
    subst_t_tv_t_x_fresh.
Qed.


Lemma subst_t_tv_t_tm_fresh : forall x u t, 
  x \notin ftv_tm t ->  t = (subst_t_tv_t_tm u x t).
Proof.
  destruct t; intros; simpl; fequals*.
  apply* subst_t_tv_t_st_fresh.
  apply* subst_t_tv_t_e_fresh.
  apply* subst_t_tv_t_f_fresh.
Qed.


(* Substitutions for term variables in terms is identity with a fresh variable. *)

Lemma subst_v_v_tm_v_fresh : forall x t u, 
  x \notin fv_tm_v t ->  t = (subst_v_v_tm_v u x t).
Proof.
  intros.
  induction t.
  all: simpls*. 
  case_var*.
Qed.

Ltac subst_v_v_tm_x_fresh :=
  lets: subst_v_v_tm_v_fresh;
  lets: subst_t_tv_t_fresh;
  intros;
  simpls*;
  fequals*.

Lemma subst_v_v_tm_st_fresh : forall x u t, 
  x \notin fv_tm_st t ->  t = (subst_v_v_tm_st u x t).
Proof.
  intros x u.
  apply (St_ind_mutual 
           (fun t : St => 
              x \notin fv_tm_st t ->  t = (subst_v_v_tm_st u x t))
           (fun t : E  => 
              x \notin fv_tm_e t ->  t = (subst_v_v_tm_e u x t))
           (fun t : F  => 
              x \notin fv_tm_f t ->  t = (subst_v_v_tm_f u x t)));
    subst_v_v_tm_x_fresh.
Qed.

Lemma subst_v_v_tm_e_fresh : forall x u t, 
  x \notin fv_tm_e t ->  t = (subst_v_v_tm_e u x t).
Proof.
  intros x u.
  apply (E_ind_mutual 
           (fun t : St => 
              x \notin fv_tm_st t ->  t = (subst_v_v_tm_st u x t))
           (fun t : E  => 
              x \notin fv_tm_e t ->  t = (subst_v_v_tm_e u x t))
           (fun t : F  => 
              x \notin fv_tm_f t ->  t = (subst_v_v_tm_f u x t)));
    subst_v_v_tm_x_fresh.
Qed.

Lemma subst_v_v_tm_f_fresh : forall x u t, 
  x \notin fv_tm_f t ->  t = (subst_v_v_tm_f u x t).
Proof.
  intros x u.
  apply (F_ind_mutual 
           (fun t : St => 
              x \notin fv_tm_st t ->  t = (subst_v_v_tm_st u x t))
           (fun t : E  => 
              x \notin fv_tm_e t ->  t = (subst_v_v_tm_e u x t))
           (fun t : F  => 
              x \notin fv_tm_f t ->  t = (subst_v_v_tm_f u x t)));
    subst_v_v_tm_x_fresh.
Qed.

Lemma subst_v_v_tm_fresh : forall x u t, 
  x \notin fv_tm t ->  t = (subst_v_v_tm u x t).
Proof.
  destruct t; intros; simpl; fequals*.
  apply* subst_v_v_tm_st_fresh.
  apply* subst_v_v_tm_e_fresh.
  apply* subst_v_v_tm_f_fresh.
Qed.

(* Substitution distributes on the open operation. *)

(* For types for type variable substitution. *)

Lemma subst_open_t :
  forall x u t1 t2, 
    lc_t u -> 
    (subst_t_tv_t u x (open_t t2 t1)) =
    (open_t (subst_t_tv_t u x t2) (subst_t_tv_t u x t1)).
Proof.
  intros.
  unfold open_t.
  generalize 0.
  induction t1; try solve[intros; simpl; fequals*].
  intros; simpl; case_nat*.
  intros. 
  simpl.
  case_var*.
  apply* lc__open_rec_t_identity.
Qed.

(* For types for type variables in terms. *)
(* This does not make sense because we can not substitute terms into term binders 
generally in Cyclone.

 This is due to the inability to generally substitute a term for a variable
 in p_e x p expressions. 

 Will it make problems in the proofs? Perhaps.

Lemma subst_open_t_tm_st:
  forall u alpha s1 s2,
    lc_t u -> 
    (subst_t_tv_t_st u alpha (open_rec_t_tm_st 0 s2 s1)) = 
    (open_rec_t_tm_st 0 (subst_t_tv_t_st u alpha s2) (subst_t_tv_t_st u alpha s1)).


 And neither does this make sense:

Lemma subst_open_t_tm_st:
  forall x y s1 s2,
    lc_t_tm_st (e_s (v_e y)) -> 
    (subst_v_v_tm_st x y (open_rec_v_tm_st 0 s2 s1)) = 
    (open_rec_v_tm_st 0 (subst_v_v_tm_st x y s2) (subst_v_v_tm_st x y s1)).

 But both of these might work on variable for varible substition?

*)

(** Substitution and open_var for distinct names commute. *)

Lemma subst_open_tvar:
  forall (alpha beta : var) t e,
    alpha <> beta ->
    lc_t t ->
    forall n, 
    (open_rec_t_tn (ftvar beta)  (subst_t_tv_t t  alpha e)) =
    (subst_t_tv_t t    alpha         (open_rec_t_t n (ftvar beta) e)).
Proof.
  introv Neq lctaut.
  induction e; intros; 
  lets L: (lc__open_rec_t_identity lctaut);
  simpls*; fequals*; simpls*.
  case_nat*.
  simpl.
  case_var*.
  case_var*.
Qed.

Lemma subst_open_tvar_term:
  forall (alpha beta : var) t e,
    alpha <> beta ->
    lc_t t ->
    forall n, 
    (open_rec_t_tm n (ftvar beta)  (subst_t_tv_t_tm t  alpha e)) =
    (subst_t_tv_t_tm    t    alpha      (open_rec_t_tm n (ftvar beta) e)).
Proof.
  introv Neq lctaut.
  induction e; intros.
  lets L: (lc_t_tm__open_rec_t_identity lctaut).
  simpls*; fequals*; simpls*.
  case_nat*.
  simpl.
  case_var*.
  case_var*.
Qed.


Lemma subst_open_evar:
  forall (x y : var) t e,
    x <> y ->
    lc_term t ->
    forall n, 
    (open_rec_t_t n (fvar y)  (subst_t_tv_t t  x e)) =
    (subst_t_tv_t t          x   (open_rec_t_t n (fevar y) e)).
Proof.
  introv Neq lctaut.
  induction e; intros; 
  lets L: (lc__open_rec_t_identity lctaut);
  simpls*; fequals*; simpls*.
  case_nat*.
  simpl.
  case_var*.
  case_var*.
Qed.

(** Opening up an abstraction of body t with a term u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma subst_intro_tau :
  forall alpha t u, 
    alpha \notin (ftv_t t) ->
    lc_t u ->
    (open_rec_t_t 0 t u) = (subst_t_tv_t u alpha (open_rec_t_t 0 t (ftvar alpha))).
Proof.
  introv Fr lctauu.
  induction t; intros; simpls*; case_var*; fequals*; simpls*;
  lets L : (lc__open_rec_t_identity lctauu 0);
  symmetry;
  auto.
Qed.  


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

Lemma open_tm : forall t u,
  body t -> term u -> term (t ^^ u).
Proof.
  intros. destruct H. pick_fresh y. rewrite* (@subst_intro y).
Qed.

Hint Resolve open_tm.


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
