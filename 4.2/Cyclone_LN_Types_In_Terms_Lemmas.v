(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION".   Daniel Grossman, August 2003 *)
(* Lemmas from the Lambda JAR paper. *)
(* Brian Milnes 2016 *)

Set Implicit Arguments.
Require Export Cyclone_LN_Tactics Cyclone_LN_Types Cyclone_LN_Terms Cyclone_LN_Types_In_Terms Cyclone_LN_Types_Lemmas.
Open Scope cyclone_scope.
Open Scope nat_scope.
Import TTM.


(* This is the version just for the lemmas manipulating types in terms. *)
Module TTMP. (* TM = Term P = Proof. *)

(* ====================================================================== *)
(** ** Proofs *)

(* ********************************************************************** *)
(** Variable closing and variable opening are reciprocal of one another *)

(** Showing that [close_var] after [open_var] is the identity is easy *)

Print fv_v.

Lemma close_v_open_v :
  forall t alpha n,
  alpha \notin fv_v t -> 
  close_rec_v n alpha (open_rec_v n (ftvar alpha) t) = t.
Proof.
  introv.
  induction t; simpl; introv Fr; fequals~.
Qed.

(* The application of a mutually defined induction principle in Coq is
 quite verbose. You must make N predicates for N way mutually recursively
 defined inductive types and then apply them. Each of the N must have
 it's own Lemma. To shorten this, I define functions and an Ltac to
 prevent the repeating of any text that I can. *)

Function close_st_open_st_pred (t : St) :=
  forall alpha n, 
    alpha \notin fv_st t ->
    close_rec_st n alpha (open_rec_st n (ftvar alpha) t) = t.
Hint Unfold close_st_open_st_pred.

Function close_e_open_e_pred (t : E) :=
  forall alpha n, 
    alpha \notin fv_e t ->
    close_rec_e n alpha (open_rec_e n (ftvar alpha) t) = t.
Hint Unfold close_e_open_e_pred.

Function close_f_open_f_pred (t : F) :=
  forall alpha n, 
    alpha \notin fv_f t ->
    close_rec_f n alpha (open_rec_f n (ftvar alpha) t) = t.
Hint Unfold close_f_open_f_pred.

Ltac close_X_open_X_proof :=
  autounfold in *;
  simpl;
  intros;
  fequals~;
  applys* close_v_open_v.

Ltac close_X_open_X_induction M :=
  apply(M
          close_st_open_st_pred
          close_e_open_e_pred
          close_f_open_f_pred).

Lemma close_st_open_st :
  forall t alpha n, 
    alpha \notin fv_st t ->
    close_rec_st n alpha (open_rec_st n (ftvar alpha) t) = t.
Proof.
  (* BUG, I think I really need a simultaneous induction method on types and terms. *)
  close_X_open_X_induction St_ind_mutual;
  autounfold in *;
  simpl;
  intros;
  fequals~;
  try applys* close_v_open_v.

  Focus 5.


  generalize n.
  induction t; try solve[intros; simpl; fequals~; simpl in H0; auto].

  Focus 3.
  simpl.
  fequals~.
  simpl in H0; auto.


  simpl.
  case_nat~.
  admit.

  admit.
  auto.

  assert(alpha \notin fv_e e); auto.
  assert(alpha \notin T.fv t); auto.
  apply H with (n:= n) in H1.



  lets M: TP.close_open.
  specialize (M alpha t H2).
  


  close_X_open_X_proof.
Qed.

Lemma close_e_open_e :
  forall t, close_e_open_e_pred t.
Proof.
  close_X_open_X_induction E_ind_mutual;
  close_X_open_X_proof.
Qed.

Lemma close_f_open_f :
  forall t, close_f_open_f_pred t.
Proof.
  close_X_open_X_induction F_ind_mutual;
  close_X_open_X_proof.
Qed.

Lemma close_open :
  forall x t n, 
  x \notin fv_tm t -> 
  close_rec n x (open_rec n x t) = t.
Proof.
  destruct t; simpl; intros; fequals~.
  applys~ close_st_open_st.
  applys~ close_e_open_e.
  applys~ close_f_open_f.
Qed.

(** The other direction is much harder; First, we first need
    to establish the injectivity of [open_var] *)

Lemma open_rec_st_inj :
  forall x n t1 t2, 
    x \notin (fv_tm_st t1) ->
    x \notin (fv_tm_st t2) -> 
    open_rec_st n x t1 = open_rec_st n x t2 ->
    (t1 = t2).
Proof.
  introv Fr1 Fr2 Eq.
  rewrite~ <- (@close_st_open_st t1 x n).
  rewrite~ <- (@close_st_open_st t2 x n).
  fequals~.
Qed.

Lemma open_rec_e_inj :
  forall x n t1 t2, 
    x \notin (fv_tm_e t1) ->
    x \notin (fv_tm_e t2) -> 
    open_rec_e n x t1 = open_rec_e n x t2 ->
    (t1 = t2).
Proof.
  introv Fr1 Fr2 Eq.
  rewrite~ <- (@close_e_open_e t1 x n).
  rewrite~ <- (@close_e_open_e t2 x n).
  fequals~.
Qed.

Lemma open_rec_f_inj :
  forall x n t1 t2, 
    x \notin (fv_tm_f t1) ->
    x \notin (fv_tm_f t2) -> 
    open_rec_f n x t1 = open_rec_f n x t2 ->
    (t1 = t2).
Proof.
  introv Fr1 Fr2 Eq.
  rewrite~ <- (@close_f_open_f t1 x n).
  rewrite~ <- (@close_f_open_f t2 x n).
  fequals~.
Qed.

Lemma open_rec_inj :
  forall x n t1 t2, 
    x \notin (fv_tm t1) ->
    x \notin (fv_tm t2) -> 
    open_rec n x t1 = open_rec n x t2 ->
    (t1 = t2).
Proof.
  introv Fr1 Fr2 Eq.
  rewrite~ <- (@close_open x t1 n).
  rewrite~ <- (@close_open x t2 n).
  fequals~.
Qed.

(** We also need one (tricky) auxiliary lemma to handle the binder case *)

Lemma open_rec_v_close_rec_v_on_open_rec_v:
  forall x y z t i j,
    i <> j ->
    y <> x ->
    y \notin (fv_tm_v t) ->
    open_rec_v i y (open_rec_v j z (close_rec_v j x t))
  = open_rec_v j z (close_rec_v j x (open_rec_v i y t)).
Proof.
  induction t; try solve[simpl; intros; try solve [ fequals~ ]];
  intros;
  do 4 (simpl; try case_nat~; try case_nat~; try case_var~).
Qed.

Function open_rec_e_close_rec_e_on_open_rec_e_pred (t : E) :=
  forall x y z i j,
    i <> j ->
    y <> x ->
    y \notin (fv_tm_e t) ->
    open_rec_e i y (open_rec_e j z (close_rec_e j x t))
  = open_rec_e j z (close_rec_e j x (open_rec_e i y t)).
Hint Unfold open_rec_e_close_rec_e_on_open_rec_e_pred.

Function open_rec_st_close_rec_st_on_open_rec_st_pred (t : St) :=
  forall x y z i j,
    i <> j ->
    y <> x ->
    y \notin (fv_tm_st t) ->
    open_rec_st i y (open_rec_st j z (close_rec_st j x t))
  = open_rec_st j z (close_rec_st j x (open_rec_st i y t)).
Hint Unfold open_rec_st_close_rec_st_on_open_rec_st_pred.

Function open_rec_f_close_rec_f_on_open_rec_f_pred (t : F) :=
  forall x y z i j,
    i <> j ->
    y <> x ->
    y \notin (fv_tm_f t) ->
    open_rec_f i y (open_rec_f j z (close_rec_f j x t))
  = open_rec_f j z (close_rec_f j x (open_rec_f i y t)).
Hint Unfold open_rec_f_close_rec_f_on_open_rec_f_pred.

Ltac open_rec_X_close_rec_X_on_open_rec_X_induction MIS :=
  apply (MIS
           open_rec_st_close_rec_st_on_open_rec_st_pred
           open_rec_e_close_rec_e_on_open_rec_e_pred
           open_rec_f_close_rec_f_on_open_rec_f_pred).
  
Ltac open_rec_X_close_rec_X_on_open_rec_X_proof :=
  autounfold in *;
  try solve[simpl; intros; try solve [ fequals~ ]];
  intros;
  do 4 (simpl; try case_nat~; try case_nat~; try case_var~);
  do 2 (fequals~; apply~ open_rec_v_close_rec_v_on_open_rec_v).

Lemma open_rec_st_close_rec_st_on_open_rec_st:
  forall t, open_rec_st_close_rec_st_on_open_rec_st_pred t.
Proof.
  open_rec_X_close_rec_X_on_open_rec_X_induction St_ind_mutual;
  open_rec_X_close_rec_X_on_open_rec_X_proof.
Qed.

Lemma open_rec_e_close_rec_e_on_open_rec_e:
  forall t, open_rec_e_close_rec_e_on_open_rec_e_pred t.
Proof.
  open_rec_X_close_rec_X_on_open_rec_X_induction E_ind_mutual;
  open_rec_X_close_rec_X_on_open_rec_X_proof.
Qed.

Lemma open_rec_f_close_rec_f_on_open_rec_f:
  forall t, open_rec_f_close_rec_f_on_open_rec_f_pred t.
Proof.
  open_rec_X_close_rec_X_on_open_rec_X_induction F_ind_mutual;
  open_rec_X_close_rec_X_on_open_rec_X_proof.
Qed.

Lemma open_rec_close_rec_on_open_rec:
  forall x y z t i j,
    i <> j ->
    y <> x ->
    y \notin (fv_tm t) ->
    open_rec i y (open_rec j z (close_rec j x t))
  = open_rec j z (close_rec j x (open_rec i y t)).
Proof.
  destruct t; simpl; intros; fequals~.
  applys~ open_rec_st_close_rec_st_on_open_rec_st.
  applys~ open_rec_e_close_rec_e_on_open_rec_e.
  applys~ open_rec_f_close_rec_f_on_open_rec_f.
Qed.

(** Now we can prove that [open_var] after [close_var] is the identity *)

Lemma open_rec_v_close_rec_v: 
  forall x t n, 
    lc_v t -> 
    open_rec_v n x (close_rec_v n x t)  = t.
Proof.
  introv T. 
  induction T. 
  intros; simpl; case_var~; simpl; case_nat~.
Qed.

Function open_rec_st_close_rec_st_pred (t : St) (_ : lc_st t):=
  forall x, 
  forall n,
    open_rec_st n x (close_rec_st n x t)  = t.
Hint Unfold open_rec_st_close_rec_st_pred.

Function open_rec_e_close_rec_e_pred (t : E) (_ : lc_e t):=
  forall x n, 
    open_rec_e n x (close_rec_e n x t)  = t.
Hint Unfold open_rec_e_close_rec_e_pred.

Function open_rec_f_close_rec_f_pred (t : F) (_ : lc_f t) :=
  forall x n, 
    open_rec_f n x (close_rec_f n x t)  = t.
Hint Unfold open_rec_f_close_rec_f_pred.

Ltac open_rec_X_close_rec_X_induction MIS :=
  apply (MIS 
           open_rec_st_close_rec_st_pred
           open_rec_e_close_rec_e_pred
           open_rec_f_close_rec_f_pred).

Ltac open_rec_X_close_rec_X_proof y M := 
  autounfold in *;
  intros; simpl; fequals~;
  lets: open_rec_v_close_rec_v;
  try solve[case_var~; simpl; case_nat~];
  try solve[ 
        match goal with
            |- ?t = _ => pick_fresh y from (fv_tm_st t)
        end;
        apply open_rec_st_inj with (x:= y) (n:= 0); auto;
        lets M: open_rec_st_close_rec_st_on_open_rec_st;
        unfold  open_rec_st_close_rec_st_on_open_rec_st_pred in M;
        rewrite~ M].


Lemma open_rec_st_close_rec_st: 
  forall t,
     lc_st t ->
     forall x, 
       forall n,
         open_rec_st n x (close_rec_st n x t)  = t.
Proof.
  open_rec_X_close_rec_X_induction lc_st_ind_mutual;
  open_rec_X_close_rec_X_proof y M.
Qed.

Lemma open_rec_e_close_rec_e: 
  forall t,
     lc_e t ->
     forall x, 
       forall n,
         open_rec_e n x (close_rec_e n x t)  = t.
Proof.
  open_rec_X_close_rec_X_induction lc_e_ind_mutual;
  open_rec_X_close_rec_X_proof y M.
Qed.

Lemma open_rec_f_close_rec_f: 
  forall t,
     lc_f t ->
     forall x, 
       forall n,
         open_rec_f n x (close_rec_f n x t)  = t.
Proof.
  open_rec_X_close_rec_X_induction lc_f_ind_mutual;
  open_rec_X_close_rec_X_proof y M.
Qed.

Lemma open_rec_close_rec: 
  forall t,
     lc_tm t ->
     forall x, 
       forall n,
         open_rec n x (close_rec n x t)  = t.
Proof.
  destruct t; intros; simpl; fequals~; inversions H.
  apply~ open_rec_st_close_rec_st.
  apply~ open_rec_e_close_rec_e.
  apply~ open_rec_f_close_rec_f.  
Qed.

(** As a bonus, we get the injectivity of [close_var] *)

Lemma close_on_var_inj :
  forall x t1 t2, 
    lc_tm t1 ->
    lc_tm t2 ->
    close x t1 = close x t2 ->
    (t1 = t2).
Proof.
  unfold close.
  introv T1 T2 Eq.
  rewrite~ <- (@open_rec_close_rec t1 T1 x 0).
  rewrite~ <- (@open_rec_close_rec t2 T2 x 0).
  fequals~.
Qed.

(* ********************************************************************** *)
(** Properties of [body] *)

(** An abstraction is locally closed iff it satifies the predicate [body] *) 

(* BUG: it's ugly! and it won't ltac. *)

Lemma lc_dfun_iff_body : 
  forall t0 t1 s,
    lc_f (dfun t0 t1 s) <-> body_tm (term_st s).
Proof. 
  intros.
  unfold body_tm, open_t_tm.
  simpl.
  iff H.
  inversion* H.

  inverts H.
  pick_fresh y.
  apply lc_dfun with (L':= x).
  assert (y \notin x).
  auto.
  intros.
  specialize (H0 x0 H1).
  inversions~ H0.
Qed.

(* Difference in the work, body requires something about e that
  is missing. *)

Lemma lc_open_iff_body : 
  forall e s,
    lc_e e ->
    lc_st (open e s) <-> body_tm (term_st s).
Proof. 
  introv lce.
  unfold body_tm, open_t_tm.
  simpl.
  iff H.
  inversions* H.

  inversion H.
  apply lc_open with (L':= x \u (fv_tm_st s)); auto.
  intros.
  specialize (H0 x0).
  assert(x0 \notin x).
  auto.
  apply H0 in H2.
  inversions~ H2.
Qed.


Lemma lc_openstar_iff_body : 
  forall e s,
    lc_e e ->
    lc_st (openstar e s) <-> body_tm (term_st s).
Proof. 
  introv lce.
  unfold body_tm, open_t_tm.
  simpl.
  iff H.
  inversions* H.

  inversion H.
  apply lc_openstar with (L':= x \u (fv_tm_st s)); auto.
  intros.
  specialize (H0 x0).
  assert(x0 \notin x).
  auto.
  apply H0 in H2.
  inversions~ H2.
Qed.

Lemma lc_letx_iff_body : 
  forall e s,
    lc_e e ->
    lc_st (letx e s) <-> body_tm (term_st s).
Proof. 
  introv lce.
  unfold body_tm, open_t_tm.
  simpl.
  iff H.
  inversions* H.

  inversion H.
  apply lc_st_letx with (L':= x \u (fv_tm_st s)); auto.
  intros.
  specialize (H0 x0).
  assert(x0 \notin x).
  auto.
  apply H0 in H2.
  inversions~ H2.
Qed.

(* ********************************************************************** *)
(** Interaction of [fv] with [open_var] and [close_var] *)

(** Opening with [u] adds [fv u] to the set of free variables *)

Lemma fv_tm_v_open :
  forall (t : V) (u : var) (n: nat),
    fv_tm_v (open_rec_v n u t) \c  fv_tm_v t \u \{u}.
Proof.
  intros.
  destruct t; simpl; try case_nat; simpl; fset.
Qed.

Function fv_tm_st_open_pred (t : St) :=
  forall (u : var) (n : nat),
    fv_tm_st (open_rec_st n u t) \c fv_tm_st t \u \{u}.
Hint Unfold fv_tm_st_open_pred.

Function fv_tm_e_open_pred (t : E) :=
  forall (u : var) (n : nat),
    fv_tm_e (open_rec_e n u t) \c fv_tm_e t \u \{u}.
Hint Unfold fv_tm_e_open_pred.

Function fv_tm_f_open_pred (t : F) :=
  forall (u : var) (n : nat),
    fv_tm_f (open_rec_f n u t) \c fv_tm_f t \u \{u}.
Hint Unfold fv_tm_f_open_pred.

Ltac fv_tm_X_open_proof :=
  autounfold in *;
  intros l; simpl; try case_nat; try fset;
  intros;
  applys~ fv_tm_v_open.

Ltac fv_tm_X_open_induction T :=
  apply (T
           fv_tm_st_open_pred
           fv_tm_e_open_pred
           fv_tm_f_open_pred).
  
Lemma fv_tm_st_open:
  forall t u n,
    fv_tm_st (open_rec_st n u t) \c fv_tm_st t \u \{u}.
Proof.
  fv_tm_X_open_induction St_ind_mutual;
  fv_tm_X_open_proof.
Qed.

Lemma fv_tm_e_open :
  forall t u n, 
    fv_tm_e (open_rec_e n u t) \c fv_tm_e t \u \{u}.
Proof.
  fv_tm_X_open_induction E_ind_mutual;
  fv_tm_X_open_proof.
Qed.

Lemma fv_tm_f_open :
  forall t u n, 
    fv_tm_f (open_rec_f n u t) \c fv_tm_f t \u \{u}.
Proof.
  fv_tm_X_open_induction F_ind_mutual;
  fv_tm_X_open_proof.
Qed.

Lemma fv_tm_open : forall t u,
  fv_tm (open u t) \c fv_tm t \u \{u}.
Proof.
  destruct t; intros.
  apply fv_tm_st_open.
  apply fv_tm_e_open.
  apply fv_tm_f_open.
Qed.

(** In particular, opening with variable [x] adds [x] to the set 
    of free variables *)

Lemma open_var_fv : forall x t,
  fv_tm (open_rec 0 x t) \c (fv_tm t \u \{x}).
Proof.
  intros.
  apply fv_tm_open. 
Qed.

(** Closing w.r.t variable [x] removes [x] from the set of free variables *)

Lemma close_tv_v_fv : forall x t n,
  fv_tm_v (close_rec_v n x t) \c (fv_tm_v t \- \{x}).
Proof.
  intros.
  destruct t; simpl; fset.
  case_var~; simpl; fset.
Qed.

Function close_tv_st_fv_pred (t : St) :=
  forall x n,
    fv_tm_st (close_rec_st n x t) \c (fv_tm_st t \- \{x}).
Hint Unfold close_tv_st_fv_pred.

Function close_tv_e_fv_pred (t : E) :=
  forall x n,
    fv_tm_e (close_rec_e n x t) \c (fv_tm_e t \- \{x}).
Hint Unfold close_tv_e_fv_pred.

Function close_tv_f_fv_pred (t : F) :=
  forall x n,
    fv_tm_f (close_rec_f n x t) \c (fv_tm_f t \- \{x}).
Hint Unfold close_tv_f_fv_pred.

Ltac close_tv_X_fv_induction T :=
  apply (T
           close_tv_st_fv_pred
           close_tv_e_fv_pred
           close_tv_f_fv_pred).

Ltac close_tv_X_fv_proof :=
  lets: close_tv_v_fv;
  autounfold in *; simpl; intros; fset.

Lemma close_tv_st_fv :
  forall t x n,
    fv_tm_st (close_rec_st n x t) \c (fv_tm_st t \- \{x}).
Proof.
  close_tv_X_fv_induction St_ind_mutual;
  close_tv_X_fv_proof.
Qed.

Lemma close_tv_e_fv :
  forall t x n,
    fv_tm_e (close_rec_e n x t) \c (fv_tm_e t \- \{x}).
Proof.
  close_tv_X_fv_induction E_ind_mutual;
  close_tv_X_fv_proof.
Qed.

Lemma close_tv_f_fv :
  forall t x n,
    fv_tm_f (close_rec_f n x t) \c (fv_tm_f t \- \{x}).
Proof.
  close_tv_X_fv_induction F_ind_mutual;
  close_tv_X_fv_proof.
Qed.

Lemma close_tv_fv : forall x t,
  fv_tm (close_rec 0 x t) \c (fv_tm t \- \{x}).
Proof.
  destruct t; intros.
  apply close_tv_st_fv.
  apply close_tv_e_fv.
  apply close_tv_f_fv.
Qed.

(* ********************************************************************** *)
(** Properties of substitution *)

(** Distributivity of [subst] on [open].
    Two (tricky) intermediate lemmas are required *)

Lemma open_rec_v_lc_ind : 
  forall t j v i u,
    i <> j ->
    open_rec_v i u (open_rec_v j v t) = open_rec_v j v t ->
    open_rec_v i u t = t.
Proof.
  induction t; introv Nq Eq;
  simpls; inversions~ Eq; fequals*.
  case_nat~. case_nat~.
Qed.

Function open_rec_st_lc_ind_pred (t : St) :=
  forall j v i u,
    i <> j ->
    open_rec_st i u (open_rec_st j v t) = open_rec_st j v t ->
    open_rec_st i u t = t.
Hint Unfold open_rec_st_lc_ind_pred.

Function open_rec_e_lc_ind_pred (t : E) :=
  forall j v i u,
    i <> j ->
    open_rec_e i u (open_rec_e j v t) = open_rec_e j v t ->
    open_rec_e i u t = t.
Hint Unfold open_rec_e_lc_ind_pred.

Function open_rec_f_lc_ind_pred (t : F) :=
  forall j v i u,
    i <> j ->
    open_rec_f i u (open_rec_f j v t) = open_rec_f j v t ->
    open_rec_f i u t = t.
Hint Unfold open_rec_f_lc_ind_pred.

Ltac open_rec_f_lc_ind_induction T :=  
  apply (T 
           open_rec_st_lc_ind_pred
           open_rec_e_lc_ind_pred
           open_rec_f_lc_ind_pred).

Ltac open_rec_f_lc_ind_proof :=
  autounfold in *;
  lets: open_rec_v_lc_ind;
  intros;
  simpls;
  try inversion_on_equated_constructors;
  fequals;
  intuition eauto.

Lemma open_rec_st_lc_ind : 
  forall t j v i u,
    i <> j ->
    open_rec_st i u (open_rec_st j v t) = open_rec_st j v t ->
    open_rec_st i u t = t.
Proof.
  open_rec_f_lc_ind_induction St_ind_mutual;
  open_rec_f_lc_ind_proof.
Qed.

Lemma open_rec_e_lc_ind : 
  forall t j v i u,
    i <> j ->
    open_rec_e i u (open_rec_e j v t) = open_rec_e j v t ->
    open_rec_e i u t = t.
Proof.
  open_rec_f_lc_ind_induction E_ind_mutual;
  open_rec_f_lc_ind_proof.
Qed.

Lemma open_rec_f_lc_ind : 
  forall t j v i u,
    i <> j ->
    open_rec_f i u (open_rec_f j v t) = open_rec_f j v t ->
    open_rec_f i u t = t.
Proof.
  open_rec_f_lc_ind_induction F_ind_mutual;
  open_rec_f_lc_ind_proof.
Qed.

Lemma open_rec_lc_ind : 
  forall t j v i u,
    i <> j ->
    open_rec i u (open_rec j v t) = open_rec j v t ->
    open_rec i u t = t.
Proof.
  intros.
  lets: open_rec_st_lc_ind.
  lets: open_rec_e_lc_ind.
  lets: open_rec_f_lc_ind.  
  destruct t; simpls; fequals~;
  inversion_on_equated_constructors;
  intuition eauto.
Qed.

Lemma open_rec_v_lc_t : forall u t k,
  lc_v t -> open_rec_v k u t = t.
Proof.
  destruct t; intros; simpls~.
  inversion H.
Qed.

Function open_rec_st_lc_t_st_pred (t : St) (_ : lc_st t) :=
  forall u, forall n, open_rec_st n u t = t.
Hint Unfold open_rec_st_lc_t_st_pred.

Function open_rec_e_lc_t_e_pred (t : E) (_ : lc_e t) :=
  forall u, forall n, open_rec_e n u t = t.
Hint Unfold open_rec_e_lc_t_e_pred.

Function open_rec_f_lc_t_f_pred (t : F) (_ : lc_f t):=
  forall u, forall n, open_rec_f n u t = t.
Hint Unfold open_rec_f_lc_t_f_pred.

Ltac open_rec_X_lc_t_X_induction T :=
  apply (T
           open_rec_st_lc_t_st_pred
           open_rec_e_lc_t_e_pred
           open_rec_f_lc_t_f_pred).

Ltac open_rec_X_lc_t_X_proof x :=
  autounfold in *;
  intros; simpl; fequals~;
  pick_fresh x;
  match goal with
   |- { S _ ttm_st> _} ?s = ?s =>
             apply~ (@open_rec_st_lc_ind s 0 x)
  end.

Lemma open_rec_st_lc_t : 
  forall t, 
    lc_st t -> 
    forall u,
     forall n,
       open_rec_st n u t = t.
Proof.
  open_rec_X_lc_t_X_induction lc_st_ind_mutual;
  open_rec_X_lc_t_X_proof x.
Qed.

Lemma open_rec_e_lc_t : 
  forall t, 
    lc_e t -> 
    forall u,
     forall n,
       open_rec_e n u t = t.
Proof.
  open_rec_X_lc_t_X_induction lc_e_ind_mutual;
  open_rec_X_lc_t_X_proof x.
Qed.

Lemma open_rec_f_lc_t : 
  forall t, 
    lc_f t -> 
    forall u,
     forall n,
       open_rec_f n u t = t.
Proof.
  open_rec_X_lc_t_X_induction lc_f_ind_mutual;
  open_rec_X_lc_t_X_proof x.
Qed.

Lemma open_rec_lc_t : 
  forall t, 
    lc_tm t -> 
    forall u,
     forall n,
       open_rec n u t = t.
Proof.
  lets L1: open_rec_st_lc_t.
  lets L2: open_rec_e_lc_t.  
  lets L3: open_rec_f_lc_t.  
  destruct t; intros; simpl; fequals~; inversions~ H.
Qed.

(* Bug: do these make sense? No. 

Lemma subst_v_open_rec_t_t:
  forall x y t v z,
    lc_v (fevar y) -> 
    subst_v x y (open t v) = 
    open (subst_v x y (term_e (v_e (fevar t)))) (subst_v x y v).  
Proof.
  intros. generalize 0.
  induction t; intros; simpl; fequals~.
  case_nat~.
  case_var~. rewrite~ open_rec_t_t_lc_t.
Qed.

(** In particular, we can distribute [subst] on [open_var] *)

Lemma subst_v_open_rec:
  forall x y u t, 
    x <> y ->
    lc_t u -> 
    subst_v u x (open_rec 0 (fevar y) t) =
    open_rec 0 (fevar y) (subst_v u x t).
Proof.
  introv N U.
  rewrite~ subst_v_open_rec_t_t.
  fequals.
  simpl.
  case_if~.
Qed.

*)

(** For the distributivity of [subst] on [close_var],
    one simple intermediate lemmas is required to 
    say that closing on a fresh name is the identity *)

Lemma close_rec_v_fresh :
  forall x t k,
  x \notin fv_tm_v t -> close_rec_v k x t = t.
Proof.
  destruct t; intros; simpls*.
  case_var~.
Qed.

Function close_rec_st_fresh_pred (t : St) :=
  forall x k,
    x \notin fv_tm_st t -> close_rec_st k x t = t.
Hint Unfold close_rec_st_fresh_pred.
  
Function close_rec_e_fresh_pred (t : E) :=
  forall x k,
    x \notin fv_tm_e t -> close_rec_e k x t = t.
Hint Unfold close_rec_e_fresh_pred.

Function close_rec_f_fresh_pred (t : F) :=
  forall x k,
    x \notin fv_tm_f t -> close_rec_f k x t = t.
Hint Unfold close_rec_f_fresh_pred.

Ltac close_rec_X_fresh_induction T :=
  apply (T
           close_rec_st_fresh_pred
           close_rec_e_fresh_pred
           close_rec_f_fresh_pred).

Ltac close_rec_X_fresh_proof :=
  lets: close_rec_v_fresh;
  autounfold in *;
  simpl;
  intros;
  fequals~.

Lemma close_rec_st_fresh :
  forall t x k,
    x \notin fv_tm_st t -> close_rec_st k x t = t.
Proof.
  close_rec_X_fresh_induction St_ind_mutual;
  close_rec_X_fresh_proof.
Qed.

Lemma close_rec_e_fresh :
  forall t x k,
    x \notin fv_tm_e t -> close_rec_e k x t = t.
Proof.
  close_rec_X_fresh_induction E_ind_mutual;
  close_rec_X_fresh_proof.
Qed.

Lemma close_rec_f_fresh :
  forall t x k,
    x \notin fv_tm_f t -> close_rec_f k x t = t.
Proof.
  close_rec_X_fresh_induction F_ind_mutual;
  close_rec_X_fresh_proof.
Qed.

Lemma close_rec_fresh :
  forall x t k,
    x \notin fv_tm t -> close_rec k x t = t.
Proof.
  lets: close_rec_st_fresh.
  lets: close_rec_e_fresh.
  lets: close_rec_f_fresh.
  destruct t; simpl; intros; fequals~.
Qed.

(** Distributivity of [subst] on [close_var] *)

Lemma subst_v_close_rec_v:
  forall t x y u,
    x <> y ->
    y \notin fv_tm_v (fevar u) -> 
    forall n, 
      subst_v_v u x (close_rec_v n y t) =
      close_rec_v n y (subst_v_v u x t).
Proof.
  destruct t; simpl; fequals~; intros;
  repeat (case_var~; simpl).
(* BUG *)
Admitted.

Function subst_v_close_rec_st_pred (t : St) :=
  forall x y u,
    x <> y ->
    y \notin fv_tm_v (fevar u) -> 
    forall n, 
      subst_v_st u x (close_rec_st n y t) =
      close_rec_st n y (subst_v_st u x t).
Hint Unfold subst_v_close_rec_st_pred.

Function subst_v_close_rec_e_pred (t : E) :=
  forall x y u,
    x <> y ->
    y \notin fv_tm_v (fevar u) -> 
    forall n,
      subst_v_e u x (close_rec_e n y t) =
      close_rec_e n y (subst_v_e u x t).
Hint Unfold subst_v_close_rec_e_pred.

Function subst_v_close_rec_f_pred (t : F) :=
  forall x y u,
    x <> y ->
    y \notin fv_tm_v (fevar u) -> 
    forall n, 
      subst_v_f u x (close_rec_f n y t) =
      close_rec_f n y (subst_v_f u x t).         
Hint Unfold subst_v_close_rec_f_pred.

Ltac subst_v_close_rec_X_induction T :=
  apply (T
           subst_v_close_rec_st_pred
           subst_v_close_rec_e_pred 
           subst_v_close_rec_f_pred).

Lemma subst_v_close_rec_st:
  forall t x y u,
    x <> y ->
    y \notin fv_tm_v (fevar u) -> 
    forall n,
      subst_v_st u x (close_rec_st n y t) =
      close_rec_st n y (subst_v_st u x t).
Proof.
  subst_v_close_rec_X_induction St_ind_mutual;
  lets J: subst_v_close_rec_v;
  autounfold in *;
  simpl;
  intros;
  fequals~.
Qed.

Lemma subst_v_close_rec_e:
  forall t x y u,
    x <> y ->
    y \notin fv_tm_v (fevar u) -> 
    forall n,
      subst_v_e u x (close_rec_e n y t) =
      close_rec_e n y (subst_v_e u x t).
Proof.
  subst_v_close_rec_X_induction E_ind_mutual;
  lets J: subst_v_close_rec_v;
  autounfold in *;
  simpl;
  intros;
  fequals~.
Qed.

Lemma subst_v_close_rec_f:
  forall t x y u,
    x <> y ->
    y \notin fv_tm_v (fevar u) -> 
    forall n,
      subst_v_f u x (close_rec_f n y t) =
      close_rec_f n y (subst_v_f u x t).
Proof.
  subst_v_close_rec_X_induction F_ind_mutual;
  lets J: subst_v_close_rec_v;
  autounfold in *;
  simpl;
  intros;
  fequals~.
Qed.

Lemma subst_v_close_rec:
  forall t x y u,
    x <> y ->
    y \notin fv_tm_v (fevar u) -> 
    forall n, 
      subst_v u x (close_rec n y t) = close_rec n y (subst_v u x t).
Proof.
  lets: subst_v_close_rec_st;
  lets: subst_v_close_rec_e;
  lets: subst_v_close_rec_f;
  destruct t; simpl; intros; fequals~.
Qed.

(** Substitution for a fresh name is the identity *)

Lemma subst_v_v_fresh : forall x t u, 
  x \notin fv_tm_v t -> subst_v_v u x t = t.
Proof.
  destruct t; simpl; intros; fequals~.
  case_var~.
Qed.

Function subst_v_st_fresh_pred (t : St) :=
  forall x u, 
    x \notin fv_tm_st t -> subst_v_st u x t = t.
Hint Unfold subst_v_st_fresh_pred.

Function subst_v_e_fresh_pred (t : E) :=
  forall x u, 
    x \notin fv_tm_e t -> subst_v_e u x t = t.
Hint Unfold subst_v_e_fresh_pred.

Function subst_v_f_fresh_pred (t : F) :=  
forall x u, 
  x \notin fv_tm_f t -> subst_v_f u x t = t.
Hint Unfold subst_v_f_fresh_pred.

Ltac subst_v_X_fresh_induction T :=
  apply(T 
          subst_v_st_fresh_pred
          subst_v_e_fresh_pred
          subst_v_f_fresh_pred).

Ltac subst_v_X_fresh_proof :=
  lets: subst_v_v_fresh;
  autounfold in *;
  simpl;
  intros;
  fequals~.

Lemma subst_v_st_fresh:
  forall t x u, 
  x \notin fv_tm_st t -> subst_v_st u x t = t.
Proof.
  subst_v_X_fresh_induction St_ind_mutual;
  subst_v_X_fresh_proof.
Qed.

Lemma subst_v_e_fresh: 
forall t x u, 
  x \notin fv_tm_e t -> subst_v_e u x t = t.
Proof.
  subst_v_X_fresh_induction E_ind_mutual;
  subst_v_X_fresh_proof.
Qed.

Lemma subst_v_f_fresh:
  forall t x u, 
  x \notin fv_tm_f t -> subst_v_f u x t = t.
Proof.
  subst_v_X_fresh_induction F_ind_mutual;
  subst_v_X_fresh_proof.
Qed.

Lemma subst_v_fresh : forall x t u, 
  x \notin fv_tm t -> subst_v u x t = t.
Proof.
  lets: subst_v_st_fresh.
  lets: subst_v_e_fresh.
  lets: subst_v_f_fresh.
  destruct t; simpl; intros; fequals~.
Qed.

(** Substitution can be introduced to decompose an opening *)

(*
Lemma subst_v_v_intro :
  forall t x u, 
    x \notin (fv_tm_v (fevar u)) ->
    lc_v (fevar u) ->
    open_rec_v 0 u t = subst_v_v u x (open_rec_v 0 x t).
Proof.
  destruc
*)

(* BUG FALSE~ *)
(*
Lemma subst_v_v_intro :
  forall t x, 
    x \notin (fv_tm_v t) ->
    forall n, 
      (open_rec_v n x t) = t.
SearchAbout ((open_rec_v _ _ _) = _).

Lemma subst_v_v_intro :
  forall t x u, 
    x \notin (fv_tm_v t) ->
    lc_v u ->
    forall n, 
      open_rec_v n u t = subst_v_v u x (open_rec_v n x t).
Proof.
  destruct t; simpl; intros.
  case_nat~.
  simpl.
  case_var~.
  (* stuck *)
  admit.
  case_var~.
Qed.

Lemma subst_v_intro :
  forall t x u, 
    x \notin (fv_tm_v (fevar u)) ->
    lc_v (fevar u) ->
    forall n,
      open_rec n u t = subst_v u x (open_rec n x t).
Proof.
  introv F U. 
  rewrite~ subst_v_open_rec.
  fequals.
  simpl.
  case_var~.
  rewrite~ subst_v_fresh.
Qed.
*)

(** An alternative, longer proof, but with fewer hypotheses *)
(* BUG in substitution or open? *)

Lemma subst_v_v_intro_alternative : forall x t u, 
  x \notin (fv_tm_v t) -> 
  open_rec_v 0 u t = subst_v_v u x (open_rec_v 0 x t).
Proof.
  introv H. generalize 0. gen H.
  induction t; simpl; intros; fequals*.
  case_nat*.
  simpl. case_var*.
  case_var*.

  

Lemma subst_v_intro_alternative : forall x t u, 
  x \notin (fv_tm t) -> 
  open_rec 0 u t = subst_v u x (open_rec 0 x t).
Proof.
  introv H. generalize 0. gen H.
  induction t; simpl; intros; fequals*.
  case_nat*.
  simpl. case_var*.
  case_var*.
Qed.

(** Substitution can be introduced to decompose a variable
    closing in terms of another one using a different name *)

Lemma close_rename : forall x y t,
  x \notin fv_tm t ->
  close_rec 0 y t =
  close_rec 0 x (subst_t (fevar x) y t).
Proof.
  introv.  generalize 0.
  induction t; simpl; intros l F; fequals~.
  case_var~; case_var~; simpl; case_var~.
Qed.

(* ********************************************************************** *)
(** Preservation of local closure through substitution and opening *)

(** Substitution of a locally closed terms into another one produces
    a locally closed term *)

Lemma subst_lc : forall x u t,
  lc_t u -> lc_t t -> lc_t (subst_t u x t).
Proof.
  introv U T. induction T; simple~;
  try case_var~;
  try apply_fresh lc_t_utype;
  try apply_fresh lc_t_etype;
  rewrite~ <- subst_t_open_rec.
Qed.

(** Substitution of a locally closed terms into a body one produces
    another body *)

Lemma subst_t_body_t :
  forall x t u,
    lc_t u -> body_t t -> body_t (subst_t u x t).
Proof.
  introv U [L H]. 
  exists_fresh. 
  rewrite~ <- subst_t_open_rec.
  apply~ subst_lc.
Qed.

(** Opening of a body with a locally closed terms produces a 
    locally closed term *)

Lemma open_rec_t_t_preserves_lc_t : forall t u,
  body_t t -> lc_t u -> lc_t (open_rec_t_t 0 u t).
Proof.
  introv [L H] U.
  pick_fresh x. 
  rewrite~ (@subst_t_intro x).
  apply~ subst_lc. 
Qed.


(* ====================================================================== *)
(** ** An induction principle for locally closed terms *)

(** Interaction of [size] with [open_var] *)

Lemma size_open_rec : forall x t,
  size (open_rec_t_t 0 (fevar x) t) = size t.
Proof.
  intros. generalize 0.
  induction t; intros; simple~. case_nat~.
Qed.

(** Interaction of [size] with [close_var] *)

Lemma size_close_var : forall x t,
  size (close_rec 0 x t) = size t.
Proof.
  intros. generalize 0.
  induction t; intros; simple~. case_var~.
Qed.

(** The induction principle *)
(* This would be a bear, let me check and see if I actually do induction on
 the size of types or terms in the thesis. 

Lemma lc_induct_size : forall P : trm -> Prop,
  (forall x, P (trm_fvar x)) ->
  (forall t1 t2,
     lc t1 -> P t1 -> lc t2 -> P t2 -> P (trm_app t1 t2)) ->
  (forall t1,
     body t1 ->
     (forall t2 x, x \notin fv t2 -> size t2 = size t1 ->
       lc (open_var t2 x) -> P (open_var t2 x)) -> 
     P (trm_abs t1)) ->
  (forall t, lc t -> P t).
Proof.
  intros P Hvar Happ Habs t. 
  induction t using (@measure_induction _ size).
  introv T. inverts T; simpl in H; auto.
  apply~ Habs. exists_fresh; auto. introv Fr Eq T.
   apply~ H. rewrite~ size_open_var.
Qed.

*)



End TTMP.