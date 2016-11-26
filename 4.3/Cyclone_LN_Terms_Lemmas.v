(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION".   Daniel Grossman, August 2003 *)
(* Lemmas from the Lambda JAR paper built just for Terms. *)
(* Brian Milnes 2016 *)

Set Implicit Arguments.
Require Export Cyclone_LN_Tactics Cyclone_LN_Types Cyclone_LN_Types_Lemmas Cyclone_LN_Terms.
Open Scope cyclone_scope.
Open Scope nat_scope.
Import TM.

(* TODO: I'm really messing with Arthur's names and it's not a good way to do things. *)

Module TMP. (* TM = Term P = Proof. *)

(* This is the version just for the lemmas about manipulating terms. *)

(* ====================================================================== *)
(** ** Proofs *)

(* ********************************************************************** *)
(** Variable closing and variable opening are reciprocal of one another *)

(** Showing that [close_var] after [open_var] is the identity is easy *)

Lemma close_v_tm_v_open_v_tm_v :
  forall t x n,
  x \notin fv_v t -> 
  close_rec_v n x (open_rec_v n x t) = t.
Proof.
  introv.
  induction t; simpl; introv Fr; fequals~.
  case_nat~. simpl. case_var~.
  case_var~.
Qed.

(* The application of a mutually defined induction principle in Coq is
 quite verbose. You must make N predicates for N way mutually recursively
 defined inductive types and then apply them. Each of the N must have
 it's own Lemma. To shorten this, I define functions and an Ltac to
 prevent the repeating of any text that I can. *)

Function close_v_tm_st_open_v_tm_st_pred (t : St) :=
  forall x n, 
    x \notin fv_st t ->
    close_rec_st n x (open_rec_st n x t) = t.
Hint Unfold close_v_tm_st_open_v_tm_st_pred.

Function close_v_tm_e_open_v_tm_e_pred (t : E) :=
  forall x n, 
    x \notin fv_e t ->
    close_rec_e n x (open_rec_e n x t) = t.
Hint Unfold close_v_tm_e_open_v_tm_e_pred.

Function close_v_tm_f_open_v_tm_f_pred (t : F) :=
  forall x n, 
    x \notin fv_f t ->
    close_rec_f n x (open_rec_f n x t) = t.
Hint Unfold close_v_tm_f_open_v_tm_f_pred.

Ltac close_v_tm_X_open_v_tm_X_proof :=
  autounfold in *;
  simpl;
  intros;
  fequals~;
  applys* close_v_tm_v_open_v_tm_v.

Ltac close_v_tm_X_open_v_tm_X_induction M :=
  apply(M
          close_v_tm_st_open_v_tm_st_pred
          close_v_tm_e_open_v_tm_e_pred
          close_v_tm_f_open_v_tm_f_pred).

Lemma close_v_tm_st_open_v_tm_st :
  forall t, close_v_tm_st_open_v_tm_st_pred t.
Proof.
  close_v_tm_X_open_v_tm_X_induction St_ind_mutual;
  close_v_tm_X_open_v_tm_X_proof.
Qed.

Lemma close_v_tm_e_open_v_tm_e :
  forall t, close_v_tm_e_open_v_tm_e_pred t.
Proof.
  close_v_tm_X_open_v_tm_X_induction E_ind_mutual;
  close_v_tm_X_open_v_tm_X_proof.
Qed.

Lemma close_v_tm_f_open_v_tm_f :
  forall t, close_v_tm_f_open_v_tm_f_pred t.
Proof.
  close_v_tm_X_open_v_tm_X_induction F_ind_mutual;
  close_v_tm_X_open_v_tm_X_proof.
Qed.

Lemma close_v_tm_open_v_tm :
  forall x t n, 
  x \notin fv t -> 
  close_rec n x (open_rec n x t) = t.
Proof.
  destruct t; simpl; intros; fequals~.
  applys~ close_v_tm_st_open_v_tm_st.
  applys~ close_v_tm_e_open_v_tm_e.
  applys~ close_v_tm_f_open_v_tm_f.
Qed.

(** The other direction is much harder; First, we first need
    to establish the injectivity of [open_var] *)

Lemma open_rec_st_inj :
  forall x n t1 t2, 
    x \notin (fv_st t1) ->
    x \notin (fv_st t2) -> 
    open_rec_st n x t1 = open_rec_st n x t2 ->
    (t1 = t2).
Proof.
  introv Fr1 Fr2 Eq.
  rewrite~ <- (@close_v_tm_st_open_v_tm_st t1 x n).
  rewrite~ <- (@close_v_tm_st_open_v_tm_st t2 x n).
  fequals~.
Qed.

Lemma open_rec_e_inj :
  forall x n t1 t2, 
    x \notin (fv_e t1) ->
    x \notin (fv_e t2) -> 
    open_rec_e n x t1 = open_rec_e n x t2 ->
    (t1 = t2).
Proof.
  introv Fr1 Fr2 Eq.
  rewrite~ <- (@close_v_tm_e_open_v_tm_e t1 x n).
  rewrite~ <- (@close_v_tm_e_open_v_tm_e t2 x n).
  fequals~.
Qed.

Lemma open_rec_f_inj :
  forall x n t1 t2, 
    x \notin (fv_f t1) ->
    x \notin (fv_f t2) -> 
    open_rec_f n x t1 = open_rec_f n x t2 ->
    (t1 = t2).
Proof.
  introv Fr1 Fr2 Eq.
  rewrite~ <- (@close_v_tm_f_open_v_tm_f t1 x n).
  rewrite~ <- (@close_v_tm_f_open_v_tm_f t2 x n).
  fequals~.
Qed.

Lemma open_rec_inj :
  forall x n t1 t2, 
    x \notin (fv t1) ->
    x \notin (fv t2) -> 
    open_rec n x t1 = open_rec n x t2 ->
    (t1 = t2).
Proof.
  introv Fr1 Fr2 Eq.
  rewrite~ <- (@close_v_tm_open_v_tm x t1 n).
  rewrite~ <- (@close_v_tm_open_v_tm x t2 n).
  fequals~.
Qed.

(** We also need one (tricky) auxiliary lemma to handle the binder case *)

(* Question: Have I weakened this too much? *)
Lemma open_rec_v_close_rec_v_on_open_rec_v:
  forall x y z t i j,
    i <> j ->
    y <> x ->
    y \notin (fv_v t) ->
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
    y \notin (fv_e t) ->
    open_rec_e i y (open_rec_e j z (close_rec_e j x t))
  = open_rec_e j z (close_rec_e j x (open_rec_e i y t)).
Hint Unfold open_rec_e_close_rec_e_on_open_rec_e_pred.

Function open_rec_st_close_rec_st_on_open_rec_st_pred (t : St) :=
  forall x y z i j,
    i <> j ->
    y <> x ->
    y \notin (fv_st t) ->
    open_rec_st i y (open_rec_st j z (close_rec_st j x t))
  = open_rec_st j z (close_rec_st j x (open_rec_st i y t)).
Hint Unfold open_rec_st_close_rec_st_on_open_rec_st_pred.

Function open_rec_f_close_rec_f_on_open_rec_f_pred (t : F) :=
  forall x y z i j,
    i <> j ->
    y <> x ->
    y \notin (fv_f t) ->
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
    y \notin (fv t) ->
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
            |- ?t = _ => pick_fresh y from (fv_st t)
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
     lc t ->
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

Lemma close_v_tm_on_var_inj :
  forall x t1 t2, 
    lc t1 ->
    lc t2 ->
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
    lc_f (dfun t0 t1 s) <-> body (term_st s).
Proof. 
  intros.
  unfold body.
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
    lc_st (openx e s) <-> body (term_st s).
Proof. 
  introv lce.
  unfold body.
  simpl.
  iff H.
  inversions* H.

  inversion H.
  apply lc_open with (L':= x \u (fv_st s)); auto.
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
    lc_st (openstar e s) <-> body (term_st s).
Proof. 
  introv lce.
  unfold body.
  simpl.
  iff H.
  inversions* H.

  inversion H.
  apply lc_openstar with (L':= x \u (fv_st s)); auto.
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
    lc_st (letx e s) <-> body (term_st s).
Proof. 
  introv lce.
  unfold body.
  simpl.
  iff H.
  inversions* H.

  inversion H.
  apply lc_st_letx with (L':= x \u (fv_st s)); auto.
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

Lemma fv_v_open :
  forall (t : V) (u : var) (n: nat),
    fv_v (open_rec_v n u t) \c  fv_v t \u \{u}.
Proof.
  intros.
  destruct t; simpl; try case_nat; simpl; fset.
Qed.

Function fv_st_open_pred (t : St) :=
  forall (u : var) (n : nat),
    fv_st (open_rec_st n u t) \c fv_st t \u \{u}.
Hint Unfold fv_st_open_pred.

Function fv_e_open_pred (t : E) :=
  forall (u : var) (n : nat),
    fv_e (open_rec_e n u t) \c fv_e t \u \{u}.
Hint Unfold fv_e_open_pred.

Function fv_f_open_pred (t : F) :=
  forall (u : var) (n : nat),
    fv_f (open_rec_f n u t) \c fv_f t \u \{u}.
Hint Unfold fv_f_open_pred.

Ltac fv_X_open_proof :=
  autounfold in *;
  intros l; simpl; try case_nat; try fset;
  intros;
  applys~ fv_v_open.

Ltac fv_X_open_induction T :=
  apply (T
           fv_st_open_pred
           fv_e_open_pred
           fv_f_open_pred).
  
Lemma fv_st_open:
  forall t u n,
    fv_st (open_rec_st n u t) \c fv_st t \u \{u}.
Proof.
  fv_X_open_induction St_ind_mutual;
  fv_X_open_proof.
Qed.

Lemma fv_e_open :
  forall t u n, 
    fv_e (open_rec_e n u t) \c fv_e t \u \{u}.
Proof.
  fv_X_open_induction E_ind_mutual;
  fv_X_open_proof.
Qed.

Lemma fv_f_open :
  forall t u n, 
    fv_f (open_rec_f n u t) \c fv_f t \u \{u}.
Proof.
  fv_X_open_induction F_ind_mutual;
  fv_X_open_proof.
Qed.

Lemma fv_open : forall t u,
  fv (open u t) \c fv t \u \{u}.
Proof.
  destruct t; intros.
  apply fv_st_open.
  apply fv_e_open.
  apply fv_f_open.
Qed.

(** In particular, opening with variable [x] adds [x] to the set 
    of free variables *)

Lemma open_var_fv : forall x t,
  fv (open_rec 0 x t) \c (fv t \u \{x}).
Proof.
  intros.
  apply fv_open. 
Qed.

(** Closing w.r.t variable [x] removes [x] from the set of free variables *)

Lemma close_tv_v_fv : forall x t n,
  fv_v (close_rec_v n x t) \c (fv_v t \- \{x}).
Proof.
  intros.
  destruct t; simpl; fset.
  case_var~; simpl; fset.
Qed.

Function close_tv_st_fv_pred (t : St) :=
  forall x n,
    fv_st (close_rec_st n x t) \c (fv_st t \- \{x}).
Hint Unfold close_tv_st_fv_pred.

Function close_tv_e_fv_pred (t : E) :=
  forall x n,
    fv_e (close_rec_e n x t) \c (fv_e t \- \{x}).
Hint Unfold close_tv_e_fv_pred.

Function close_tv_f_fv_pred (t : F) :=
  forall x n,
    fv_f (close_rec_f n x t) \c (fv_f t \- \{x}).
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
    fv_st (close_rec_st n x t) \c (fv_st t \- \{x}).
Proof.
  close_tv_X_fv_induction St_ind_mutual;
  close_tv_X_fv_proof.
Qed.

Lemma close_tv_e_fv :
  forall t x n,
    fv_e (close_rec_e n x t) \c (fv_e t \- \{x}).
Proof.
  close_tv_X_fv_induction E_ind_mutual;
  close_tv_X_fv_proof.
Qed.

Lemma close_tv_f_fv :
  forall t x n,
    fv_f (close_rec_f n x t) \c (fv_f t \- \{x}).
Proof.
  close_tv_X_fv_induction F_ind_mutual;
  close_tv_X_fv_proof.
Qed.

Lemma close_tv_fv : forall x t,
  fv (close_rec 0 x t) \c (fv t \- \{x}).
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
   |- { S _ TM_st> _} ?s = ?s =>
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
    lc t -> 
    forall u n,
       open_rec n u t = t.
Proof.
  lets L1: open_rec_st_lc_t.
  lets L2: open_rec_e_lc_t.  
  lets L3: open_rec_f_lc_t.  
  destruct t; intros; simpl; fequals~; inversions~ H.
Qed.

Lemma subst_v_open_v:
  forall (z x y : var) s n,
    z <> x ->
    z <> y ->
    {n TM_v> z} ([x TM_v> y] s) = [x TM_v> y] {n TM_v> z} s.
Proof.
  intros.
  induction s.
  simpl.
  case_nat~.
  simpl.
  case_var~.
  simpl.
  case_var~.
Qed.

Function subst_st_open_st_pred (s : St) :=
  forall (z x y : var) n,
    z <> x ->
    z <> y ->
    {n TM_st> z} ([x TM_st> y] s) = [x TM_st> y] {n TM_st> z} s.
Hint Unfold subst_st_open_st_pred.

Function subst_e_open_e_pred (s : E) :=
  forall (z x y : var) n,
    z <> x ->
    z <> y ->
    {n TM_e> z} ([x TM_e> y] s) = [x TM_e> y] {n TM_e> z} s.
Hint Unfold subst_e_open_e_pred.

Function subst_f_open_f_pred (s : F) :=
  forall (z x y : var) n,
    z <> x ->
    z <> y ->
    {n TM_f> z} ([x TM_f> y] s) = [x TM_f> y] {n TM_f> z} s.
Hint Unfold subst_f_open_f_pred.

Ltac subst_X_open_X_induction T :=
  apply (T 
           subst_st_open_st_pred
           subst_e_open_e_pred
           subst_f_open_f_pred).

Ltac subst_X_open_X_proof :=
  unfold subst_st_open_st_pred, subst_e_open_e_pred, subst_f_open_f_pred;
  simpl;
  intros;
  fequals~;
  try applys~ subst_v_open_v.

Lemma subst_st_open_st:
  forall t,  subst_st_open_st_pred t.
Proof.
  subst_X_open_X_induction St_ind_mutual;
  subst_X_open_X_proof.
Qed.

Lemma subst_e_open_e:
  forall t,  subst_e_open_e_pred t.
Proof.
  subst_X_open_X_induction E_ind_mutual;
  subst_X_open_X_proof.
Qed.

Lemma subst_f_open_f:
  forall t,  subst_f_open_f_pred t.
Proof.
  subst_X_open_X_induction F_ind_mutual;
  subst_X_open_X_proof.
Qed.

Lemma subst_open:
  forall (z x y : var) s n,
    z <> x ->
    z <> y ->
    {n TM> z} ([x TM> y] s) = [x TM> y] {n TM> z} s.
Proof.
  destruct s; simpl; intros; fequals~.
  applys~ subst_st_open_st.
  applys~ subst_e_open_e.
  applys~ subst_f_open_f.
Qed.

(** In particular, we can distribute [subst] on [open_var] *)

Lemma subst_v_open_rec_v:
  forall t x y u n,
    x <> y ->
    y <> u ->
    subst_v u x (open_rec_v n y t) = open_rec_v n y (subst_v u x t).
Proof.
  intros.
  rewrite~ subst_v_open_v.
Qed.

Function subst_st_open_rec_st_pred (t : St) :=
  forall x y u n,
    x <> y ->
    y <> u ->
    subst_st u x (open_rec_st n y t) = open_rec_st n y (subst_st u x t).
Hint Unfold subst_st_open_rec_st_pred.

Function subst_e_open_rec_e_pred (t : E) :=
  forall x y u n,
    x <> y ->
    y <> u ->
    subst_e u x (open_rec_e n y t) = open_rec_e n y (subst_e u x t).
Hint Unfold subst_e_open_rec_e_pred.

Function subst_f_open_rec_f_pred (t : F) :=
  forall x y u n,
    x <> y ->
    y <> u ->
    subst_f u x (open_rec_f n y t) = open_rec_f n y (subst_f u x t).
Hint Unfold subst_f_open_rec_f_pred.

Ltac subst_X_open_rec_X_induction T :=
  apply (T 
           subst_st_open_rec_st_pred
           subst_e_open_rec_e_pred
           subst_f_open_rec_f_pred).

Ltac subst_X_open_rec_X_proof :=
  autounfold in *;
  simpl;
  intros;
  fequals~;
  try rewrite~ subst_v_open_v.

Lemma subst_st_open_rec_st:
  forall t, subst_st_open_rec_st_pred t.
Proof.
  subst_X_open_rec_X_induction St_ind_mutual;
  subst_X_open_rec_X_proof.
Qed.

Lemma subst_e_open_rec_e:
  forall t, subst_e_open_rec_e_pred t.
Proof.
  subst_X_open_rec_X_induction E_ind_mutual;
  subst_X_open_rec_X_proof.
Qed.

Lemma subst_f_open_rec_f:
  forall t, subst_f_open_rec_f_pred t.
Proof.
  subst_X_open_rec_X_induction F_ind_mutual;
  subst_X_open_rec_X_proof.
Qed.

Lemma subst_open_rec:
  forall t x y u n,
    x <> y ->
    y <> u ->
    subst u x (open_rec n y t) = open_rec n y (subst u x t).
Proof.
  destruct t; simpl; intros; fequals~.
  applys~ subst_st_open_rec_st.
  applys~ subst_e_open_rec_e.
  applys~ subst_f_open_rec_f.
Qed.

(** For the distributivity of [subst] on [close_var],
    one simple intermediate lemmas is required to 
    say that closing on a fresh name is the identity *)

Lemma close_rec_v_fresh :
  forall x t k,
  x \notin fv_v t -> close_rec_v k x t = t.
Proof.
  destruct t; intros; simpls*.
  case_var~.
Qed.

Function close_rec_st_fresh_pred (t : St) :=
  forall x k,
    x \notin fv_st t -> close_rec_st k x t = t.
Hint Unfold close_rec_st_fresh_pred.
  
Function close_rec_e_fresh_pred (t : E) :=
  forall x k,
    x \notin fv_e t -> close_rec_e k x t = t.
Hint Unfold close_rec_e_fresh_pred.

Function close_rec_f_fresh_pred (t : F) :=
  forall x k,
    x \notin fv_f t -> close_rec_f k x t = t.
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
    x \notin fv_st t -> close_rec_st k x t = t.
Proof.
  close_rec_X_fresh_induction St_ind_mutual;
  close_rec_X_fresh_proof.
Qed.

Lemma close_rec_e_fresh :
  forall t x k,
    x \notin fv_e t -> close_rec_e k x t = t.
Proof.
  close_rec_X_fresh_induction E_ind_mutual;
  close_rec_X_fresh_proof.
Qed.

Lemma close_rec_f_fresh :
  forall t x k,
    x \notin fv_f t -> close_rec_f k x t = t.
Proof.
  close_rec_X_fresh_induction F_ind_mutual;
  close_rec_X_fresh_proof.
Qed.

Lemma close_rec_fresh :
  forall x t k,
    x \notin fv t -> close_rec k x t = t.
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
    y \notin fv_v (fevar u) -> 
    forall n, 
      subst_v u x (close_rec_v n y t) =
      close_rec_v n y (subst_v u x t).
Proof.
  intros.
  induction t; simpl; auto;
  simpl; case_var~; simpl; case_var~; simpl; case_var~.
  simpl in H0.
  assert(y <> y).
  auto.
  false.
Qed.

Function subst_st_close_rec_st_pred (t : St) :=
  forall x y u,
    x <> y ->
    y \notin fv_v (fevar u) -> 
    forall n, 
      subst_st u x (close_rec_st n y t) =
      close_rec_st n y (subst_st u x t).
Hint Unfold subst_st_close_rec_st_pred.

Function subst_e_close_rec_e_pred (t : E) :=
  forall x y u,
    x <> y ->
    y \notin fv_v (fevar u) -> 
    forall n,
      subst_e u x (close_rec_e n y t) =
      close_rec_e n y (subst_e u x t).
Hint Unfold subst_e_close_rec_e_pred.

Function subst_f_close_rec_f_pred (t : F) :=
  forall x y u,
    x <> y ->
    y \notin fv_v (fevar u) -> 
    forall n, 
      subst_f u x (close_rec_f n y t) =
      close_rec_f n y (subst_f u x t).         
Hint Unfold subst_f_close_rec_f_pred.

Ltac subst_X_close_rec_X_induction T :=
  apply (T
           subst_st_close_rec_st_pred
           subst_e_close_rec_e_pred 
           subst_f_close_rec_f_pred).

Ltac subst_X_close_rec_X_proof :=
  autounfold in *;
  simpl;
  intros;
  fequals~;
  lets~ J: subst_v_close_rec_v;
  auto.

Lemma subst_st_close_rec_st:
  forall t, subst_st_close_rec_st_pred t.
Proof.
  subst_X_close_rec_X_induction St_ind_mutual;
  subst_X_close_rec_X_proof.
Qed.

Lemma subst_e_close_rec_e:
  forall t, subst_e_close_rec_e_pred t.
Proof.
  subst_X_close_rec_X_induction E_ind_mutual;
  subst_X_close_rec_X_proof.
Qed.

Lemma subst_f_close_rec_f:
  forall t, subst_f_close_rec_f_pred t.
Proof.
  subst_X_close_rec_X_induction F_ind_mutual;
  subst_X_close_rec_X_proof.
Qed.

Lemma subst_close_rec:
  forall t x y u,
    x <> y ->
    y \notin fv_v (fevar u) -> 
    forall n, 
      subst u x (close_rec n y t) = close_rec n y (subst u x t).
Proof.
  destruct t; simpl; intros; fequals~.
  applys~ subst_st_close_rec_st.
  applys~ subst_e_close_rec_e.
  applys~ subst_f_close_rec_f.
Qed.

(** Substitution for a fresh name is the identity *)

Lemma subst_v_fresh : forall x t u, 
  x \notin fv_v t -> subst_v u x t = t.
Proof.
  destruct t; try solve[simpl; intros; fequals~].
  intros.
  simpl in H.
  assert(x <> v).
  auto.
  simpl.
  case_var~.
Qed.

Function subst_st_fresh_pred (t : St) :=
  forall x u, 
    x \notin fv_st t -> subst_st u x t = t.
Hint Unfold subst_st_fresh_pred.

Function subst_e_fresh_pred (t : E) :=
  forall x u, 
    x \notin fv_e t -> subst_e u x t = t.
Hint Unfold subst_e_fresh_pred.

Function subst_f_fresh_pred (t : F) :=  
forall x u, 
  x \notin fv_f t -> subst_f u x t = t.
Hint Unfold subst_f_fresh_pred.

Ltac subst_X_fresh_induction T :=
  apply(T 
          subst_st_fresh_pred
          subst_e_fresh_pred
          subst_f_fresh_pred).

Ltac subst_X_fresh_proof :=
  lets: subst_v_fresh;
  autounfold in *;
  simpl;
  intros;
  fequals~.

Lemma subst_st_fresh:
  forall t x u, 
  x \notin fv_st t -> subst_st u x t = t.
Proof.
  subst_X_fresh_induction St_ind_mutual;
  subst_X_fresh_proof.
Qed.

Lemma subst_e_fresh: 
forall t x u, 
  x \notin fv_e t -> subst_e u x t = t.
Proof.
  subst_X_fresh_induction E_ind_mutual;
  subst_X_fresh_proof.
Qed.

Lemma subst_f_fresh:
  forall t x u, 
  x \notin fv_f t -> subst_f u x t = t.
Proof.
  subst_X_fresh_induction F_ind_mutual;
  subst_X_fresh_proof.
Qed.

Lemma subst_fresh : forall x t u, 
  x \notin fv t -> subst u x t = t.
Proof.
  lets: subst_st_fresh.
  lets: subst_e_fresh.
  lets: subst_f_fresh.
  destruct t; simpl; intros; fequals~.
Qed.

(** Substitution can be introduced to decompose an opening *)

Lemma subst_v_intro :
  forall u, 
    lc_v (fevar u) ->
    forall t n x,
      x \notin (fv_v t) -> 
      open_rec_v n u t = subst_v u x (open_rec_v n x t).
Proof.
  introv H I. gen I.
  induction t; simpl; intros; fequals*.
  case_nat*.
  simpl. case_var*.
  case_var*.
Qed.

(** An alternative, longer proof, but with fewer hypotheses *)

Lemma subst_v_intro_alternative :
  forall t n x u, 
    x \notin (fv_v t) -> 
    open_rec_v n u t = subst_v u x (open_rec_v n x t).
Proof.
  introv H. gen H.
  induction t; simpl; intros; fequals*.
  case_nat*.
  simpl. case_var*.
  case_var*.
Qed.
  
Function subst_st_intro_alternative_st_pred (t : St) :=
  forall n x u, 
  x \notin (fv_st t) -> 
  open_rec_st n u t = subst_st u x (open_rec_st n x t).
Hint Unfold subst_st_intro_alternative_st_pred.

Function subst_e_intro_alternative_e_pred (t : E) :=
  forall n x u, 
    x \notin (fv_e t) -> 
    open_rec_e n u t = subst_e u x (open_rec_e n x t).
Hint Unfold subst_e_intro_alternative_e_pred.

Function subst_f_intro_alternative_f_pred (t : F) :=
  forall n x u, 
    x \notin (fv_f t) -> 
    open_rec_f n u t = subst_f u x (open_rec_f n x t).
Hint Unfold subst_f_intro_alternative_f_pred.

Ltac subst_X_intro_alternative_X_induction T :=
  apply (T
           subst_st_intro_alternative_st_pred
           subst_e_intro_alternative_e_pred
           subst_f_intro_alternative_f_pred).

Ltac subst_X_intro_alternative_X_proof :=
  autounfold in *;
  try solve[
        simpl;
        intros;
        fequals*;
        try apply~ subst_v_intro_alternative].

Lemma subst_st_intro_alternative:
  forall t, subst_st_intro_alternative_st_pred t.
Proof.  
  subst_X_intro_alternative_X_induction St_ind_mutual;
  subst_X_intro_alternative_X_proof.
Qed.

Lemma subst_e_intro_alternative:
  forall t, subst_e_intro_alternative_e_pred t.
Proof.  
  subst_X_intro_alternative_X_induction E_ind_mutual;
  subst_X_intro_alternative_X_proof.
Qed.

Lemma subst_f_intro_alternative:
  forall t, subst_f_intro_alternative_f_pred t.
Proof.  
  subst_X_intro_alternative_X_induction F_ind_mutual;
  subst_X_intro_alternative_X_proof.
Qed.

Lemma subst_intro_alternative : forall x t u, 
  x \notin (fv t) -> 
  open_rec 0 u t = subst u x (open_rec 0 x t).
Proof.
  destruct t; simpl; intros; fequals~.
  applys~ subst_st_intro_alternative.
  applys~ subst_e_intro_alternative.
  applys~ subst_f_intro_alternative.
Qed.

(** Substitution can be introduced to decompose a variable
    closing in terms of another one using a different name *)

Lemma close_v_rename :
  forall t n x y,
    x \notin fv_v t ->
    close_rec_v n y t =
    close_rec_v n x (subst_v x y t).
Proof.
  introv.  
  induction t;
  simpl;
  intros;
  auto;
  case_var~;
  simpl;
  case_var~.
Qed.

Function close_st_rename_pred (t : St) :=
  forall n x y,
    x \notin fv_st t ->
    close_rec_st n y t =
    close_rec_st n x (subst_st x y t).
Hint Unfold close_st_rename_pred.

Function close_e_rename_pred (t : E) :=
  forall n x y,
    x \notin fv_e t ->
    close_rec_e n y t =
    close_rec_e n x (subst_e x y t).
Hint Unfold close_e_rename_pred.

Function close_f_rename_pred (t : F) :=
  forall n x y,
    x \notin fv_f t ->
    close_rec_f n y t =
    close_rec_f n x (subst_f x y t).
Hint Unfold close_f_rename_pred.

Ltac close_X_rename_induction T :=
  apply (T
           close_st_rename_pred
           close_e_rename_pred
           close_f_rename_pred).           

Ltac close_X_rename_proof := 
  autounfold in *;
  simpl; intros; fequals~;
  try applys~ close_v_rename.

Lemma close_st_rename:
  forall t, close_st_rename_pred t.
Proof.
  close_X_rename_induction St_ind_mutual;
  close_X_rename_proof.
Qed.

Lemma close_e_rename:
  forall t, close_e_rename_pred t.
Proof.
  close_X_rename_induction E_ind_mutual;
  close_X_rename_proof.
Qed.

Lemma close_f_rename:
  forall t, close_f_rename_pred t.
Proof.
  close_X_rename_induction F_ind_mutual;
  close_X_rename_proof.
Qed.

Lemma close_rename : forall x y t,
  x \notin fv t ->
  close_rec 0 y t =
  close_rec 0 x (subst x y t).
Proof.
  destruct t; simpl; intros; fequals~.
  applys~ close_st_rename.
  applys~ close_e_rename.
  applys~ close_f_rename.
Qed.

(* ********************************************************************** *)
(** Preservation of local closure through substitution and opening *)

(** Substitution of a locally closed terms into another one produces
    a locally closed term *)

Lemma subst_lc_v : forall x y t,
  lc_v t -> lc_v (subst_v x y t).
Proof.
  introv lcvt.
  induction lcvt.
  simpl.
  destruct (classicT (x0 = y));
  auto.
Qed.
  
Function subst_st_lc_st_pred (t : St) (_ : lc_st t) :=
  forall x y,
    lc_st (subst_st x y t).
Hint Unfold subst_st_lc_st_pred.

Function subst_e_lc_e_pred (t : E)  (_ : lc_e t) :=
  forall x y,
    lc_e (subst_e x y t).
Hint Unfold subst_e_lc_e_pred.

Function subst_f_lc_f_pred (t : F) (_ : lc_f t) :=
  forall x y,
    lc_f (subst_f x y t).
Hint Unfold subst_f_lc_f_pred.

Ltac subst_X_lc_X_induction T :=
  apply (T
           subst_st_lc_st_pred
           subst_e_lc_e_pred 
           subst_f_lc_f_pred).

Ltac subst_X_lc_X_proof :=
  autounfold in *;
  intros;
  simpl;
  auto;
  try case_var~;
  try apply_fresh lc_st_letx; auto;
  try apply_fresh lc_open; auto;
  try apply_fresh lc_openstar; auto;
  try apply_fresh lc_dfun; auto;
  rewrite subst_st_open_st; auto.

Lemma subst_st_lc_st:
  forall t,
    lc_st t ->
    forall x y, 
      lc_st (subst_st x y t).
Proof.
  subst_X_lc_X_induction lc_st_ind_mutual;
  subst_X_lc_X_proof.
Qed.

Lemma subst_e_lc_e:
  forall t,
    lc_e t ->
    forall x y, 
      lc_e (subst_e x y t).
Proof.
  subst_X_lc_X_induction lc_e_ind_mutual;
  subst_X_lc_X_proof.
Qed.

Lemma subst_f_lc_f:
  forall t,
    lc_f t ->
    forall x y, 
      lc_f (subst_f x y t).
Proof.
  subst_X_lc_X_induction lc_f_ind_mutual;
  subst_X_lc_X_proof.
Qed.

Lemma subst_lc:
  forall t,
    lc t ->
    forall x y, 
      lc (subst x y t).
Proof.
  intros.
  destruct t; simpl; intros; fequals~; constructor; inversions~ H.
  applys~ subst_st_lc_st.
  applys~ subst_e_lc_e.
  applys~ subst_f_lc_f.
Qed.

(** Substitution of a locally closed terms into a body one produces
    another body *)

Lemma subst_body:
  forall t x u,
    lc_v (fevar u) ->
    body t ->
    body (subst u x t).
Proof.
  introv U [L H]. 
  exists_fresh.
  asserts~ xney : (x <> y).
  asserts~ yneu : (y <> u).
  Unset Print Notations.
  lets M: subst_open_rec.
  specialize (M t x y u 0 xney yneu).
  unfold open.
  rewrite~ <- M.
  apply~ subst_lc.
Qed.

(** Opening of a body with a locally closed terms produces a 
    locally closed term *)

Lemma open_rec_t_t_preserves_lc_t :
  forall t u,
    body t
    -> lc_v (fevar u)
    -> lc (open_rec 0 u t).
Proof.
  introv [L H] U.
  pick_fresh x. 
  rewrite~ (@subst_intro_alternative x).
  apply~ subst_lc. 
Qed.

(* ====================================================================== *)
(** ** An induction principle for locally closed terms *)

(** Interaction of [size] with [open_var] *)

Lemma size_v_open_v_rec : forall t n x,
  size_v (open_rec_v n x t) = size_v t.
Proof.
  induction t; simpl; intros.
  case_nat~.
  compute.
  reflexivity.
Qed.

Function size_st_open_rec_st_pred (t : St) :=
  forall n x,
    size_st (open_rec_st n x t) = size_st t.
Hint Unfold size_st_open_rec_st_pred.

Function size_e_open_rec_e_pred (t : E) :=
  forall n x,
    size_e (open_rec_e n x t) = size_e t.
Hint Unfold size_e_open_rec_e_pred.

Function size_f_open_rec_f_pred (t : F) :=
  forall n x,
    size_f (open_rec_f n x t) = size_f t.
Hint Unfold size_f_open_rec_f_pred.

Ltac size_X_open_rec_X_induction T :=
  apply (T
           size_st_open_rec_st_pred
           size_e_open_rec_e_pred
           size_f_open_rec_f_pred).

Ltac size_X_open_rec_X_proof :=
  autounfold in *;
  simpl;
  intros;
  fequals~.

Lemma size_st_open_st_rec:
  forall t,
    size_st_open_rec_st_pred t.
Proof.
  size_X_open_rec_X_induction St_ind_mutual;
  size_X_open_rec_X_proof.
Qed.

Lemma size_e_open_e_rec:
  forall t,
    size_e_open_rec_e_pred t.
Proof.
  size_X_open_rec_X_induction E_ind_mutual;
  size_X_open_rec_X_proof.
Qed.
  
Lemma size_f_open_f_rec:
  forall t,
    size_f_open_rec_f_pred t.
Proof.
  size_X_open_rec_X_induction F_ind_mutual;
  size_X_open_rec_X_proof.
Qed.

Lemma size_open_rec : forall t n x,
  size (open_rec n x t) = size t.
Proof.
  destruct t; simpl; intros; fequals~.
  applys~ size_st_open_st_rec.
  applys~ size_e_open_e_rec.
  applys~ size_f_open_f_rec.
Qed.

(** Interaction of [size] with [close_var] *)

Lemma size_v_close_v:
  forall t x n,
    size_v (close_rec_v n x t) = size_v t.
Proof.
  intros.
  compute.
  auto.
Qed.

Function size_st_close_st_pred (t : St) :=
  forall x n,
    size_st (close_rec_st n x t) = size_st t.  
Hint Unfold size_st_close_st_pred.

Function size_e_close_e_pred (t : E) :=
  forall x n,
    size_e (close_rec_e n x t) = size_e t.  
Hint Unfold size_e_close_e_pred.

Function size_f_close_f_pred (t : F) :=
  forall x n,
    size_f (close_rec_f n x t) = size_f t.  
Hint Unfold size_f_close_f_pred.

Ltac size_X_close_X_induction T :=
  apply (T
           size_st_close_st_pred
           size_e_close_e_pred
           size_f_close_f_pred).

Ltac size_X_close_X_proof :=
  autounfold in *;
  simpl;
  intros;
  fequals~.

Lemma size_st_close_st:
  forall t,
    size_st_close_st_pred t.
Proof.
  size_X_close_X_induction St_ind_mutual;
  size_X_close_X_proof.
Qed.

Lemma size_e_close_e:
  forall t,
    size_e_close_e_pred t.
Proof.
  size_X_close_X_induction E_ind_mutual;
  size_X_close_X_proof.
Qed.

Lemma size_f_close_f:
  forall t,
    size_f_close_f_pred t.
Proof.
  size_X_close_X_induction F_ind_mutual;
  size_X_close_X_proof.
Qed.

Lemma size_close_var : forall x t,
  size (close_rec 0 x t) = size t.
Proof.
  destruct t; simpl; fequals~.
  applys~ size_st_close_st.
  applys~ size_e_close_e.
  applys~ size_f_close_f.
Qed.

(** The induction principle on size is not needed. *)
(* This would be very large, three induction principles. *)
(* And the only thing Dan seems to induct on is the length of a context,
  not its full size. So unless I need this I won't make it. *)

End TMP.

