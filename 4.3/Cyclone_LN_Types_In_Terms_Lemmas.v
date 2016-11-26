(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION".   Daniel Grossman, August 2003 *)
(* Lemmas from the Lambda JAR paper. *)
(* Brian Milnes 2016 *)

Set Implicit Arguments.
Require Export TLC.LibFset.
Require Export Cyclone_LN_Tactics Cyclone_LN_Types Cyclone_LN_Terms Cyclone_LN_Types_In_Terms.
Require Export Cyclone_LN_Types_Lemmas Cyclone_LN_Terms_Lemmas.
Open Scope cyclone_scope.
Open Scope nat_scope.
Open Scope fset_scope.
Import TTM.
Import TMP.

(* This is the version just for the lemmas manipulating types in terms. *)
Module TTMP. (* T = Types TM = Term P = Proof. *)

(* ====================================================================== *)
(** ** Proofs *)

(* ********************************************************************** *)
(** Variable closing and variable opening are reciprocal of one another *)

(** Showing that [close_var] after [open_var] is the identity is easy *)

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

Function close_tau_open_tau_pred (t : Tau) :=
  forall alpha n, 
    alpha \notin T.fv t ->
    T.close_rec n alpha (T.open_rec n (ftvar alpha) t) = t.
Hint Unfold close_tau_open_tau_pred.

Ltac close_X_open_X_proof :=
  autounfold in *;
  simpl;
  intros;
  fequals~;
  try applys* close_v_open_v;
  try case_nat~;
  simpl;
  try case_var~;
  try case_var~.

Ltac close_X_open_X_induction M :=
  apply(M
          close_st_open_st_pred
          close_e_open_e_pred
          close_f_open_f_pred
          close_tau_open_tau_pred).

Lemma close_st_open_st :
  forall t alpha n, 
    alpha \notin fv_st t ->
    close_rec_st n alpha (open_rec_st n (ftvar alpha) t) = t.
Proof.
  close_X_open_X_induction Tau_St_ind_mutual;
  close_X_open_X_proof.
Qed.

Lemma close_e_open_e :
  forall t, close_e_open_e_pred t.
Proof.
  close_X_open_X_induction Tau_E_ind_mutual;
  close_X_open_X_proof.
Qed.

Lemma close_f_open_f :
  forall t, close_f_open_f_pred t.
Proof.
  close_X_open_X_induction Tau_F_ind_mutual;
  close_X_open_X_proof.
Qed.

Lemma close_tau_open_tau:
  forall t, close_tau_open_tau_pred t.
Proof.
  close_X_open_X_induction Tau_Tau_ind_mutual;
  close_X_open_X_proof.
Qed.

Lemma close_open :
  forall alpha t n, 
  alpha \notin TTM.fv t -> 
  close_rec n alpha (open_rec n (ftvar alpha) t) = t.
Proof.
  destruct t; simpl; intros; fequals~.
  applys~ close_st_open_st.
  applys~ close_e_open_e.
  applys~ close_f_open_f.
Qed.

(** The other direction is much harder; First, we first need
    to establish the injectivity of [open_var] *)

Lemma open_rec_st_inj :
  forall alpha n t1 t2, 
    alpha \notin (fv_st t1) ->
    alpha \notin (fv_st t2) -> 
    open_rec_st n (ftvar alpha) t1 = open_rec_st n (ftvar alpha) t2 ->
    (t1 = t2).
Proof.
  introv Fr1 Fr2 Eq.
  rewrite~ <- (@close_st_open_st t1 alpha n).
  rewrite~ <- (@close_st_open_st t2 alpha n).
  fequals~.
Qed.

Lemma open_rec_e_inj :
  forall alpha n t1 t2, 
    alpha \notin (fv_e t1) ->
    alpha \notin (fv_e t2) -> 
    open_rec_e n (ftvar alpha) t1 = open_rec_e n (ftvar alpha) t2 ->
    (t1 = t2).
Proof.
  introv Fr1 Fr2 Eq.
  rewrite~ <- (@close_e_open_e t1 alpha n).
  rewrite~ <- (@close_e_open_e t2 alpha n).
  fequals~.
Qed.

Lemma open_rec_f_inj :
  forall alpha n t1 t2, 
    alpha \notin (fv_f t1) ->
    alpha \notin (fv_f t2) -> 
    open_rec_f n (ftvar alpha) t1 = open_rec_f n (ftvar alpha) t2 ->
    (t1 = t2).
Proof.
  introv Fr1 Fr2 Eq.
  rewrite~ <- (@close_f_open_f t1 alpha n).
  rewrite~ <- (@close_f_open_f t2 alpha n).
  fequals~.
Qed.

Lemma open_rec_inj :
  forall alpha n t1 t2, 
    alpha \notin (fv t1) ->
    alpha \notin (fv t2) -> 
    open_rec n (ftvar alpha) t1 = open_rec n (ftvar alpha) t2 ->
    (t1 = t2).
Proof.
  introv Fr1 Fr2 Eq.
  rewrite~ <- (@close_open alpha t1 n).
  rewrite~ <- (@close_open alpha t2 n).
  fequals~.
Qed.

(** We also need one (tricky) auxiliary lemma to handle the binder case *)

Lemma open_rec_v_close_rec_v_on_open_rec_v:
  forall alpha beta gamma t i j,
    i <> j ->
    beta <> alpha ->
    beta \notin (fv_v t) ->
    open_rec_v i (ftvar beta) (open_rec_v j (ftvar gamma) (close_rec_v j alpha t))
  = open_rec_v j (ftvar gamma) (close_rec_v j alpha (open_rec_v i (ftvar beta) t)).
Proof.
  induction t; try solve[simpl; intros; try solve [ fequals~ ]];
  intros;
  do 4 (simpl; try case_nat~; try case_nat~; try case_var~).
Qed.

Function open_rec_e_close_rec_e_on_open_rec_e_pred (t : E) :=
  forall alpha beta gamma i j,
    i <> j ->
    beta <> alpha ->
    beta \notin (fv_e t) ->
    open_rec_e i (ftvar beta) (open_rec_e j (ftvar gamma) (close_rec_e j alpha t))
  = open_rec_e j (ftvar gamma) (close_rec_e j alpha (open_rec_e i (ftvar beta) t)).
Hint Unfold open_rec_e_close_rec_e_on_open_rec_e_pred.

Function open_rec_st_close_rec_st_on_open_rec_st_pred (t : St) :=
  forall alpha beta gamma i j,
    i <> j ->
    beta <> alpha ->
    beta \notin (fv_st t) ->
    open_rec_st i (ftvar beta) (open_rec_st j (ftvar gamma) (close_rec_st j alpha t))
  = open_rec_st j (ftvar gamma) (close_rec_st j alpha (open_rec_st i (ftvar beta) t)).
Hint Unfold open_rec_st_close_rec_st_on_open_rec_st_pred.

Function open_rec_f_close_rec_f_on_open_rec_f_pred (t : F) :=
  forall alpha beta gamma i j,
    i <> j ->
    beta <> alpha ->
    beta \notin (fv_f t) ->
    open_rec_f i (ftvar beta) (open_rec_f j (ftvar gamma) (close_rec_f j alpha t))
  = open_rec_f j (ftvar gamma) (close_rec_f j alpha (open_rec_f i (ftvar beta) t)).
Hint Unfold open_rec_f_close_rec_f_on_open_rec_f_pred.

Ltac open_rec_X_close_rec_X_on_open_rec_X_induction MIS :=
  apply (MIS
           open_rec_st_close_rec_st_on_open_rec_st_pred
           open_rec_e_close_rec_e_on_open_rec_e_pred
           open_rec_f_close_rec_f_on_open_rec_f_pred).
  
Ltac open_rec_X_close_rec_X_on_open_rec_X_proof :=
  autounfold in *;
  try solve[simpl; intros; try solve [ fequals~ ]];
  simpl;
  intros;
  fequals~;
  lets M: TP.open_close_var_on_open_var;
  auto.

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
  forall alpha beta gamma t i j,
    i <> j ->
    beta <> alpha ->
    beta \notin (fv t) ->
    open_rec i (ftvar beta) (open_rec j (ftvar gamma) (close_rec j alpha t))
  = open_rec j (ftvar gamma) (close_rec j alpha (open_rec i (ftvar beta) t)).
Proof.
  destruct t; simpl; intros; fequals~.
  applys~ open_rec_st_close_rec_st_on_open_rec_st.
  applys~ open_rec_e_close_rec_e_on_open_rec_e.
  applys~ open_rec_f_close_rec_f_on_open_rec_f.
Qed.

(** Now we can prove that [open_var] after [close_var] is the identity *)

Lemma open_rec_v_close_rec_v: 
  forall alpha t n, 
    lc_v t -> 
    open_rec_v n (ftvar alpha) (close_rec_v n alpha t)  = t.
Proof.
  introv T. 
  induction T. 
  auto.
Qed.

(* Mutual induction again. *)

Function open_rec_st_close_rec_st_pred (t : St) (_ : lc_st t):=
  forall alpha n,
    open_rec_st n (ftvar alpha) (close_rec_st n alpha t)  = t.
Hint Unfold open_rec_st_close_rec_st_pred.

Function open_rec_e_close_rec_e_pred (t : E) (_ : lc_e t):=
  forall alpha n, 
    open_rec_e n (ftvar alpha) (close_rec_e n alpha t)  = t.
Hint Unfold open_rec_e_close_rec_e_pred.

Function open_rec_f_close_rec_f_pred (t : F) (_ : lc_f t) :=
  forall alpha n, 
    open_rec_f n (ftvar alpha) (close_rec_f n alpha t)  = t.
Hint Unfold open_rec_f_close_rec_f_pred.

Ltac open_rec_X_close_rec_X_induction MIS :=
  apply (MIS 
           open_rec_st_close_rec_st_pred
           open_rec_e_close_rec_e_pred
           open_rec_f_close_rec_f_pred).

(* This interesting in that I'm hinting some very general proof tactics.
  It could be dangerous. *)

Ltac invert_lc_btvar :=
  match goal with
    | H : T.lc (btvar _) |- _  => inversion H
  end.

Hint Extern 1 (T.lc (btvar _)) => invert_lc_btvar.

Ltac inversion_on_lc :=
  match goal with
    | H : T.lc (_ _)    |- _ => inversions~ H
    | H : T.lc (_ _ _)    |- _ => inversions~ H
    | H : TTM.lc (_ _)    |- _ => inversions~ H
    | H : TTM.lc (_ _ _)    |- _ => inversions~ H
end.

Hint Extern 1 (T.lc (_ _)) => inversion_on_lc.
Hint Extern 1 (T.lc (_ _ _)) => inversion_on_lc.

Ltac open_rec_X_close_rec_X_proof t :=
  autounfold in *;
  lets: open_rec_v_close_rec_v;
  lets~ M: TP.open_close_var;
  try solve[simpl; intros; fequals~];
  simpl;
  intros;
  fequals~;
  try induction t; simpl; intros; fequals~;
  try solve[case_var~; simpl; case_nat~].

Lemma open_rec_st_close_rec_st: 
  forall t,
     lc_st t ->
     forall alpha, 
       forall n,
         open_rec_st n (ftvar alpha) (close_rec_st n alpha t)  = t.
Proof.
  open_rec_X_close_rec_X_induction lc_st_ind_mutual;
  open_rec_X_close_rec_X_proof t.
Qed.

Lemma open_rec_e_close_rec_e: 
  forall t,
     lc_e t ->
     forall alpha, 
       forall n,
         open_rec_e n (ftvar alpha) (close_rec_e n alpha t)  = t.
Proof.
  open_rec_X_close_rec_X_induction lc_e_ind_mutual;
  open_rec_X_close_rec_X_proof t.
Qed.

Lemma open_rec_f_close_rec_f: 
  forall t,
     lc_f t ->
     forall alpha, 
       forall n,
         open_rec_f n (ftvar alpha) (close_rec_f n alpha t)  = t.
Proof.
  open_rec_X_close_rec_X_induction lc_f_ind_mutual;
  open_rec_X_close_rec_X_proof t.
Qed.

Lemma open_rec_close_rec: 
  forall t,
     lc t ->
     forall alpha, 
       forall n,
         open_rec n (ftvar alpha) (close_rec n alpha t)  = t.
Proof.
  destruct t; intros; simpl; fequals~; inversions H.
  apply~ open_rec_st_close_rec_st.
  apply~ open_rec_e_close_rec_e.
  apply~ open_rec_f_close_rec_f.  
Qed.

(** As a bonus, we get the injectivity of [close_var] *)

Lemma close_on_var_inj :
  forall alpha t1 t2, 
    lc t1 ->
    lc t2 ->
    close alpha t1 = close alpha t2 ->
    (t1 = t2).
Proof.
  unfold close.
  introv T1 T2 Eq.
  rewrite~ <- (@open_rec_close_rec t1 T1 alpha 0).
  rewrite~ <- (@open_rec_close_rec t2 T2 alpha 0).
  fequals~.
Qed.

(* ********************************************************************** *)
(** Interaction of [fv] with [open_var] and [close_var] *)

(** Opening with [u] adds [fv u] to the set of free variables *)

Lemma fv_v_open :
  forall (t : V) (u : var) (n: nat),
    fv_v (open_rec_v n (ftvar u) t) \c  fv_v t \u \{u}.
Proof.
  intros.
  destruct t; simpl; try case_nat; simpl; fset.
Qed.

Function fv_st_open_pred (t : St) :=
  forall (u : var) (n : nat),
    fv_st (open_rec_st n (ftvar u) t) \c fv_st t \u \{u}.
Hint Unfold fv_st_open_pred.

Function fv_e_open_pred (t : E) :=
  forall (u : var) (n : nat),
    fv_e (open_rec_e n (ftvar u) t) \c fv_e t \u \{u}.
Hint Unfold fv_e_open_pred.

Function fv_f_open_pred (t : F) :=
  forall (u : var) (n : nat),
    fv_f (open_rec_f n (ftvar u) t) \c fv_f t \u \{u}.
Hint Unfold fv_f_open_pred.

Ltac fv_X_open_proof t t0 u:= 
  autounfold in *;
  lets I: fv_v_open;
  try solve[intros l; simpl; try case_nat; try fset];
  simpl;
  intros;
  lets: (TP.fv_open t (ftvar u));
  try lets: (TP.fv_open t0 (ftvar u));
  lets: (TP.fv_open t (ftvar u));
  fset.

Ltac fv_X_open_induction T :=
  apply (T
           fv_st_open_pred
           fv_e_open_pred
           fv_f_open_pred).
  
Lemma fv_st_open:
  forall t u n,
    fv_st (open_rec_st n (ftvar u) t) \c fv_st t \u \{u}.
Proof.
  fv_X_open_induction St_ind_mutual;
  fv_X_open_proof t t0 u.
Qed.

Lemma fv_e_open :
  forall t u n, 
    fv_e (open_rec_e n (ftvar u) t) \c fv_e t \u \{u}.
Proof.
  fv_X_open_induction E_ind_mutual;
  fv_X_open_proof t t0 u.
Qed.

Lemma fv_f_open :
  forall t u n, 
    fv_f (open_rec_f n (ftvar u) t) \c fv_f t \u \{u}.
Proof.
  fv_X_open_induction F_ind_mutual;
  fv_X_open_proof t t0 u.
Qed.

Lemma fv_open : forall t u,
  fv (open (ftvar u) t) \c fv t \u \{u}.
Proof.
  destruct t; intros.
  apply fv_st_open.
  apply fv_e_open.
  apply fv_f_open.
Qed.

(** In particular, opening with variable [x] adds [x] to the set 
    of free variables *)

Lemma open_var_fv : forall alpha t,
  fv (open_rec 0 (ftvar alpha) t) \c (fv t \u \{alpha}).
Proof.
  intros.
  apply fv_open. 
Qed.

(** Closing w.r.t variable [x] removes [x] from the set of free variables *)

Lemma close_tv_v_fv : forall alpha t n,
  fv_v (close_rec_v n alpha t) \c (fv_v t \- \{alpha}).
Proof.
  intros.
  destruct t; simpl; fset.
Qed.

Function close_tv_st_fv_pred (t : St) :=
  forall alpha n,
    fv_st (close_rec_st n alpha t) \c (fv_st t \- \{alpha}).
Hint Unfold close_tv_st_fv_pred.

Function close_tv_e_fv_pred (t : E) :=
  forall alpha n,
    fv_e (close_rec_e n alpha t) \c (fv_e t \- \{alpha}).
Hint Unfold close_tv_e_fv_pred.

Function close_tv_f_fv_pred (t : F) :=
  forall alpha n,
    fv_f (close_rec_f n alpha t) \c (fv_f t \- \{alpha}).
Hint Unfold close_tv_f_fv_pred.

Ltac close_tv_X_fv_induction T :=
  apply (T
           close_tv_st_fv_pred
           close_tv_e_fv_pred
           close_tv_f_fv_pred).

Ltac close_tv_X_fv_proof :=
  lets: close_tv_v_fv;
  lets: TP.close_fv;
  autounfold in *; simpl; intros; fset.

Lemma close_tv_st_fv :
  forall t alpha n,
    fv_st (close_rec_st n alpha t) \c (fv_st t \- \{alpha}).
Proof.
  close_tv_X_fv_induction St_ind_mutual;
  close_tv_X_fv_proof.
Qed.

Lemma close_tv_e_fv :
  forall t alpha n,
    fv_e (close_rec_e n alpha t) \c (fv_e t \- \{alpha}).
Proof.
  close_tv_X_fv_induction E_ind_mutual;
  close_tv_X_fv_proof.
Qed.

Lemma close_tv_f_fv :
  forall t alpha n,
    fv_f (close_rec_f n alpha t) \c (fv_f t \- \{alpha}).
Proof.
  close_tv_X_fv_induction F_ind_mutual;
  close_tv_X_fv_proof.
Qed.

Lemma close_tv_fv : forall alpha t,
  fv (close_rec 0 alpha t) \c (fv t \- \{alpha}).
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

Lemma open_rec_v_lc_ind:
  forall t j v i u,
    i <> j ->
    open_rec_v i u (open_rec_v j v t) = open_rec_v j v t ->
    open_rec_v i u t = t.
Proof.
  induction t; introv Nq Eq;
  simpls; inversions~ Eq; fequals*.
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
  lets: TP.open_rec_lc_ind;
  intros;
  simpls;
  try inversion_on_equated_constructors;
  fequals;
  intuition eauto.

Lemma open_rec_st_lc_ind:
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

Lemma open_rec_lc_ind: 
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

Ltac open_rec_X_lc_t_X_proof alpha := 
  lets: open_rec_v_lc_t;
  lets: TP.open_rec_lc;
  autounfold in *;
  intros; simpl; fequals~.

Lemma open_rec_st_lc_t: 
  forall t, 
    lc_st t -> 
    forall u,
     forall n,
       open_rec_st n u t = t.
Proof.
  open_rec_X_lc_t_X_induction lc_st_ind_mutual;
  open_rec_X_lc_t_X_proof alpha.
Qed.

Lemma open_rec_e_lc_t : 
  forall t, 
    lc_e t -> 
    forall u,
     forall n,
       open_rec_e n u t = t.
Proof.
  open_rec_X_lc_t_X_induction lc_e_ind_mutual;
  open_rec_X_lc_t_X_proof alpha.
Qed.

Lemma open_rec_f_lc_t : 
  forall t, 
    lc_f t -> 
    forall u,
     forall n,
       open_rec_f n u t = t.
Proof.
  open_rec_X_lc_t_X_induction lc_f_ind_mutual;
  open_rec_X_lc_t_X_proof alpha.
Qed.

Lemma open_rec_lc_t : 
  forall t, 
    lc t -> 
    forall u,
     forall n,
       open_rec n u t = t.
Proof.
  lets L1: open_rec_st_lc_t.
  lets L2: open_rec_e_lc_t.  
  lets L3: open_rec_f_lc_t.  
  destruct t; intros; simpl; fequals~; inversions~ H.
Qed.

(* Restart here. *)


Function subst_st_open_pred (t : St) := 
  forall alpha u v n, 
    T.lc u ->
    subst_st u alpha (open_rec_st n v t) = 
    open_rec_st n (T.subst u alpha v) (subst_st u alpha t).
Hint Unfold subst_st_open_pred.

Function subst_e_open_pred (t : E) := 
  forall alpha u v n, 
    T.lc u ->
    subst_e u alpha (open_rec_e n v t) = 
    open_rec_e n (T.subst u alpha v) (subst_e u alpha t).
Hint Unfold subst_e_open_pred.

Function subst_f_open_pred (t : F) := 
  forall alpha u v n, 
    T.lc u ->
    subst_f u alpha (open_rec_f n v t) = 
    open_rec_f n (T.subst u alpha v) (subst_f u alpha t).
Hint Unfold subst_f_open_pred.

Ltac subst_X_open_induction T :=
  apply (T
           subst_st_open_pred
           subst_e_open_pred
           subst_f_open_pred).

Ltac subst_X_open_proof :=
  autounfold in *;
  lets: TP.subst_open_rec;
  intros; simpl; fequals~.

Lemma subst_st_open:
  forall t, subst_st_open_pred t.
Proof.
  subst_X_open_induction St_ind_mutual;
  subst_X_open_proof.
Qed.

Lemma subst_e_open:
  forall t, subst_e_open_pred t.
Proof.
  subst_X_open_induction E_ind_mutual;
  subst_X_open_proof.
Qed.

Lemma subst_f_open:
  forall t, subst_f_open_pred t.
Proof.
  subst_X_open_induction F_ind_mutual;
  subst_X_open_proof.
Qed.

Lemma subst_open:
  forall (t: Term) (alpha : var) (u : Tau) (v : Tau)  n, 
    T.lc u ->
    subst u alpha (open_rec n v t) = 
    open_rec n (T.subst u alpha v) (subst u alpha t).
Proof.
  lets: subst_st_open;
  lets: subst_e_open;
  lets: subst_f_open;
  autounfold in *;
  destruct t;
  simpl;
  intros;
  fequals~.
Qed.

(** In particular, we can distribute [subst] on [open_var] *)

Lemma subst_open_var:
  forall alpha beta u t, 
    alpha <> beta ->
    T.lc u -> 
    subst u alpha (open_rec 0 (ftvar beta) t) =
    open_rec 0 (ftvar beta) (subst u alpha t).
Proof.
  introv N U.
  rewrite~ subst_open.
  fequals.
  simpl.
  case_var~.
Qed.


(** For the distributivity of [subst] on [close_var],
    one simple intermediate lemmas is required to 
    say that closing on a fresh name is the identity *)

Lemma close_rec_v_fresh :
  forall alpha t k,
  alpha \notin fv_v t -> close_rec_v k alpha t = t.
Proof.
  destruct t; intros; simpls*.
Qed.

Function close_rec_st_fresh_pred (t : St) :=
  forall alpha k,
    alpha \notin fv_st t -> close_rec_st k alpha t = t.
Hint Unfold close_rec_st_fresh_pred.
  
Function close_rec_e_fresh_pred (t : E) :=
  forall alpha k,
    alpha \notin fv_e t -> close_rec_e k alpha t = t.
Hint Unfold close_rec_e_fresh_pred.

Function close_rec_f_fresh_pred (t : F) :=
  forall alpha k,
    alpha \notin fv_f t -> close_rec_f k alpha t = t.
Hint Unfold close_rec_f_fresh_pred.

Ltac close_rec_X_fresh_induction T :=
  apply (T
           close_rec_st_fresh_pred
           close_rec_e_fresh_pred
           close_rec_f_fresh_pred).

Ltac close_rec_X_fresh_proof :=
  lets: close_rec_v_fresh;
  lets: TP.close_rec_fresh;
  autounfold in *;
  simpl;
  intros;
  fequals~.

Lemma close_rec_st_fresh :
  forall t alpha k,
    alpha \notin fv_st t -> close_rec_st k alpha t = t.
Proof.
  close_rec_X_fresh_induction St_ind_mutual;
  close_rec_X_fresh_proof.
Qed.

Lemma close_rec_e_fresh :
  forall t alpha k,
    alpha \notin fv_e t -> close_rec_e k alpha t = t.
Proof.
  close_rec_X_fresh_induction E_ind_mutual;
  close_rec_X_fresh_proof.
Qed.

Lemma close_rec_f_fresh :
  forall t alpha k,
    alpha \notin fv_f t -> close_rec_f k alpha t = t.
Proof.
  close_rec_X_fresh_induction F_ind_mutual;
  close_rec_X_fresh_proof.
Qed.

Lemma close_rec_fresh:
  forall alpha t k,
    alpha \notin fv t -> close_rec k alpha t = t.
Proof.
  lets: close_rec_st_fresh.
  lets: close_rec_e_fresh.
  lets: close_rec_f_fresh.
  destruct t; simpl; intros; fequals~.
Qed.

(** Distributivity of [subst] on [close_var] *)

Function subst_st_close_rec_st_pred (t : St) :=
  forall (alpha beta : var) (u : Tau),
    alpha <> beta ->
    beta \notin T.fv u ->
    forall n, 
      subst_st u alpha (close_rec_st n beta t) = 
      close_rec_st n beta (subst_st u alpha t).
Hint Unfold subst_st_close_rec_st_pred.

Function subst_e_close_rec_e_pred (t : E) :=
  forall alpha beta u,
    alpha <> beta ->
    beta \notin T.fv u ->
    forall n,
      subst_e u alpha (close_rec_e n beta t) =
      close_rec_e n beta (subst_e u alpha t).
Hint Unfold subst_e_close_rec_e_pred.

Function subst_f_close_rec_f_pred (t : F) :=
  forall alpha beta u,
    alpha <> beta ->
    beta \notin T.fv u ->
    forall n, 
      subst_f u alpha (close_rec_f n beta t) =
      close_rec_f n beta (subst_f u alpha t).         
Hint Unfold subst_f_close_rec_f_pred.

Ltac subst_X_close_rec_X_induction T :=
  apply (T
           subst_st_close_rec_st_pred
           subst_e_close_rec_e_pred 
           subst_f_close_rec_f_pred).

Ltac subst_X_close_rec_X_proof :=
  lets: TP.subst_close_rec;
  autounfold in *;
  simpl;
  intros;
  fequals~.

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

Lemma subst_v_close_rec:
  forall t alpha beta u,
    alpha <> beta ->
    beta \notin T.fv u ->
    forall n, 
      subst u alpha (close_rec n beta t) = close_rec n beta (subst u alpha t).
Proof.
  lets: subst_st_close_rec_st;
  lets: subst_e_close_rec_e;
  lets: subst_f_close_rec_f;
  autounfold in *;
  destruct t; simpl; intros; fequals~.
Qed.

(** Substitution for a fresh name is the identity *)

Function subst_st_fresh_pred (t : St) :=
  forall alpha u, 
    alpha \notin fv_st t -> subst_st u alpha t = t.
Hint Unfold subst_st_fresh_pred.

Function subst_e_fresh_pred (t : E) :=
  forall alpha u, 
    alpha \notin fv_e t -> subst_e u alpha t = t.
Hint Unfold subst_e_fresh_pred.

Function subst_f_fresh_pred (t : F) :=  
forall alpha u, 
  alpha \notin fv_f t -> subst_f u alpha t = t.
Hint Unfold subst_f_fresh_pred.

Ltac subst_X_fresh_induction T :=
  apply(T 
          subst_st_fresh_pred
          subst_e_fresh_pred
          subst_f_fresh_pred).

Ltac subst_X_fresh_proof :=
  lets: subst_fresh;
  lets: TP.subst_fresh;
  autounfold in *;
  simpl;
  intros;
  fequals~.

Lemma subst_st_fresh:
  forall t alpha u, 
  alpha \notin fv_st t -> subst_st u alpha t = t.
Proof.
  subst_X_fresh_induction St_ind_mutual;
  subst_X_fresh_proof.
Qed.

Lemma subst_e_fresh: 
forall t alpha u, 
  alpha \notin fv_e t -> subst_e u alpha t = t.
Proof.
  subst_X_fresh_induction E_ind_mutual;
  subst_X_fresh_proof.
Qed.

Lemma subst_f_fresh:
  forall t alpha u, 
  alpha \notin fv_f t -> subst_f u alpha t = t.
Proof.
  subst_X_fresh_induction F_ind_mutual;
  subst_X_fresh_proof.
Qed.

Lemma subst_v_fresh : forall alpha t u, 
  alpha \notin fv t -> subst u alpha t = t.
Proof.
  lets: subst_st_fresh.
  lets: subst_e_fresh.
  lets: subst_f_fresh.
  destruct t; simpl; intros; fequals~.
Qed.

(** Substitution can be introduced to decompose an opening *)

(** An alternative, longer proof, but with fewer hypotheses *)

Function subst_st_intro_alternative_pred (t : St) :=
 forall alpha  u n, 
  alpha \notin (fv_st t) -> 
  open_rec_st n u t = subst_st u alpha (open_rec_st n (ftvar alpha) t).
Hint Unfold subst_st_intro_alternative_pred.

Function subst_e_intro_alternative_pred (t : E) :=
 forall alpha  u n, 
  alpha \notin (fv_e t) -> 
  open_rec_e n u t = subst_e u alpha (open_rec_e n (ftvar alpha) t).
Hint Unfold subst_e_intro_alternative_pred.

Function subst_f_intro_alternative_pred (t : F) :=
 forall alpha  u n, 
  alpha \notin (fv_f t) -> 
  open_rec_f n u t = subst_f u alpha (open_rec_f n (ftvar alpha) t).
Hint Unfold subst_f_intro_alternative_pred.

Ltac subst_X_intro_alternative_induction T :=
  apply (T
           subst_st_intro_alternative_pred
           subst_e_intro_alternative_pred
           subst_f_intro_alternative_pred).

Ltac subst_X_intro_alternative_proof := 
  autounfold in *;
  lets: TP.subst_intro_alternative;
  simpl;
  intros;
  fequals~.

Lemma subst_st_intro_alternative:
  forall t, subst_st_intro_alternative_pred t.
Proof.
  subst_X_intro_alternative_induction St_ind_mutual;
  subst_X_intro_alternative_proof.  
Qed.

Lemma subst_e_intro_alternative:
  forall t, subst_e_intro_alternative_pred t.
Proof.
  subst_X_intro_alternative_induction E_ind_mutual;
  subst_X_intro_alternative_proof.  
Qed.

Lemma subst_f_intro_alternative:
  forall t, subst_f_intro_alternative_pred t.
Proof.
  subst_X_intro_alternative_induction F_ind_mutual;
  subst_X_intro_alternative_proof.  
Qed.

Lemma subst_intro_alternative : forall alpha t u n, 
  alpha \notin (fv t) -> 
  open_rec n u t = subst u alpha (open_rec n (ftvar alpha) t).
Proof.
  destruct t;
  lets: subst_st_intro_alternative;
  lets: subst_e_intro_alternative;
  lets: subst_f_intro_alternative;
  autounfold in *;
  simpl; intros; fequals~.
Qed.

(** Substitution can be introduced to decompose a variable
    closing in terms of another one using a different name *)

Function close_st_rename_pred (t : St) := 
  forall alpha beta n,
  alpha \notin fv_st t ->
  close_rec_st n beta t =
  close_rec_st n alpha (subst_st (ftvar alpha) beta t).
Hint Unfold close_st_rename_pred.

Function close_e_rename_pred (t : E) := 
  forall alpha beta n,
  alpha \notin fv_e t ->
  close_rec_e n beta t =
  close_rec_e n alpha (subst_e (ftvar alpha) beta t).
Hint Unfold close_e_rename_pred.

Function close_f_rename_pred (t : F) := 
  forall alpha beta n,
  alpha \notin fv_f t ->
  close_rec_f n beta t =
  close_rec_f n alpha (subst_f (ftvar alpha) beta t).
Hint Unfold close_f_rename_pred.

Ltac close_X_rename_induction T :=
  apply (T 
           close_st_rename_pred
           close_e_rename_pred
           close_f_rename_pred).

Ltac close_X_rename_proof :=
  lets M: TP.close_rename;
  autounfold in *;
  simpl;
  intros;
  fequals~.

Lemma close_st_rename: 
  forall t,  close_st_rename_pred t.
Proof.
  close_X_rename_induction St_ind_mutual;
  close_X_rename_proof.
Qed.

Lemma close_e_rename: 
  forall t,  close_e_rename_pred t.
Proof.
  close_X_rename_induction E_ind_mutual;
  close_X_rename_proof.
Qed.

Lemma close_f_rename: 
  forall t,  close_f_rename_pred t.
Proof.
  close_X_rename_induction F_ind_mutual;
  close_X_rename_proof.
Qed.

Lemma close_rename : forall t alpha beta n,
  alpha \notin fv t ->
  close_rec n beta t =
  close_rec n alpha (subst (ftvar alpha) beta t).
Proof.
  lets: close_st_rename;
  lets: close_e_rename;
  lets: close_f_rename;  
  autounfold in *;
  destruct t; simpl; intros; fequals~.
Qed.

(* ********************************************************************** *)
(** Preservation of local closure through substitution and opening *)

(** Substitution of a locally closed terms into another one produces
    a locally closed term *)

Function subst_st_lc_pred (t : St) (_ : lc_st t) := 
  forall alpha u,
    T.lc u -> lc_st (subst_st u alpha t).
Hint Unfold subst_st_lc_pred.

Function subst_e_lc_pred (t : E) (_ : lc_e t) := 
  forall alpha u,
    T.lc u -> lc_e (subst_e u alpha t).
Hint Unfold subst_e_lc_pred.

Function subst_f_lc_pred (t : F) (_ : lc_f t) := 
  forall alpha u,
    T.lc u -> lc_f (subst_f u alpha t).
Hint Unfold subst_f_lc_pred.

Ltac subst_X_lc_induction T :=
  apply (T
           subst_st_lc_pred
           subst_e_lc_pred
           subst_f_lc_pred).

Ltac subst_X_lc_proof :=
  autounfold in *;
  simpl;
  intros;
  fequals~;
  lets: TP.subst_lc;
  constructor~.

Lemma subst_st_lc :
  forall t,
    lc_st t ->
    forall alpha u,
    T.lc u -> lc_st (subst_st u alpha t).
Proof.
  subst_X_lc_induction lc_st_ind_mutual;
  subst_X_lc_proof.
Qed.

Lemma subst_e_lc :
  forall t,
    lc_e t ->
    forall alpha u,
    T.lc u -> lc_e (subst_e u alpha t).
Proof.
  subst_X_lc_induction lc_e_ind_mutual;
  subst_X_lc_proof.
Qed.

Lemma subst_f_lc :
  forall t,
    lc_f t ->
    forall alpha u,
    T.lc u -> lc_f (subst_f u alpha t).
Proof.
  subst_X_lc_induction lc_f_ind_mutual;
  subst_X_lc_proof.
Qed.

Lemma subst_lc :
  forall alpha u t,
    T.lc u -> lc t -> lc (subst u alpha t).
Proof.
  lets: subst_st_lc;
  lets: subst_e_lc;
  lets: subst_f_lc;  
  simpl;
  intros;
  destruct t;
  inversion_on_lc;
  constructor~.
Qed.

(** Substitution of a locally closed terms into a body one produces
    another body *)


(* We need a lemma that Arthur only proved for his alternate inductive lc. *)
Lemma lc_open_var_rec_v:
  forall t alpha,
    lc_v t -> lc_v (open_rec_v 0 (ftvar alpha) t).
Proof.
  induction t; auto.
Qed.  

Function lc_open_var_rec_st_pred (t : St) :=
  forall alpha,
    lc_st t -> lc_st (open_rec_st 0 (ftvar alpha) t).
Hint Unfold lc_open_var_rec_st_pred.

Function lc_open_var_rec_e_pred (t : E) :=
  forall alpha,
    lc_e t -> lc_e (open_rec_e 0 (ftvar alpha) t).
Hint Unfold lc_open_var_rec_e_pred.

Function lc_open_var_rec_f_pred (t : F) :=
  forall alpha,
    lc_f t -> lc_f (open_rec_f 0 (ftvar alpha) t).
Hint Unfold lc_open_var_rec_f_pred.

Ltac lc_open_var_rec_X_induction T :=
  apply (T
           lc_open_var_rec_st_pred
           lc_open_var_rec_e_pred
           lc_open_var_rec_f_pred).

Ltac inversion_on_lc_term :=
  match goal with
    | H : TTM.lc_st (_ _)    |- _ => inversions~ H
    | H : TTM.lc_st (_ _ _)    |- _ => inversions~ H
    | H : TTM.lc_e (_ _)    |- _ => inversions~ H
    | H : TTM.lc_e (_ _ _)    |- _ => inversions~ H
    | H : TTM.lc_f (_ _)    |- _ => inversions~ H
    | H : TTM.lc_f (_ _ _)    |- _ => inversions~ H
end.  

Ltac lc_open_var_rec_X_proof :=
  lets: lc_open_var_rec_v;
  autounfold in *;
  simpl;
  intros;
  inversion_on_lc_term;
  constructor~;
  applys~ TP.lc_open_var_rec.

Lemma lc_open_var_rec_st:
  forall t, lc_open_var_rec_st_pred t.
Proof.  
  lc_open_var_rec_X_induction St_ind_mutual;
  lc_open_var_rec_X_proof.
Qed.

Lemma lc_open_var_rec_e:
  forall t, lc_open_var_rec_e_pred t.
Proof.  
  lc_open_var_rec_X_induction E_ind_mutual;
  lc_open_var_rec_X_proof.
Qed.

Lemma lc_open_var_rec_f:
  forall t, lc_open_var_rec_f_pred t.
Proof.  
  lc_open_var_rec_X_induction F_ind_mutual;
  lc_open_var_rec_X_proof.
Qed.

Lemma lc_open_var_rec:
  forall alpha t,
    lc t -> lc (open_rec 0 (ftvar alpha) t).
Proof.  
  intros.
  lets: lc_open_var_rec_st;
  lets: lc_open_var_rec_e;
  lets: lc_open_var_rec_f;
  destruct t;
  autounfold in *;
  inversions~ H;
  constructor~.
Qed.  

Lemma subst_body :
  forall alpha t u,
    T.lc u -> body t -> body (subst u alpha t).
Proof.
  introv U [L H].
  exists_fresh.
  rewrite~ <- subst_open_var.
  apply~ subst_lc.
Qed.

(** Opening of a body with a locally closed terms produces a 
    locally closed term *)

Lemma open_rec_preserves_lc : forall t u,
  body t -> T.lc u -> lc (open_rec 0 u t).
Proof.
  introv [L H] U.
  pick_fresh alpha.
  rewrite~ (@subst_intro_alternative alpha).
  apply~ subst_lc. 
Qed.

(* ********************************************************************** *)
(** Properties of [body] *)

(** An abstraction is locally closed iff it satifies the predicate [body] *) 

(* This is a weakened version as body does not imply lc t0 and lc t1. *)
Lemma lc_dfun_iff_body : 
  forall t0 t1 s,
    T.lc t0 ->
    T.lc t1 ->
    lc_st s ->
    lc (term_f (dfun t0 t1 s)) <-> body (term_st s).
Proof.
  intros.
  iff A.
  inversions~ A.
  inversions~ H3.
  unfold body.
  exists ((T.fv t0 \u T.fv t1) \u TM.fv_st s \u (fv_st s)).
  intros.
  constructor.
  applys~ lc_open_var_rec_st.

  unfold body in A.
  simpl in A.
  constructor.
  constructor~.
Qed.


Lemma lc_open_iff_body: 
  forall e s,
    lc_e e ->
    lc_st s ->
    lc_st (openx e s) <-> body (term_st s).
Proof. 
  intros.
  iff A.
  inversions~ A.
  unfold body.
  exists ((fv_e e) \u (fv_st s)).
  intros.
  constructor.
  applys~ lc_open_var_rec_st.

  unfold body in A.
  simpl in A.
  constructor.
  assumption.
  assumption.
Qed.


Lemma lc_openstar_iff_body : 
  forall e s,
    lc_e e ->
    lc_st s ->
    lc_st (openstar e s) <-> body (term_st s).
Proof. 
  intros.
  iff A.
  inversions~ A.
  unfold body.
  exists ((fv_e e) \u (fv_st s)).
  intros.
  constructor.
  applys~ lc_open_var_rec_st.

  unfold body in A.
  simpl in A.
  constructor.
  assumption.
  assumption.
Qed.


Lemma lc_letx_iff_body : 
  forall e s,
    lc_e e ->
    lc_st s ->
    lc_st (letx e s) <-> body (term_st s).
Proof. 
  intros.
  iff A.
  inversions~ A.
  unfold body.
  exists ((fv_e e) \u (fv_st s)).
  intros.
  constructor.
  applys~ lc_open_var_rec_st.

  unfold body in A.
  simpl in A.
  constructor.
  assumption.
  assumption.
Qed.

(* ====================================================================== *)
(** ** An induction principle for locally closed terms *)

(** Interaction of [size] with [open_var] *)

Lemma size_open_rec_v:
  forall t alpha n, 
    TM.size_v (open_rec_v n (ftvar alpha) t) = TM.size_v t.
Proof.
  intros.
  induction t; auto.
Qed.

Function size_open_rec_st_pred (t : St) :=
  forall alpha n, 
    TM.size_st (open_rec_st n (ftvar alpha) t) = TM.size_st t.
Hint Unfold size_open_rec_st_pred.

Function size_open_rec_e_pred (t : E) :=
  forall alpha n,
    TM.size_e (open_rec_e n (ftvar alpha) t) = TM.size_e t.
Hint Unfold size_open_rec_e_pred.

Function size_open_rec_f_pred (t : F) :=
  forall alpha n, 
    TM.size_f (open_rec_f n (ftvar alpha) t) = TM.size_f t.
Hint Unfold size_open_rec_f_pred.

Ltac size_open_rec_X_induction T :=
  apply (T 
           size_open_rec_st_pred
           size_open_rec_e_pred
           size_open_rec_f_pred).

Ltac size_open_rec_X_proof :=
  autounfold in *;
  lets: TP.size_open_var;
  lets: TMP.size_open_rec;
  simpl;
  intros;
  fequals~;
  auto.

Lemma size_open_rec_st:
  forall t, size_open_rec_st_pred t.
Proof.
  size_open_rec_X_induction St_ind_mutual;
  size_open_rec_X_proof.
Qed.

Lemma size_open_rec_e:
  forall t, size_open_rec_e_pred t.
Proof.
  size_open_rec_X_induction E_ind_mutual;
  size_open_rec_X_proof.
Qed.

Lemma size_open_rec_f:
  forall t, size_open_rec_f_pred t.
Proof.
  size_open_rec_X_induction F_ind_mutual;
  size_open_rec_X_proof.
Qed.

Lemma size_open_rec:
  forall t alpha n, 
    TM.size (open_rec n (ftvar alpha) t) = TM.size t.
Proof.
  destruct t;
  lets: size_open_rec_st;
  lets: size_open_rec_e;
  lets: size_open_rec_f;
  simpl;
  intros;
  fequals~.
Qed.

(** Interaction of [size] with [close_var] *)

Lemma size_close_var_v:
  forall t alpha n,
  TM.size_v (close_rec_v n alpha t) = TM.size_v t.
Proof.
  induction t; auto.
Qed.

Function size_close_var_st_pred (t : St) :=
  forall alpha n,
  TM.size_st (close_rec_st n alpha t) = TM.size_st t.
Hint Unfold size_close_var_st_pred.

Function size_close_var_e_pred (t : E) :=
  forall alpha n,
    TM.size_e (close_rec_e n alpha t) = TM.size_e t.
Hint Unfold size_close_var_e_pred.

Function size_close_var_f_pred (t : F) :=
  forall alpha n,
    TM.size_f (close_rec_f n alpha t) = TM.size_f t.
Hint Unfold size_close_var_f_pred.

Ltac size_close_var_X_induction T :=
  apply (T
           size_close_var_st_pred
           size_close_var_e_pred
           size_close_var_f_pred).           

Ltac size_close_var_X_proof :=
  autounfold in *;
  lets: TP.size_close_var;
  lets: TMP.size_close_var;
  simpl;
  intros;
  fequals~.

Lemma size_close_var_st:
  forall t, size_close_var_st_pred t.
Proof.
  size_close_var_X_induction St_ind_mutual;
  size_close_var_X_proof.
Qed.

Lemma size_close_var_e:
  forall t, size_close_var_e_pred t.
Proof.
  size_close_var_X_induction E_ind_mutual;
  size_close_var_X_proof.
Qed.
  
Lemma size_close_var_f:
  forall t, size_close_var_f_pred t.
Proof.
  size_close_var_X_induction F_ind_mutual;
  size_close_var_X_proof.
Qed.


Lemma size_close_var:
  forall t alpha n,
    TM.size (close_rec n alpha t) = TM.size t.
Proof.
  lets: size_close_var_st;
  lets: size_close_var_e;
  lets: size_close_var_f;
  destruct t;
  simpl;
  intros;
  fequals~.
Qed.

(** The induction principle *)
(* This would be very large, three induction principles. *)
(* And the only thing Dan seems to induct on is the length of a context,
  not its full size. So unless I need this I won't make it. *)

End TTMP.