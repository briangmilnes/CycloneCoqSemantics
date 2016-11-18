(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION".   Daniel Grossman, August 2003 *)
(* Lemmas from the Lambda JAR paper. *)
(* Brian Milnes 2016 *)

Set Implicit Arguments.
Require Export Cyclone_Type_Substitution Cyclone_LN_FV Cyclone_LN_LC_Body Cyclone_LN_Open_Close Cyclone_LN_Tactics Cyclone_LN_FSET Cyclone_LN_Tactics Cyclone_LN_Size.
Open Scope cyclone_scope.

(* This is the version just for the lemmas about manipulating terms. *)

(* ====================================================================== *)
(** ** Proofs *)

(* ********************************************************************** *)
(** Variable closing and variable opening are reciprocal of one another *)

(** Showing that [close_var] after [open_var] is the identity is easy *)

Lemma close_v_tm_v_open_t_t_v :
  forall t x n,
  x \notin fv_tm_v t -> 
  close_rec_v_tm_v n x (open_rec_v_tm_v n x t) = t.
Proof.
  introv.
  induction t; simpl; introv Fr; fequals~.
  case_nat~. simpl. case_var~.
  case_var~.
Qed.

(* BUG: unparallel with p and v on the arguments here. *)

Lemma close_v_tm_p_open_t_t_p :
  forall t x n,
  x \notin fv_tm_p t -> 
  close_rec_v_tm_p n x (open_rec_v_tm_p n x t) = t.
Proof.
  introv.
  induction t; simpl; introv Fr; fequals~.
  case_nat~. simpl. case_var~.
  case_var~.
Qed.

(* Restart Here: time for simultaneous induction but the form is working. *)

Lemma close_v_tm_e_open_t_t_e :
  forall t x n,
    x \notin fv_tm_st t ->
    close_rec_v_tm_st n x (open_rec_v_tm_st n x t) = t.
Proof.
  apply (St_ind_mutual 
           (fun t : St => 
              forall x n, 
                x \notin fv_tm_st t ->
                close_rec_v_tm_st n x (open_rec_v_tm_st n x t) = t)
           (fun t : E  => 
              forall x n, 
                x \notin fv_tm_e t ->
                close_rec_v_tm_e n x (open_rec_v_tm_e n x t) = t)
           (fun t : F  => 
              forall x n, 
                x \notin fv_tm_f t ->
                close_rec_v_tm_f n x (open_rec_v_tm_f n x t) = t));
  try solve[intros;
            simpl;
            fequals~;
            try apply* close_v_tm_v_open_t_t_v];
  (* A bit sloppy I'd say. *)
  try solve[
  introv IH1 IH2 NI;
  simpl;
  fequals~;
  simpl in NI;
  try solve[applys* IH1];
  try solve[applys* IH2]];
  try solve[
        introv IH1 IH2 IH3 NI;
        simpl;
          fequals~;
                 simpl in NI;
          try solve[applys* IH1];
          try solve[applys* IH2];
          try solve[applys* IH3]].
  all: intros.
  simpl.
  fequals~.
  simpl in H.
  try apply* close_v_tm_v_open_t_t_v.

Qed.




Lemma close_v_tm_open_t_t : forall x t, 
  x \notin fv_tm t -> 
  close_rec_v_tm 0 x (open_rec_v_tm 0 x t) = t.
Proof.
  introv. generalize 0.
  induction t; simpl; introv Fr; fequals~.
  case_nat~. simpl. case_var~.
  case_var~.
Qed.

(** The other direction is much harder; First, we first need
    to establish the injectivity of [open_var] *)

Lemma open_var_inj :
  forall x t1 t2, 
    x \notin (fv_tm t1) ->
    x \notin (fv_tm t2) -> 
    open_t_t (fevar x) t1 = open_t_t (fevar x) t2 ->
    (t1 = t2).
Proof.
  introv Fr1 Fr2 Eq.
  rewrite~ <- (@close_v_tm_open_t_t x t1).
  rewrite~ <- (@close_v_tm_open_t_t x t2).
  fequals~.
Qed.

(** We also need one (tricky) auxiliary lemma to handle the binder case *)

Lemma open_close_var_on_open_var :
  forall x y z t i j,
    i <> j ->
    y <> x ->
    y \notin (fv_tm t) ->
    open_rec_t_t i (fevar y) (open_rec_t_t j (fevar z) (close_rec_v_tm j x t))
  = open_rec_t_t j (fevar z) (close_rec_v_tm j x (open_rec_t_t i (fevar y) t)).
Proof.
  induction t; try solve[simpl; intros; try solve [ fequals~ ]];
  intros;
  do 4 (simpl; try case_nat~; try case_nat~; try case_var~).
Qed.

(** Now we can prove that [open_var] after [close_var] is the identity *)

Lemma open_close_var : forall x t, 
  lc_t t -> 
  open_t_t (fevar x) (close_v_tm x t)  = t.
Proof.
  introv T. unfold open_t_t, close_v_tm. generalize 0.
  induction T; try solve[intros; simpl; introv; fequals~];
  try solve[intros; simpl; case_var~; simpl; case_nat~];
  intros;
  simpl;
  fequals~;
  match goal with
   |- ?t = _ => pick_fresh y from (fv_tm t)
  end;
  apply~ (@open_var_inj y);
  lets M: open_close_var_on_open_var;
  unfold open_t_t in M;
  unfold open_t_t;
  rewrite~ M .
Qed.


(** As a bonus, we get the injectivity of [close_var] *)

Lemma close_var_inj : forall x t1 t2, 
  lc_t t1 -> lc_t t2 ->
  close_v_tm x t1 = close_v_tm x t2 ->
  (t1 = t2).
Proof.
  introv T1 T2 Eq.
  rewrite~ <- (@open_close_var x t1).
  rewrite~ <- (@open_close_var x t2).
  fequals~.
Qed.

(* ********************************************************************** *)
(** Properties of [body] *)

(** An abstraction is locally closed iff it satifies the predicate [body] *) 

(* BUG: why is this working for Arthur and not me? LC hints ? *)

Lemma lc_utype_iff_body : forall k t, 
  lc_t (utype k t) <-> body_t t.
Proof. 
  intros.
  unfold body_t, open_t_t.
  iff H;
  inversions* H.
Qed.

Lemma lc_etype_iff_body : forall p k t, 
  lc_t (etype p k t) <-> body_t t.
Proof.
  intros.
  unfold body_t, open_t_t.
  iff H; inversions* H.
Qed.

(*
Lemma lc_abs_iff_body : forall t1, 
  lc (trm_abs t1) <-> body t1.
Proof. intros. unfold body.
       iff H; inversions* H. 
Qed.
*)

(* ********************************************************************** *)
(** Interaction of [fv] with [open_var] and [close_var] *)

(** Opening with [u] adds [fv u] to the set of free variables *)

Lemma ftv_open : forall t u,
  fv_tm (open_t_t u t) \c fv_tm t \u fv_tm u.
Proof.
  introv. unfold open_t_t. generalize 0.
  induction t; intros l; simpl; try case_nat; try fset.
Qed.

(*
Lemma fv_open : forall t u,
  fv (open t u) \c fv t \u fv u.
Proof.
  introv. unfold open. generalize 0.
  induction t; intros k; simpl; try fset.
  case_nat; simpl; fset.
Qed.
*)

(** In particular, opening with variable [x] adds [x] to the set 
    of free variables *)

Lemma open_var_fv : forall x t,
  fv_tm (open_rec_t_t 0 (fevar x) t) \c (fv_tm t \u \{x}).
Proof. intros. apply ftv_open. Qed.

(*
Lemma open_var_fv : forall x t,
  fv (open_var t x) \c (fv t \u \{x}).
Proof. intros. apply fv_open. Qed.
*)

(** Closing w.r.t variable [x] removes [x] from the set of free variables *)

Lemma close_tv_fv : forall x t,
  fv_tm (close_rec_v_tm 0 x t) \c (fv_tm t \- \{x}).
Proof.
  introv. unfold close_v_tm. generalize 0.
  induction t; intros l; simpl; try fset.
  case_var; simpl; fset. 
Qed.

(*
Lemma close_var_fv : forall x t,
  fv (close_var x t) \c (fv t \- \{x}).
Proof.
  introv. unfold close_var. generalize 0.
  induction t; intros k; simpl; try fset.
  case_var; simpl; fset. 
Qed.
*)

(* ********************************************************************** *)
(** Properties of substitution *)

(** Distributivity of [subst] on [open].
    Two (tricky) intermediate lemmas are required *)

Lemma open_rec_lc_ind : 
  forall t j v i u,
    i <> j ->
    open_rec_t_t i u (open_rec_t_t j v t) = open_rec_t_t j v t ->
    open_rec_t_t i u t = t.
Proof.
  induction t; introv Nq Eq;
   simpls; inversions~ Eq; fequals*.
  case_nat~. case_nat~.
Qed.

Lemma open_rec_t_t_lc_t : forall u t k,
  lc_t t -> open_rec_t_t k u t = t.
Proof.
  introv T. gen k.
  induction T; intros; simpl; fequals~;
  pick_fresh x;
  apply~ (@open_rec_lc_ind t0 0 (fevar x));
  apply~ H0.
Qed.

Lemma subst_t_v_tm_open_rec_t_t :
  forall x u t v, 
    lc_t u -> 
    subst_t_v_tm u x (open_rec_t_t 0 v t) =
    open_rec_t_t 0 (subst_t_v_tm u x v) (subst_t_v_tm u x t).
Proof.
  intros. generalize 0.
  induction t; intros; simpl; fequals~.
  case_nat~.
  case_var~. rewrite~ open_rec_t_t_lc_t.
Qed.

(** In particular, we can distribute [subst] on [open_var] *)

Lemma subst_t_v_tm_open_rec_v_tm:
  forall x y u t, 
    x <> y ->
    lc_t u -> 
    subst_t_v_tm u x (open_rec_t_t 0 (fevar y) t) =
    open_rec_t_t 0 (fevar y) (subst_t_v_tm u x t).
Proof.
  introv N U.
  rewrite~ subst_t_v_tm_open_rec_t_t.
  fequals.
  simpl.
  case_if~.
Qed.

(** For the distributivity of [subst] on [close_var],
    one simple intermediate lemmas is required to 
    say that closing on a fresh name is the identity *)

Lemma close_rec_v_tm_fresh : forall k x t,
  x \notin fv_tm t -> close_rec_v_tm k x t = t.
Proof.
  introv. gen k. induction t; simpl; intros; fequals*. 
  case_var~. 
Qed.

(** Distributivity of [subst] on [close_var] *)

Lemma subst_t_v_tm_close_rec_v_tm:
  forall x y u t, 
    x <> y ->
    y \notin fv_tm u -> 
    subst_t_v_tm u x (close_rec_v_tm 0 y t) = close_rec_v_tm 0 y (subst_t_v_tm u x t).
Proof.
  introv N F. generalize 0.
  induction t; intros l; simpl; fequals~.
  case_var~; simpl.
  case_var~; simpl. case_var~.
  case_var~; simpl.
  rewrite~ close_rec_v_tm_fresh.
  case_var~.
Qed.

(** Substitution for a fresh name is the identity *)

Lemma subst_t_v_tm_fresh : forall x t u, 
  x \notin fv_tm t -> subst_t_v_tm u x t = t.
Proof.
  intros.
  induction t; simpls; fequals~. case_var~.
Qed.

(** Substitution can be introduced to decompose an opening *)

Lemma subst_t_v_tm_intro :
  forall x t u, 
    x \notin (fv_tm t) ->
    lc_t u ->
    open_rec_t_t 0 u t = subst_t_v_tm u x (open_rec_t_t 0 (fevar x) t).
Proof.
  introv F U. 
  rewrite~ subst_t_v_tm_open_rec_t_t.
  fequals.
  simpl.
  case_var~.
  rewrite~ subst_t_v_tm_fresh.
Qed.

(** An alternative, longer proof, but with fewer hypotheses *)

Lemma subst_t_v_tm_intro_alternative : forall x t u, 
  x \notin (fv_tm t) -> 
  open_rec_t_t 0 u t = subst_t_v_tm u x (open_rec_t_t 0 (fevar x) t).
Proof.
  introv H. generalize 0. gen H.
  induction t; simpl; intros; fequals*.
  case_nat*.
  simpl. case_var*.
  case_var*.
Qed.

(** Substitution can be introduced to decompose a variable
    closing in terms of another one using a different name *)

Lemma close_v_tm_rename : forall x y t,
  x \notin fv_tm t ->
  close_rec_v_tm 0 y t =
  close_rec_v_tm 0 x (subst_t_v_tm (fevar x) y t).
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
  lc_t u -> lc_t t -> lc_t (subst_t_v_tm u x t).
Proof.
  introv U T. induction T; simple~;
  try case_var~;
  try apply_fresh lc_t_utype;
  try apply_fresh lc_t_etype;
  rewrite~ <- subst_t_v_tm_open_rec_v_tm.
Qed.

(** Substitution of a locally closed terms into a body one produces
    another body *)

Lemma subst_t_v_tm_body_t :
  forall x t u,
    lc_t u -> body_t t -> body_t (subst_t_v_tm u x t).
Proof.
  introv U [L H]. 
  exists_fresh. 
  rewrite~ <- subst_t_v_tm_open_rec_v_tm.
  apply~ subst_lc.
Qed.

(** Opening of a body with a locally closed terms produces a 
    locally closed term *)

Lemma open_rec_t_t_preserves_lc_t : forall t u,
  body_t t -> lc_t u -> lc_t (open_rec_t_t 0 u t).
Proof.
  introv [L H] U.
  pick_fresh x. 
  rewrite~ (@subst_t_v_tm_intro x).
  apply~ subst_lc. 
Qed.


(* ====================================================================== *)
(** ** An induction principle for locally closed terms *)

(** Interaction of [size] with [open_var] *)

Lemma size_open_rec_v_tm : forall x t,
  size_t (open_rec_t_t 0 (fevar x) t) = size_t t.
Proof.
  intros. generalize 0.
  induction t; intros; simple~. case_nat~.
Qed.

(** Interaction of [size] with [close_var] *)

Lemma size_close_var : forall x t,
  size_t (close_rec_v_tm 0 x t) = size_t t.
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
