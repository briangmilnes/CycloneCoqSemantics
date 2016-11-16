(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION".   Daniel Grossman, August 2003 *)
(* Lemmas from the Lambda JAR paper. *)
(* Brian Milnes 2016 *)

Set Implicit Arguments.
Require Export Cyclone_Type_Substitution Cyclone_LN_FV Cyclone_LN_LC_Body Cyclone_LN_Open_Close Cyclone_LN_Tactics Cyclone_LN_FSET.
Open Scope cyclone_scope.

(* Arthur has 31 Lemmas in the JAR paper implementation. 
   As we have three forms of subst/open/close 
   t_tv_t
   t_tv_tm
   v_v_tm
   
 we end up with roughly three times the number of lemmas.
 And the t_tv_tm and v_v_tm forms have four versions to 
 implement the mutually recursive induction.

 I'll have to do something to either automate these or
to move to flattened syntax. Certainly something to
reduce their textual size as they are copying inductive
hypothesis.

 Arthur is also not using the {}/[] formulation in these
copied lemmas. 
*)


(* ====================================================================== *)
(** ** Proofs *)

(* ********************************************************************** *)
(** Variable closing and variable opening are reciprocal of one another *)

(** Showing that [close_var] after [open_var] is the identity is easy *)

Lemma close_tv_t_open_t_t : forall alpha t, 
  alpha \notin ftv_t t -> 
  close_tv_t alpha (open_t_t (ftvar alpha) t ) = t.
Proof.
  introv. unfold close_tv_t, open_t_t. generalize 0.
  induction t; simpl; introv Fr; fequals~.
  case_nat~. simpl. case_var~.
  case_var~.
Qed.

(** The other direction is much harder; First, we first need
    to establish the injectivity of [open_var] *)

Lemma open_var_inj :
  forall alpha t1 t2, 
    alpha \notin (ftv_t t1) ->
    alpha \notin (ftv_t t2) -> 
    (open_t_t (ftvar alpha) t1 = open_t_t (ftvar alpha) t2) ->
  (t1 = t2).
Proof.
  introv Fr1 Fr2 Eq.
  rewrite~ <- (@close_tv_t_open_t_t alpha t1).
  rewrite~ <- (@close_tv_t_open_t_t alpha t2).
  fequals~.
Qed.

(** We also need one (tricky) auxiliary lemma to handle the binder case *)

Lemma open_close_var_on_open_var :
  forall alpha beta z t i j,
    i <> j ->
    beta <> alpha ->
    beta \notin (ftv_t t) ->
    open_rec_t_t i (ftvar beta) (open_rec_t_t j z (close_rec_tv_t j alpha t))
  = open_rec_t_t j z (close_rec_tv_t j alpha (open_rec_t_t i (ftvar beta) t)).
Proof.
  induction t; try solve[simpl; intros; try solve [ fequals~ ]].
  intros.

  do 2 (case_nat; simpl); try solve [ case_var~ | case_nat~ ]. 

(*
  induction t; simpl; intros; try solve [ fequals~ ].
  do 2 (case_nat; simpl); try solve [ case_var~ | case_nat~ ]. 
  case_nat~. simpl.
  case_var~. simpl. case_nat~. 
*)
Admitted.

(** Now we can prove that [open_var] after [close_var] is the identity *)

Lemma open_close_var : forall alpha t, 
  lc_t t -> 
  open_t_t (close_tv_t alpha t) (ftvar alpha) = t.
Proof.
  introv T. unfold open_t_t, close_tv_t. generalize 0.
  induction T; intros; simpl; introv; fequals~.
  case_var~. simpl. case_nat~.
  match goal with |- ?t = _ => pick_fresh y from (fv t) end.
   apply~ (@open_var_inj y).
   lets M: open_close_var_on_open_var. unfold open_rec_t_t in M.
   unfold open_var, open. rewrite~ M. apply~ H0.
Qed.

(** As a bonus, we get the injectivity of [close_var] *)

Lemma close_var_inj : forall x t1 t2, 
  lc t1 -> lc t2 ->
  (close_var x t1 = close_var x t2) -> (t1 = t2).
Proof.
  introv T1 T2 Eq.
  rewrite~ <- (@open_close_var x t1).
  rewrite~ <- (@open_close_var x t2).
  fequals~.
Qed.


(* ********************************************************************** *)
(** Properties of [body] *)

(** An abstraction is locally closed iff it satifies the predicate [body] *) 

Lemma lc_abs_iff_body : forall t1, 
  lc (trm_abs t1) <-> body t1.
Proof. intros. unfold body.
       iff H; inversions* H. 
Qed.


(* ********************************************************************** *)
(** Interaction of [fv] with [open_var] and [close_var] *)

(** Opening with [u] adds [fv u] to the set of free variables *)

Lemma fv_open : forall t u,
  fv (open t u) \c fv t \u fv u.
Proof.
  introv. unfold open. generalize 0.
  induction t; intros k; simpl; try fset.
  case_nat; simpl; fset.
Qed.

(** In particular, opening with variable [x] adds [x] to the set 
    of free variables *)

Lemma open_var_fv : forall x t,
  fv (open_var t x) \c (fv t \u \{x}).
Proof. intros. apply fv_open. Qed.

(** Closing w.r.t variable [x] removes [x] from the set of free variables *)

Lemma close_var_fv : forall x t,
  fv (close_var x t) \c (fv t \- \{x}).
Proof.
  introv. unfold close_var. generalize 0.
  induction t; intros k; simpl; try fset.
  case_var; simpl; fset. 
Qed.


(* ********************************************************************** *)
(** Properties of substitution *)

(** Distributivity of [subst] on [open].
    Two (tricky) intermediate lemmas are required *)

Lemma open_rec_lc_ind : forall t j v i u, i <> j ->
  open_rec i u (open_rec j v t) = open_rec j v t ->
  open_rec i u t = t.
Proof.
  induction t; introv Nq Eq;
   simpls; inversions~ Eq; fequals*.
  case_nat~. case_nat~.
Qed.

Lemma open_rec_lc : forall u t k,
  lc t -> open_rec k u t = t.
Proof.
  unfold open_rec_t_t. introv T. gen k.
  induction T; intros; simpl; fequals~. 
  pick_fresh y. apply~ (@open_rec_lc_ind t1 0 (trm_fvar y)).
  apply~ H0.
Qed.

Lemma subst_open : forall x u t v, lc u -> 
  subst x u (open t v) = open (subst x u t) (subst x u v).
Proof.
  intros. unfold open. generalize 0.
  induction t; intros; simpl; fequals~.
  case_nat~.
  case_var~. rewrite~ open_rec_lc.
Qed.

(** In particular, we can distribute [subst] on [open_var] *)

Lemma subst_open_var : forall x y u t, 
  y <> x -> lc u -> 
  subst x u (open_var t y) = open_var (subst x u t) y.
Proof.
  introv N U. unfold open_var. rewrite~ subst_open.
  fequals. simpl. case_if~.
Qed.

(** For the distributivity of [subst] on [close_var],
    one simple intermediate lemmas is required to 
    say that closing on a fresh name is the identity *)

Lemma close_rec_tv_t_fresh : forall k x t,
  x \notin fv t -> close_rec_tv_t k x t = t.
Proof.
  introv. gen k. induction t; simpl; intros; fequals*. 
  case_var~. 
Qed.

(** Distributivity of [subst] on [close_var] *)

Lemma subst_close_var : forall x y u t, 
  y <> x -> y \notin fv u -> 
  subst x u (close_var y t) = close_var y (subst x u t).
Proof.
  introv N F. unfold close_var. generalize 0.
  induction t; intros k; simpl; fequals~.
  case_var~; simpl.
    case_var~; simpl. case_var~.
    case_var~; simpl.
      rewrite~ close_rec_tv_t_fresh.
      case_var~.
Qed.

(** Substitution for a fresh name is the identity *)

Lemma subst_fresh : forall x t u, 
  x \notin fv t -> subst x u t = t.
Proof. intros. induction t; simpls; fequals~. case_var~. Qed.

(** Substitution can be introduced to decompose an opening *)

Lemma subst_intro : forall x t u, 
  x \notin (fv t) -> lc u ->
  open t u = subst x u (open_var t x).
Proof.
  introv F U. unfold open_var. rewrite~ subst_open.
  fequals. rewrite~ subst_fresh. simpl. case_var~.
Qed.

(** An alternative, longer proof, but with fewer hypotheses *)

Lemma subst_intro_alternative : forall x t u, 
  x \notin (fv t) -> 
  open t u = subst x u (open_var t x).
Proof.
  introv H. unfold open_var, open. generalize 0. gen H.
  induction t; simpl; intros; fequals*.
  case_nat*.
  simpl. case_var*.
  case_var*.
Qed.

(** Substitution can be introduced to decompose a variable
    closing in terms of another one using a different name *)

Lemma close_var_rename : forall x y t,
  x \notin fv t ->
  close_var y t = close_var x (subst y (trm_fvar x) t).
Proof.
  introv. unfold close_var. generalize 0.
  induction t; simpl; intros k F; fequals~.
  case_var; simpl; case_var~.
Qed.


(* ********************************************************************** *)
(** Preservation of local closure through substitution and opening *)

(** Substitution of a locally closed terms into another one produces
    a locally closed term *)

Lemma subst_lc : forall z u t,
  lc u -> lc t -> lc (subst z u t).
Proof.
  introv U T. induction T; simple~.
  case_var~.
  apply_fresh lc_abs. rewrite~ <- subst_open_var.
Qed.

(** Substitution of a locally closed terms into a body one produces
    another body *)

Lemma subst_body : forall z t u,
  lc u -> body t -> body (subst z u t).
Proof.
  introv U [L H]. exists_fresh. 
  rewrite~ <- subst_open_var. apply~ subst_lc.
Qed.

(** Opening of a body with a locally closed terms produces a 
    locally closed term *)

Lemma open_lc : forall t u,
  body t -> lc u -> lc (open t u).
Proof.
  introv [L H] U. pick_fresh y. rewrite~ (@subst_intro y).
  apply~ subst_lc. 
Qed.


(* ********************************************************************** *)
(** Two additional lemmas (not used in practical developments) *)

(** A body becomes a locally closed term when [open_var] is applied *)

Lemma open_var_lc : forall t1 x, 
  body t1 -> lc (open_var t1 x).
Proof.
  introv [L M]. pick_fresh y. unfold open_var. 
  rewrite~ (@subst_intro y). applys~ subst_lc.
Qed. 

(** A locally closed term becomes a body when [closed_var] is applied *)

Lemma close_var_lc : forall t x, 
  lc t -> body (close_var x t).
Proof.
  introv T. exists_fresh.
  rewrite~ (@close_var_rename y).
  rewrite~ open_close_var; apply~ subst_lc.
Qed.



(* ====================================================================== *)
(** ** An induction principle for locally closed terms *)

(** Interaction of [size] with [open_var] *)

Lemma size_open_var : forall x t,
  size (open_var t x) = size t.
Proof.
  intros. unfold open_var, open. generalize 0.
  induction t; intros; simple~. case_nat~.
Qed.

(** Interaction of [size] with [close_var] *)

Lemma size_close_var : forall x t,
  size (close_var x t) = size t.
Proof.
  intros. unfold close_var. generalize 0.
  induction t; intros; simple~. case_var~.
Qed.

(** The induction principle *)

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

(* ********************************************************************** *)
(** Weakening property of [lc_at] *)

Lemma lc_at_weaken_ind : forall k1 k2 t,
  lc_at k1 t -> k1 <= k2 -> lc_at k2 t.
Proof. introv. gen k1 k2. induction t; simpl; introv T Lt; auto_star. Qed.

Lemma lc_at_weaken : forall k t,
  lc' t -> lc_at k t.
Proof. introv H. apply~ (@lc_at_weaken_ind 0). Qed.
