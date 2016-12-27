(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION".   Daniel Grossman, August 2003 *)
(* Lemmas from the Lambda JAR paper, comments/theorems from Arthur Chargeuraud. *)
(* Brian Milnes 2016 *)

Set Implicit Arguments.
Require Export Cyclone_LN_Types Cyclone_LN_Tactics.
Open Scope cyclone_scope.
Open Scope nat_scope.
Import T.

(* This is the version just for the lemmas about types. *)

(* ====================================================================== *)
(** ** Proofs *)

(* ********************************************************************** *)
(** Variable closing and variable opening are reciprocal of one another *)

(** Showing that [close_var] after [open_var] is the identity is easy *)

Module TP. (* T = Type P = Proof. *)

Lemma close_open : forall alpha t, 
  alpha \notin fv t -> 
  close alpha (open (ftvar alpha) t ) = t.
Proof.
  introv. unfold close, open. generalize 0.
  induction t; simpl; introv Fr; fequals~.
  case_nat~. simpl. 
  case_var~.
  case_var~.
Qed.

(** The other direction is much harder; First, we first need
    to establish the injectivity of [open_var] *)

Lemma open_var_inj :
  forall alpha t1 t2, 
    alpha \notin (fv t1) ->
    alpha \notin (fv t2) -> 
    open (ftvar alpha) t1 = open (ftvar alpha) t2 ->
    (t1 = t2).
Proof.
  introv Fr1 Fr2 Eq.
  rewrite~ <- (@close_open alpha t1).
  rewrite~ <- (@close_open alpha t2).
  fequals~.
Qed.

(** We also need one (tricky) auxiliary lemma to handle the binder case *)

Lemma open_close_var_on_open_var :
  forall alpha beta gamma t i j,
    i <> j ->
    beta <> alpha ->
    beta \notin (fv t) ->
    open_rec i (ftvar beta) (open_rec j (ftvar gamma) (close_rec j alpha t))
  = open_rec j (ftvar gamma) (close_rec j alpha (open_rec i (ftvar beta) t)).
Proof.
  induction t; try solve[simpl; intros; try solve [ fequals~ ]];
  intros;
  do 4 (simpl; try case_nat~; try case_nat~; try case_var~).
Qed.

(** Now we can prove that [open_var] after [close_var] is the identity *)

Lemma open_close_var : forall alpha t,
  lc t -> 
  forall n, open_rec n (ftvar alpha) (close_rec n alpha t)  = t.
Proof.
  introv T. 
  induction T; try solve[intros; simpl; introv; fequals~];
  try solve[intros; simpl; case_var~; simpl; case_nat~];
  intros;
  simpl;
  fequals~;
  match goal with
   |- ?t = _ => pick_fresh y from (fv t)
  end;
  apply~ (@open_var_inj y);
  lets M: open_close_var_on_open_var;
  unfold open in M;
  unfold open;
  rewrite~ M.
Qed.

(** As a bonus, we get the injectivity of [close_var] *)

Lemma close_var_inj : forall alpha t1 t2, 
  lc t1 -> lc t2 ->
  forall n, 
    close_rec n alpha t1 = close_rec n alpha t2 ->
    (t1 = t2).
Proof.
  introv T1 T2 Eq.
  rewrite~ <- (@open_close_var alpha t1 T1 n).
  rewrite~ <- (@open_close_var alpha t2 T2 n).
  fequals~.
Qed.

(* ********************************************************************** *)
(** Properties of [body] *)

(** An abstraction is locally closed iff it satifies the predicate [body] *) 

Lemma lc_utype_iff_body : forall k t, 
  lc (utype k t) <-> body t.
Proof. 
  intros.
  unfold body, open.
  iff H;
  inversions* H.
Qed.

Lemma lc_etype_iff_body : forall p k t, 
  lc (etype p k t) <-> body t.
Proof.
  intros.
  unfold body, open.
  iff H; inversions* H.
Qed.


(* ********************************************************************** *)
(** Interaction of [fv] with [open_var] and [close_var] *)
(* Bugs here: weak, it's an equality. *)

(** Opening with [u] adds [fv u] to the set of free variables *)

Lemma fv_open : forall t u n,
  fv (open_rec n u t) \c fv t \u fv u.
Proof.
  intros t u.
  induction t; intros; simpl; try case_nat; try fset.
Qed.

(** In particular, opening with variable [x] adds [x] to the set 
    of free variables *)

Lemma open_var_fv : forall x t n,
  fv (open_rec n (ftvar x) t) \c (fv t \u \{x}).
Proof. intros. apply fv_open. Qed.

(** Closing w.r.t variable [x] removes [x] from the set of free variables *)

Lemma close_fv : forall x t n,
  fv (close_rec n x t) \c (fv t \- \{x}).
Proof.
  intros x t.
  induction t; intros l; simpl; try fset.
  case_var; simpl; fset. 
Qed.

(* ********************************************************************** *)
(** Properties of substitution *)

(** Distributivity of [subst] on [open].
    Two (tricky) intermediate lemmas are required *)

Lemma open_rec_lc_ind : 
  forall t j v i u,
    i <> j ->
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
  introv T. gen k.
  induction T; intros; simpl; fequals~;
  pick_fresh alpha;
  apply~ (@open_rec_lc_ind t0 0 (ftvar alpha));
  apply~ H0.
Qed.

Lemma subst_open_rec :
  forall alpha u t v n, 
    lc u -> 
    subst u alpha (open_rec n v t) =
    open_rec n (subst u alpha v) (subst u alpha t).
Proof.
  intros. generalize n.
  induction t; intros; simpl; fequals~.
  case_nat~.
  case_var~.
  rewrite~ open_rec_lc.
Qed.

(** In particular, we can distribute [subst] on [open_var] *)

Lemma subst_open_var:
  forall alpha beta u t n, 
    alpha <> beta ->
    lc u -> 
    subst u alpha (open_rec n (ftvar beta) t) =
    open_rec n (ftvar beta) (subst u alpha t).
Proof.
  introv N U.
  rewrite~ subst_open_rec.
  fequals.
  simpl.
  case_if~.
Qed.

(** For the distributivity of [subst] on [close_var],
    one simple intermediate lemmas is required to 
    say that closing on a fresh name is the identity *)

Lemma close_rec_fresh : forall k alpha t,
  alpha \notin fv t -> close_rec k alpha t = t.
Proof.
  introv. gen k. induction t; simpl; intros; fequals*. 
  case_var~. 
Qed.

(** Distributivity of [subst] on [close_var] *)

Lemma subst_close_rec:
  forall alpha beta u t n, 
    alpha <> beta ->
    beta \notin fv u -> 
    subst u alpha (close_rec n beta t) = close_rec n beta (subst u alpha t).
Proof.
  introv N F. generalize n.
  induction t; intros l; simpl; fequals~.
  case_var~; simpl.
  case_var~; simpl. case_var~.
  case_var~; simpl.
  rewrite~ close_rec_fresh.
  case_var~.
Qed.

(** Substitution for a fresh name is the identity *)

Lemma subst_fresh : forall alpha t u, 
  alpha \notin fv t -> subst u alpha t = t.
Proof.
  intros.
  induction t; simpls; fequals~. case_var~.
Qed.

(** Substitution can be introduced to decompose an opening *)

Lemma subst_intro :
  forall alpha t u, 
    alpha \notin (fv t) ->
    lc u ->
    open_rec 0 u t = subst u alpha (open_rec 0 (ftvar alpha) t).
Proof.
  introv F U. 
  rewrite~ subst_open_rec.
  fequals.
  simpl.
  case_var~.
  rewrite~ subst_fresh.
Qed.

(** An alternative, longer proof, but with fewer hypotheses *)

Lemma subst_intro_alternative : forall alpha t u n, 
  alpha \notin (fv t) -> 
  open_rec n u t = subst u alpha (open_rec n (ftvar alpha) t).
Proof.
  introv H. generalize n. gen H.
  induction t; simpl; intros; fequals*.
  case_nat*.
  simpl. case_var*.
  case_var*.
Qed.

(** Substitution can be introduced to decompose a variable
    closing in terms of another one using a different name *)

Lemma close_rename : forall alpha beta t n,
  alpha \notin fv t ->
  close_rec n beta t =
  close_rec n alpha (subst (ftvar alpha) beta t).
Proof.
  introv.  generalize n.
  induction t; simpl; intros l F; fequals~.
  case_var~; case_var~; simpl; case_var~.
Qed.

(* ********************************************************************** *)
(** Preservation of local closure through substitution and opening *)

(** Substitution of a locally closed terms into another one produces
    a locally closed term *)

Lemma subst_lc : forall alpha u t,
  lc u -> lc t -> lc (subst u alpha t).
Proof.
  introv U T. induction T; simple~;
  try case_var~;
  try apply_fresh lc_utype;
  try apply_fresh lc_etype;
  rewrite~ <- subst_open_var.
Qed.

(* ====================================================================== *)
(** ** An induction principle for locally closed terms *)

(** Interaction of [size] with [open_var] *)

Lemma size_open_var : forall alpha t n,
  size (open_rec n (ftvar alpha) t) = size t.
Proof.
  intros. generalize n.
  induction t; intros; simple~. case_nat~.
Qed.

(** Interaction of [size] with [close_var] *)

Lemma size_close_var : forall alpha t n,
  size (close_rec n alpha t) = size t.
Proof.
  intros. generalize n.
  induction t; intros; simple~. case_var~.
Qed.

(** The induction principle *)

(* Although Dan uses only induction on the size of \Gamma,
 I may find this useful in an LN style proof. *)

Lemma lc_induct_size :
  forall P : Tau -> Prop,
    (forall alpha,  P (ftvar alpha)) ->
    (P cint) ->
    (forall t1 t2, (lc t1) -> (P t1) -> (lc t2) -> (P t2) ->
                   P (cross t1 t2)) ->
    (forall t1 t2, (lc t1) -> (P t1) -> (lc t2) -> (P t2) ->
                   P (arrow t1 t2)) ->
    (forall t1, (lc t1) -> (P t1) -> P (ptype t1)) ->

    (forall k t1,
       body t1 ->
       (forall t2 alpha,
          alpha \notin fv t2 ->
          size t2 = size t1 ->
          lc (open_rec 0 (ftvar alpha) t2) ->
          P (open_rec 0 (ftvar alpha) t2)) ->
       P (utype k t1)) ->

    (forall p k t1,
       body t1 ->
       (forall t2 alpha,
          alpha \notin fv t2 ->
          size t2 = size t1 ->
          lc (open_rec 0 (ftvar alpha) t2) ->
          P (open_rec 0 (ftvar alpha) t2)) ->
       P (etype p k t1)) -> 

    (forall t, lc t -> P t).
Proof.
  intros P Hvar Hcint Hcross Harrow Hptype Hutype Hetype t.
  induction t using (@measure_induction _ size).
  introv T. 
  inverts T; simpl in H; auto.

  apply~ Hutype.
  try exists_fresh; auto.
  try introv Fr Eq T.
  apply~ H.
  try rewrite~ size_open_var.

  apply~ Hetype.
  try exists_fresh; auto.
  try introv Fr Eq T.
  apply~ H.
  try rewrite~ size_open_var.

Qed.


(* ====================================================================== *)
(** ** Alternative definition for local closure *)

(* ********************************************************************** *)
(** Equivalence of [lc] and [lc'] *)

Lemma lc_rec_open_var_rec : forall x t k,
  lc_at k (open_rec k (ftvar x) t) -> lc_at (S k) t.
Proof.
  induction t; simpl; introv H; autos*.
  case_nat; simpls~.
Qed.

Lemma lc_to_lc' : forall t,
  lc t -> lc' t.
Proof.
  introv T. induction T; unfold lc'; simple~;
  do 2 try solve [pick_fresh x; apply~ (@lc_rec_open_var_rec x); apply~ H0].
Qed.

Lemma lc_at_open_var_rec : forall x t k,
  lc_at (S k) t -> lc_at k (open_rec k (ftvar x) t).
Proof.
  induction t; simpl; introv H; autos*. case_nat; simple~.
Qed.

Lemma lc'_to_lc : forall t,
  lc' t -> lc t.
Proof.
  introv. unfold lc'.
  induction t using (@measure_induction _ size).
  destruct t; simpl; introv T'; simpl in H; autos*.
  apply_fresh lc_utype. apply H. rewrite~ size_open_var.
   apply~ lc_at_open_var_rec.
  apply_fresh lc_etype. apply H. rewrite~ size_open_var.
   apply~ lc_at_open_var_rec.
Qed.

Lemma lc_eq_lc' : lc = lc'.
Proof. extens. split. applys lc_to_lc'. applys lc'_to_lc. Qed.

(** Substitution of a locally closed terms into a body one produces
    another body *)

(* We need a lemma that Arthur only proved for his alternate inductive lc. *)

Lemma open_rec_lc'_ind : forall u t k,
  lc_at k t -> open_rec k u t = t.
Proof.
  introv. gen k. induction t; simpl; introv F; fequals*.
  case_nat~. false. nat_math.
Qed.

Lemma lc'_open_var_rec:
  forall alpha t,
    lc' t -> lc (open_rec 0 (ftvar alpha) t).
Proof.  
  introv lct.
  assert(lc' t); auto.
  unfold lc' in *.
  apply open_rec_lc'_ind with (u:= ftvar alpha) in lct.
  rewrite lct.
  apply lc'_to_lc in H.
  assumption.
Qed.

Lemma lc_open_var_rec:
  forall alpha t,
    lc t -> lc (open_rec 0 (ftvar alpha) t).
Proof.
  intros.
  apply lc_to_lc' in H.
  applys~ lc'_open_var_rec.
Qed.

Lemma subst_body :
  forall alpha t u,
    lc u -> body t -> body (subst u alpha t).
Proof.
  introv U [L H]. 
  exists_fresh. 
  unfold open.
  rewrite~ <- subst_open_var.
  apply~ subst_lc.
Qed.

(** Opening of a body with a locally closed terms produces a 
    locally closed term *)

Lemma open_rec_preserves_lc : forall t u,
  body t -> lc u -> lc (open_rec 0 u t).
Proof.
  introv [L H] U.
  pick_fresh alpha. 
  rewrite~ (@subst_intro alpha).
  apply~ subst_lc. 
Qed.

End TP.