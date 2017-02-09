(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION".   Daniel Grossman, August 2003 *)
(* Lemmas from the Lambda JAR paper built just for Terms. *)
(* Brian Milnes 2016 *)

Set Implicit Arguments.
Require Export Cyclone_LN_Tactics Cyclone_LN_Types Cyclone_LN_Types_Lemmas Cyclone_LN_Terms.
Require Export Cyclone_Classes Cyclone_Inductions.
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

Function close_open_prop (What In : Type) (H: LangFuns What Variables.var In) :=
  fun (t : In) =>
  forall (x : Variables.var) (n : nat),
    x \notin fv' t -> 
    close_rec' n x (open_rec' n x t) = t.
Hint Unfold close_open_prop.

(* This is a dramatically simplified version of the mutually inductive
proofs. Type classes are used to rewrite a single statement of the
lemma at the term level into each of the lemmas. The induction ltac
rewrites the predicate three times to set up the induction functions.
*)

Lemma close_open_v:
  forall (t : V), close_open_prop VLangFuns t.
Proof.
  introv; induction* t;
  simpl; intros; fequals~;
  try case_nat~; try simpl; try case_var~; try case_var~.
Qed.

Ltac close_open_proof :=
  auto_star;
  simpl;
  intros;
  fequals~;
  try applys~ close_open_v.

Lemma close_open_st:
  forall (t : St), close_open_prop StLangFuns t. 
Proof.
  StEF_Induction St_ind_mutual close_open_prop;
  close_open_proof.
Qed.

Lemma close_open_e:
  forall (t : E), close_open_prop ELangFuns t.
Proof.
  StEF_Induction E_ind_mutual close_open_prop;
  close_open_proof.
Qed.

Lemma close_open_f:
 forall (t : F), close_open_prop FLangFuns t.
Proof.
  StEF_Induction F_ind_mutual close_open_prop; 
  close_open_proof.
Qed.

Lemma close_open:
  forall t, close_open_prop TermLangFuns t.
Proof.
  lets*: close_open_st.
  lets*: close_open_e.
  lets*: close_open_f.
  intros; destruct* t; intros*; simpl; fequals~.
Qed.

(** The other direction is much harder; First, we first need
    to establish the injectivity of [open_var] *)

Function open_inj_prop (What In : Type) (H: LangFuns What Variables.var In) :=
  fun (t1 : In) =>
  forall (x : Variables.var) (n : nat) t2,
    x \notin (fv' t1) ->
    x \notin (fv' t2) -> 
    open_rec' n x t1 = open_rec' n x t2 ->
    (t1 = t2).
Hint Unfold open_inj_prop.

Lemma open_rec_v_inj :
  forall (t : V),  open_inj_prop VLangFuns t.
Proof.
  auto_star.
  intros.
  rewrite~ <- (@close_open_v t x n).
  rewrite~ <- (@close_open_v t2 x n).
  fequals~.
Qed.

Lemma open_rec_st_inj :
  forall (t : St),  open_inj_prop StLangFuns t.
Proof.
  auto_star.
  intros.
  rewrite~ <- (@close_open_st t x n).
  rewrite~ <- (@close_open_st t2 x n).
  fequals~.
Qed.

Lemma open_rec_e_inj :
  forall (t : E),  open_inj_prop ELangFuns t.
Proof.
  intros*.
  rewrite~ <- (@close_open_e t x n).
  rewrite~ <- (@close_open_e t2 x n).
  fequals~.
Qed.

Lemma open_rec_f_inj :
  forall (t : F),  open_inj_prop FLangFuns t.
Proof.
  intros*.
  rewrite~ <- (@close_open_f t x n).
  rewrite~ <- (@close_open_f t2 x n).
  fequals~.
Qed.

Lemma open_rec_inj :
  forall (t : Term),  open_inj_prop TermLangFuns t.
Proof.
  intros*.
  rewrite~ <- (@close_open t x n).
  rewrite~ <- (@close_open t2 x n).
  fequals~.
Qed.

(** We also need one (tricky) auxiliary lemma to handle the binder case *)

Function open_close_var_on_open_var_prop (What In : Type)
         (H: LangFuns What Variables.var In) :=
  fun (t : In) =>
  forall (x y z: Variables.var) (i j : nat),
    i <> j ->
    y <> x ->
    y \notin (fv' t) ->
    open_rec' i y (open_rec' j z (close_rec' j x t))
  = open_rec' j z (close_rec' j x (open_rec' i y t)).
Hint Unfold open_close_var_on_open_var_prop.

Lemma open_close_var_on_open_var_v:
  forall t,  open_close_var_on_open_var_prop VLangFuns t.
Proof.
  intros*.
  induction t; try solve[simpl; intros; try solve [ fequals~ ]];
  intros;
  do 4 (simpl; try case_nat~; try case_nat~; try case_var~).
Qed.

Ltac open_close_var_on_open_var_proof :=
  try solve[intros*; simpl; intros; try solve [ fequals~ ]];
  try solve[simpl; intros; fequals*; try apply~ open_close_var_on_open_var_v].

Lemma open_close_var_on_open_var_st:
  forall t,  open_close_var_on_open_var_prop StLangFuns t.
Proof.
  StEF_Induction St_ind_mutual open_close_var_on_open_var_prop;
  open_close_var_on_open_var_proof.
Qed.

Lemma open_close_var_on_open_var_e:
  forall t,  open_close_var_on_open_var_prop ELangFuns t.
Proof.
  StEF_Induction E_ind_mutual open_close_var_on_open_var_prop;
  open_close_var_on_open_var_proof.
Qed.

Lemma open_close_var_on_open_var_f:
  forall t,  open_close_var_on_open_var_prop FLangFuns t.
Proof.
  StEF_Induction F_ind_mutual open_close_var_on_open_var_prop;
  open_close_var_on_open_var_proof.
Qed.

Lemma open_close_var_on_open_var:
  forall t,  open_close_var_on_open_var_prop TermLangFuns t.
Proof.
  lets: open_close_var_on_open_var_st.
  lets: open_close_var_on_open_var_e.
  lets: open_close_var_on_open_var_f.
  simpl_classes.
  intros; destruct* t; simpl; intros; fequals~.
Qed.

(** Now we can prove that [open_var] after [close_var] is the identity *)

Function open_close_var_prop 
  (What In : Type) (H: LangFuns What Variables.var In) 
  (L : LcJudgement In) :=
  fun (t : In) (_ : lc' t) =>
   forall (x : Variables.var) (n : nat),
    open_rec' n x (close_rec' n x t)  = t.
Hint Unfold open_close_var_prop.

Lemma open_close_var_v:
  forall (t : V) (l : lc' t), open_close_var_prop VLangFuns LcVJudgement t l.
Proof.
  simpl_classes.
  introv LC.
  induction LC.
  intros; simpl; case_var~; simpl; case_nat~.
Qed.

Ltac open_close_var_proof y M :=
  intros; simpl; fequals~;
  lets*: open_close_var_on_open_var_v;
  try solve[case_var~; simpl; case_nat~];
  try solve[ 
        match goal with
            |- ?t = _ => pick_fresh y from (fv_st t)
        end];
  match goal with
    |- ?t = _ => pick_fresh y from (fv_st t)
  end; auto_star;
  apply open_rec_st_inj with (x:= y) (n:= 0); auto_star;
  lets* M: open_close_var_on_open_var_st;
  rewrite* M.

Lemma open_close_var_st: 
  forall (t : St) (l : lc' t), open_close_var_prop StLangFuns LcStJudgement t l.
Proof.
  LCSt_Induction lc_st_ind_mutual open_close_var_prop;
  open_close_var_proof y M.
Qed.

Lemma open_close_var_e: 
  forall (t : E) (l : lc' t), open_close_var_prop ELangFuns LcEJudgement t l.
Proof.
  LCSt_Induction lc_e_ind_mutual open_close_var_prop;
  open_close_var_proof y M.
Qed.

Lemma open_close_var_f: 
  forall (t : F) (l : lc' t), open_close_var_prop FLangFuns LcFJudgement t l.
Proof.
  LCSt_Induction lc_f_ind_mutual open_close_var_prop;
  open_close_var_proof y M.
Qed.

Lemma open_close_var:
  forall (t : Term) (l : lc' t), open_close_var_prop TermLangFuns LcTermJudgement t l.
Proof.
  lets*: open_close_var_st.
  lets*: open_close_var_e.
  lets*: open_close_var_f.
  intros; destruct* t; intros; simpl; fequals~; inversions* l.
Qed.

(** As a bonus, we get the injectivity of [close_var] *)

Lemma close_var_inj :
  forall t1 t2 x,
    lc t1 ->
    lc t2 ->
    close x t1 = close x t2 ->
    (t1 = t2).
Proof.
  unfold close.
  introv T1 T2 Eq.
  rewrite~ <- (@open_close_var t1 T1 x 0).
  rewrite~ <- (@open_close_var t2 T2 x 0).
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

Function fv_open_prop (What In : Type) (H: LangFuns What Variables.var In) :=
  fun (t : In) =>
  forall (u : Variables.var) (n : nat),
    fv' (open_rec' n u t) \c  fv' t \u \{u}.
Hint Unfold fv_open_prop.

Lemma fv_open_v :
  forall (v : V), fv_open_prop VLangFuns v.
Proof.
  intros*; destruct* v; simpl; try case_nat~; fset.
Qed.

Ltac fv_open_proof :=
  simpl_classes;
  intros l; simpl; try case_nat; try fset;
  intros;
  applys~ fv_open_v.

Lemma fv_open_st:
  forall (t : St), fv_open_prop StLangFuns t.
Proof.
  StEF_Induction St_ind_mutual fv_open_prop;
  fv_open_proof.
Qed.

Lemma fv_open_e:
  forall (t : E), fv_open_prop ELangFuns t.
Proof.
  StEF_Induction E_ind_mutual fv_open_prop;
  fv_open_proof.
Qed.

Lemma fv_open_f:
  forall (t : F), fv_open_prop FLangFuns t.
Proof.
  StEF_Induction F_ind_mutual fv_open_prop;
  fv_open_proof.
Qed.

Lemma fv_open : 
  forall (t : Term), fv_open_prop TermLangFuns t.
Proof.
  lets*: fv_open_st.
  lets*: fv_open_e.
  lets*: fv_open_f.
  intros*; destruct* t; simpl; intros*.
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

Function close_var_fv_prop (What In : Type) (H: LangFuns What Variables.var In) :=
  fun (t : In) =>
  forall (x : Variables.var) (n : nat),
  fv' (close_rec' n x t) \c (fv' t \- \{x}).
Hint Unfold close_var_fv_prop.

Lemma close_var_fv_v : 
  forall (t : V), close_var_fv_prop VLangFuns t.
Proof.
  intros*.
  destruct t; simpl; fset.
  case_var~; simpl; fset.
Qed.

Ltac close_var_fv_proof :=
  lets*: close_var_fv_v;
  simpl_classes; intros*; simpl; fset.

Lemma close_var_fv_st :
  forall (t : St), close_var_fv_prop StLangFuns t.
Proof.
  StEF_Induction St_ind_mutual close_var_fv_prop;
  close_var_fv_proof.
Qed.

Lemma close_var_fv_e :
  forall (t : E), close_var_fv_prop ELangFuns t.
Proof.
  StEF_Induction E_ind_mutual close_var_fv_prop;
  close_var_fv_proof.
Qed.

Lemma close_var_fv_f :
  forall (t : F), close_var_fv_prop FLangFuns t.
Proof.
  StEF_Induction F_ind_mutual close_var_fv_prop;
  close_var_fv_proof.
Qed.

Lemma close_var_fv : forall x t,
  fv (close_rec 0 x t) \c (fv t \- \{x}).
Proof.
  lets*: close_var_fv_st.
  lets*: close_var_fv_e.
  lets*: close_var_fv_f.
  destruct t; simpl; auto_star.
Qed.

(* ********************************************************************** *)
(** Properties of substitution *)

(** Distributivity of [subst] on [open].
    Two (tricky) intermediate lemmas are required *)

Function open_rec_lc_ind_prop (What In : Type) (H: LangFuns What Variables.var In) :=
  fun (t : In) =>
  forall (v u: Variables.var) (i j : nat),
    i <> j ->
    open_rec' i u (open_rec' j v t) = open_rec' j v t ->
    open_rec' i u t = t.
Hint Unfold open_rec_lc_ind_prop.

Lemma open_rec_lc_ind_v : 
  forall (t : V), open_rec_lc_ind_prop VLangFuns t.
Proof.
  induction t; introv Nq Eq;
  simpls; inversions~ Eq; fequals*.
  case_nat~. case_nat~.
Qed.

Ltac open_rec_lc_ind_proof :=
  lets*: open_rec_lc_ind_v;
  intros*;
  simpls;
  try inversion_on_equated_constructors;
  fequals~.

Lemma open_rec_lc_ind_st : 
  forall (t : St), open_rec_lc_ind_prop StLangFuns t.
Proof.
  StEF_Induction St_ind_mutual open_rec_lc_ind_prop;
  open_rec_lc_ind_proof.
Qed.

Lemma open_rec_lc_ind_e : 
  forall (t : E), open_rec_lc_ind_prop ELangFuns t.
Proof.
  StEF_Induction E_ind_mutual open_rec_lc_ind_prop;
  open_rec_lc_ind_proof.
Qed.

Lemma open_rec_lc_ind_f : 
  forall (t : F), open_rec_lc_ind_prop FLangFuns t.
Proof.
  StEF_Induction F_ind_mutual open_rec_lc_ind_prop;
  open_rec_lc_ind_proof.
Qed.

Lemma open_rec_lc_ind : 
  forall (t : Term), open_rec_lc_ind_prop TermLangFuns t.
Proof.
  intros.
  lets*: open_rec_lc_ind_st.
  lets*: open_rec_lc_ind_e.
  lets*: open_rec_lc_ind_f.
  destruct t; simpls;
  intros;
  fequals*;
  inversion_on_equated_constructors;
  auto_star.
Qed.

Function open_rec_lc_prop 
  (What In : Type) (H: LangFuns What Variables.var In) 
  (L : LcJudgement In) :=
  fun (t : In) (_ : lc' t) =>
   forall (u : Variables.var) (k : nat),
     open_rec' k u t = t.
Hint Unfold open_rec_lc_prop.

Lemma open_rec_lc_v:
  forall (t : V) (l : lc' t), open_close_var_prop VLangFuns LcVJudgement t l.
Proof.
  intros*.
  destruct t.
  inversion l.
  simpl.
  case_var.
  simpl.
  case_nat*.
  simpl.
  auto.
Qed.

Ltac open_rec_lc_proof :=
  intros*;
  simpl;
  fequals*;
  pick_fresh y;
  try apply~ open_rec_lc_ind_st;
  try apply~ open_rec_lc_ind_e;
  try apply~ open_rec_lc_ind_f;
  tryfalse.

Lemma open_rec_lc_st:
  forall (t : St) (l : lc' t), open_rec_lc_prop StLangFuns LcStJudgement t l.
Proof.
  LCSt_Induction lc_st_ind_mutual open_rec_lc_prop;
  open_rec_lc_proof.
Qed.

Lemma open_rec_lc_e:
  forall (t : E) (l : lc' t), open_rec_lc_prop ELangFuns LcEJudgement t l.
Proof.
  LCSt_Induction lc_e_ind_mutual open_rec_lc_prop;
  open_rec_lc_proof.
Qed.

Lemma open_rec_lc_f:
  forall (t : F) (l : lc' t), open_rec_lc_prop FLangFuns LcFJudgement t l.
Proof.
  LCSt_Induction lc_f_ind_mutual open_rec_lc_prop;
  open_rec_lc_proof.
Qed.

Lemma open_rec_lc:
  forall (t : Term) (l : lc' t), open_rec_lc_prop TermLangFuns LcTermJudgement t l.
Proof.
  lets* : open_rec_lc_st.
  lets* : open_rec_lc_e.
  lets* : open_rec_lc_f.  
  intros*.
  destruct t;
  simpl;
  inversion l;
  fequals~.
Qed.

Function subst_open_var_prop (In : Type) (H: LangFuns Variables.var Variables.var In) :=
  fun (t : In) =>
    forall (x u v : Variables.var) n,
      subst' u x (open_rec' n v t) = 
      open_rec' n (If v = x then u else v) (subst' u x t).
Hint Unfold subst_open_var_prop.

Lemma subst_open_var_v:
  forall (t : V), subst_open_var_prop VLangFuns t.
Proof.
  intros*.
  destruct t;
  repeat (simpl; case_var~);
  repeat (simpl; case_nat~);
  repeat (simpl; case_var~).
Qed.

Ltac subst_open_var_proof:= 
    try solve [intros*;
               fequals~;
               case_var~];
  intros*;
  simpl;
  fequals~;
  case_var*;
  rewrite subst_open_var_v;
  simpl_classes;
  case_var*.

Lemma subst_open_var_st:
  forall (t : St), subst_open_var_prop StLangFuns t.
Proof.
  intros*.
  StEF_Var_Induction St_ind_mutual subst_open_var_prop;
  subst_open_var_proof.
Qed.

Lemma subst_open_var_e:
  forall (t : E), subst_open_var_prop ELangFuns t.
Proof.
  intros*.
  StEF_Var_Induction E_ind_mutual subst_open_var_prop;
  subst_open_var_proof.
Qed.

Lemma subst_open_var_f:
  forall (t : F), subst_open_var_prop FLangFuns t.
Proof.
  intros*.
  StEF_Var_Induction F_ind_mutual subst_open_var_prop;
  subst_open_var_proof.
Qed.

Lemma subst_open_var:
  forall (t : Term), subst_open_var_prop TermLangFuns t.
Proof.
  intros*.
  destruct t; simpl; case_var*; fequals*;
  try rewrite subst_open_var_st; 
  try rewrite subst_open_var_e;
  try rewrite subst_open_var_f;
  simpl_classes; case_var*.
Qed.

Lemma subst_bevar_id:
  forall v x y,
    subst_v x y (bevar v) = (bevar v).
Proof.
  intros.
  unfold subst_v.
  auto.
Qed.

(* Although it is just another form of subst_open_var in our case. *)
(** In particular, we can distribute [subst] on [open_var] *)

Function subst_open_prop (In : Type) (H: LangFuns Variables.var Variables.var In) :=
  fun (t : In) => 
  forall x y u n,
    x <> y ->
    y <> u ->
    subst' u x (open_rec' n y t) = open_rec' n y (subst' u x t).
Hint Unfold subst_open_prop.

Lemma subst_open_v:
  forall (t : V),  subst_open_prop VLangFuns t.
Proof.
  intros*.
  induction t.
  simpl.
  case_nat~.
  simpl.
  case_var~.
  fequals~.
  simpl.
  case_var~.
Qed.
  
Ltac subst_open_proof :=
  intros*;
  simpl;
  fequals~;
  try applys~ subst_open_v.

Lemma subst_open_st:
  forall (t : St),  subst_open_prop StLangFuns t.
Proof.
  StEF_Var_Induction St_ind_mutual subst_open_prop;
  subst_open_proof.
Qed.

Lemma subst_open_e:
  forall (t : E),  subst_open_prop ELangFuns t.
Proof.
  StEF_Var_Induction E_ind_mutual subst_open_prop;
  subst_open_proof.
Qed.

Lemma subst_open_f:
  forall (t : F),  subst_open_prop FLangFuns t.
Proof.
  StEF_Var_Induction F_ind_mutual subst_open_prop;
  subst_open_proof.
Qed.

Lemma subst_open:
  forall (t : Term),  subst_open_prop TermLangFuns t.
Proof.
  lets*: subst_open_st.
  lets*: subst_open_e.
  lets*: subst_open_f.
  destruct t; intros*; simpl; fequals*.
Qed.

(** For the distributivity of [subst] on [close_var],
    one simple intermediate lemmas is required to 
    say that closing on a fresh name is the identity *)

Function close_rec_fresh_prop (What In : Type) (H: LangFuns What Variables.var In) :=
  fun (t : In) =>
  forall x k,
    x \notin fv' t -> close_rec' k x t = t.
Hint Unfold close_rec_fresh_prop.

Lemma close_rec_fresh_v:
  forall (t : V), close_rec_fresh_prop VLangFuns t.
Proof.
  destruct t; intros*; simpls*.
  case_var~.
Qed.

Ltac close_rec_fresh_proof :=
  lets*: close_rec_fresh_v;
  simpl;
  intros;
  fequals*.

Lemma close_rec_fresh_st :
  forall (t: St), close_rec_fresh_prop StLangFuns t.
Proof.
  StEF_Induction St_ind_mutual close_rec_fresh_prop;
  close_rec_fresh_proof.
Qed.

Lemma close_rec_fresh_e :
  forall (t: E), close_rec_fresh_prop ELangFuns t.
Proof.
  StEF_Induction E_ind_mutual close_rec_fresh_prop;
  close_rec_fresh_proof.
Qed.

Lemma close_rec_fresh_f :
  forall (t: F), close_rec_fresh_prop FLangFuns t.
Proof.
  StEF_Induction F_ind_mutual close_rec_fresh_prop;
  close_rec_fresh_proof.
Qed.

Lemma close_rec_fresh :
  forall (t: Term), close_rec_fresh_prop TermLangFuns t.
Proof.
  lets*: close_rec_fresh_st.
  lets*: close_rec_fresh_e.
  lets*: close_rec_fresh_f.
  destruct t; intros*; simpl; fequals*.
Qed.

(** Distributivity of [subst] on [close_var] *)

Function subst_close_prop (In : Type) (H: LangFuns Variables.var Variables.var In) :=
  fun (t : In) => 
  forall x y u,
    x <> y ->
    y \notin fv_v (fevar u) -> 
    forall n, 
      subst' u x (close_rec' n y t) = close_rec' n y (subst' u x t).
Hint Unfold subst_close_prop.

Lemma subst_close_v:
  forall (t : V), subst_close_prop VLangFuns t.
Proof.
  intros*.
  induction t; simpl; auto.
  repeat (case_var~; simpl).
  simpl in H0.
  apply notin_singleton_r in H0.
  tryfalse.
Qed.

Ltac subst_close_proof :=
  intros*;
  simpl;
  fequals~;
  lets~ J: subst_close_v;
  auto.

Lemma subst_close_st:
  forall (t : St), subst_close_prop StLangFuns t.
Proof.
    StEF_Var_Induction St_ind_mutual subst_close_prop;
    subst_close_proof.
Qed.

Lemma subst_close_e:
  forall (t : E), subst_close_prop ELangFuns t.
Proof.
    StEF_Var_Induction E_ind_mutual subst_close_prop;
    subst_close_proof.
Qed.

Lemma subst_close_f:
  forall (t : F), subst_close_prop FLangFuns t.
Proof.
    StEF_Var_Induction F_ind_mutual subst_close_prop;
    subst_close_proof.
Qed.

Lemma subst_close_rec:
  forall (t : Term), subst_close_prop TermLangFuns t.
Proof.
  lets*: subst_close_st.
  lets*: subst_close_e.
  lets*: subst_close_f.
  destruct t; simpl; intros; fequals~.
Qed.

(** Substitution for a fresh name is the identity *)

Function subst_fresh_prop (What In : Type) (H: LangFuns What Variables.var In) :=
  fun (t : In) => 
  forall x u, 
    x \notin fv' t -> subst' u x t = t.
Hint Unfold subst_fresh_prop.

Lemma subst_fresh_v: 
  forall (t : V), subst_fresh_prop VLangFuns t.
Proof.
  intros*.
  destruct t; try solve[simpl; intros; fequals~].
  simpl in H.
  assert(x <> v).
  auto.
  simpl.
  case_var~.
Qed.

Ltac subst_fresh_proof :=
  lets*: subst_fresh_v;
  simpl;
  intros*;
  fequals*.

Lemma subst_fresh_st:
  forall (t : St), subst_fresh_prop StLangFuns t.
Proof.
    StEF_Induction St_ind_mutual subst_fresh_prop;
    subst_fresh_proof.
Qed.

Lemma subst_fresh_e:
  forall (t : E), subst_fresh_prop ELangFuns t.
Proof.
    StEF_Induction E_ind_mutual subst_fresh_prop;
    subst_fresh_proof.
Qed.

Lemma subst_fresh_f:
  forall (t : F), subst_fresh_prop FLangFuns t.
Proof.
    StEF_Induction F_ind_mutual subst_fresh_prop;
    subst_fresh_proof.
Qed.

Lemma subst_fresh : 
  forall (t : Term), subst_fresh_prop TermLangFuns t.
Proof.
  lets*: subst_fresh_st.
  lets*: subst_fresh_e.
  lets*: subst_fresh_f.
  destruct t; intros*; simpl; fequals*.
Qed.

(** Substitution can be introduced to decompose an opening *)

Function subst_intro_prop (In : Type) (H: LangFuns Variables.var Variables.var In) :=
  fun (t : In) => 
    forall x u n,
      x \notin (fv' t) -> 
      open_rec' n u t = subst' u x (open_rec' n x t).
Hint Unfold subst_intro_prop.

Lemma subst_intro_v:
  forall (t : V), subst_intro_prop VLangFuns t.
Proof.
  intros*.
  induction t; simpl; intros; fequals*.
  case_nat*.
  simpl. 
  case_var*.
  case_var*.
  simpl in H.
  invert_x_notin_x.
Qed.

Ltac subst_intro_proof := 
  lets*: subst_intro_v;
  simpl;
  intros*;
  fequals*.

Lemma subst_intro_st:
  forall (t : St), subst_intro_prop StLangFuns t.
Proof.
  StEF_Var_Induction St_ind_mutual subst_intro_prop;
  subst_intro_proof.
Qed.

Lemma subst_intro_e:
  forall (t : E), subst_intro_prop ELangFuns t.
Proof.
  StEF_Var_Induction E_ind_mutual subst_intro_prop;
  subst_intro_proof.
Qed.

Lemma subst_intro_f:
  forall (t : F), subst_intro_prop FLangFuns t.
Proof.
  StEF_Var_Induction F_ind_mutual subst_intro_prop;
  subst_intro_proof.
Qed.

Lemma subst_intro: 
  forall (t : Term), subst_intro_prop TermLangFuns t.
Proof.
  lets*: subst_intro_st.
  lets*: subst_intro_e.
  lets*: subst_intro_f.
  destruct t; simpl; intros; fequals~.
Qed.

(** An alternative, longer proof, but with fewer hypotheses *)
(* is just the same as above, lc_v (fevar _) is a tautology. *)

(** Substitution can be introduced to decompose a variable
    closing in terms of another one using a different name *)

Function close_rename_prop (In : Type) (H: LangFuns Variables.var Variables.var In) :=
  fun (t : In) => 
  forall n x y,
    x \notin fv' t ->
    close_rec' n y t =
    close_rec' n x (subst' x y t).
Hint Unfold close_rename_prop.

Lemma close_rename_v:
  forall (t : V), close_rename_prop VLangFuns t.
Proof.
  intros*.
  induction t;
  simpl;
  auto.    
  case_var~;
  simpl;
  case_var~.
  simpl in H.
  apply notin_same in H.
  contradiction.
Qed.

Ltac close_rename_proof := 
  lets*: close_rename_v;
  simpl;
  intros*; 
  fequals*.

Lemma close_rename_st:
  forall (t : St), close_rename_prop StLangFuns t.
Proof.
  StEF_Var_Induction St_ind_mutual close_rename_prop;
  close_rename_proof.
Qed.

Lemma close_rename_e:
  forall (t : E), close_rename_prop ELangFuns t.
Proof.
  StEF_Var_Induction E_ind_mutual close_rename_prop;
  close_rename_proof.
Qed.

Lemma close_rename_f:
  forall (t : F), close_rename_prop FLangFuns t.
Proof.
  StEF_Var_Induction F_ind_mutual close_rename_prop;
  close_rename_proof.
Qed.

Lemma close_rename:
    forall (t : Term), close_rename_prop TermLangFuns t.
Proof.
  lets*: close_rename_st.
  lets*: close_rename_e.
  lets*: close_rename_f.
  destruct t; intros*; simpl; fequals*.
Qed.

(* ********************************************************************** *)
(** Preservation of local closure through substitution and opening *)

(** Substitution of a locally closed terms into another one produces
    a locally closed term *)

Function subst_lc_prop 
  (What In : Type) (H: LangFuns What Variables.var In)  (L : LcJudgement In) :=
  fun (t : In) (_ : lc' t) =>
    forall x y,
      lc' (subst' x y t).
Hint Unfold subst_lc_prop.

Lemma subst_lc_v : 
  forall (t : V) (l : lc' t), subst_lc_prop VLangFuns LcVJudgement t l.
Proof.
  intros*.
  destruct t.
  inversion l.
  simpl.
  case_var*.
Qed.
  
Ltac subst_lc_proof :=
  try solve[intros*;
            simpl;
            auto;
            try case_var~];
  intros;
  try apply_fresh* lc_st_letx;
  try apply_fresh* lc_open;
  try apply_fresh* lc_openstar;
  try apply_fresh* lc_dfun;
  try rewrite <- subst_open_st; auto.

Lemma subst_lc_st:
  forall (t : St) (l : lc' t), subst_lc_prop StLangFuns LcStJudgement t l.
Proof.
  LCSt_Induction lc_st_ind_mutual subst_lc_prop;
  try solve[subst_lc_proof].
Qed.

Lemma subst_lc_e:
  forall (t : E) (l : lc' t), subst_lc_prop ELangFuns LcEJudgement t l.
Proof.
  LCSt_Induction lc_e_ind_mutual subst_lc_prop;
  subst_lc_proof.
Qed.

Lemma subst_lc_f:
  forall (t : F) (l : lc' t), subst_lc_prop FLangFuns LcFJudgement t l.
Proof.
  LCSt_Induction lc_f_ind_mutual subst_lc_prop;
  subst_lc_proof.
Qed.

Lemma subst_lc:
  forall (t : Term) (l : lc' t), subst_lc_prop TermLangFuns LcTermJudgement t l.
Proof.
  intros*.
  lets*: subst_lc_st.
  lets*: subst_lc_e.
  lets*: subst_lc_f.
  destruct t; 
  inversion l;
  simpl;
  constructor;
  auto.
Qed.

(** Substitution of a locally closed terms into a body one produces
    another body *)

Lemma subst_body:
  forall t x u,
    lc_v (fevar u) ->
    body t ->
    body (subst u x t).
Proof.
  simpl_classes.
  introv U [L H]. 
  exists_fresh.
  asserts* xney : (x <> y).
  asserts* yneu : (y <> u).
  unfold open.
  lets* M: subst_open.
  specialize (M t x y u 0 xney yneu).
  rewrite~ <- M.
  apply~ subst_lc.
Qed.

(** Opening of a body with a locally closed terms produces a 
    locally closed term *)

Lemma open_lc :
  forall t u,
    body t
    -> lc_v (fevar u)
    -> lc (open_rec 0 u t).
Proof.
  introv [L H] U.
  pick_fresh x. 
  unfold open in H.
  lets* M: (@subst_intro t x u 0).
  rewrite M.
  apply~ subst_lc. 
  auto.
Qed.

(* ====================================================================== *)
(** ** An induction principle for locally closed terms *)

(** Interaction of [size] with [open_var] *)

Function size_open_var_prop  (What In : Type) (H: LangFuns What Variables.var In) :=
  fun (t : In) =>
    forall n x,
      size' (open_rec' n x t) = size' t.
Hint Unfold size_open_var_prop.

Lemma size_open_var_v :
    forall (t : V), size_open_var_prop VLangFuns t.
Proof.
  intros*. (* nice *)
Qed.

Ltac size_open_var_proof :=
  simpl;
  intros*.

Lemma size_open_var_st:
  forall (t : St), size_open_var_prop StLangFuns t.
Proof.
  StEF_Induction St_ind_mutual size_open_var_prop;
  size_open_var_proof.
Qed.

Lemma size_open_var_e:
  forall (t : E), size_open_var_prop ELangFuns t.
Proof.
  StEF_Induction E_ind_mutual size_open_var_prop;
  size_open_var_proof.
Qed.

Lemma size_open_var_f:
  forall (t : F), size_open_var_prop FLangFuns t.
Proof.
  StEF_Induction F_ind_mutual size_open_var_prop;
  size_open_var_proof.
Qed.

Lemma size_open_rec:
  forall (t : Term), size_open_var_prop TermLangFuns t.
Proof.
  lets*: size_open_var_st.
  lets*: size_open_var_e.
  lets*: size_open_var_f.
  destruct t; simpl; intros*.
Qed.

(** Interaction of [size] with [close_var] *)

Function size_close_var_prop  (What In : Type) (H: LangFuns What Variables.var In) :=
  fun (t : In) =>
    forall x n,
      size' (close_rec' n x t) = size' t.
Hint Unfold size_close_var_prop.

Ltac size_close_var_proof :=
  simpl;
  intros*.

Lemma size_close_var_v:
  forall (t : V), size_close_var_prop VLangFuns t.
Proof.
  size_close_var_proof.
Qed.

Lemma size_close_var_st:
  forall (t : St), size_close_var_prop StLangFuns t.
Proof.
  StEF_Induction St_ind_mutual size_close_var_prop;
  size_close_var_proof.
Qed.

Lemma size_close_var_e:
  forall (t : E), size_close_var_prop ELangFuns t.
Proof.
  StEF_Induction E_ind_mutual size_close_var_prop;
  size_close_var_proof.
Qed.

Lemma size_close_var_f:
  forall (t : F), size_close_var_prop FLangFuns t.
Proof.
  StEF_Induction F_ind_mutual size_close_var_prop;
  size_close_var_proof.  
Qed.

Lemma size_close_var:
  forall (t : Term), size_close_var_prop TermLangFuns t.
Proof.
  lets*: size_close_var_st.
  lets*: size_close_var_e.
  lets*: size_close_var_f.
  destruct t; simpl; intros*.
Qed.

(** The induction principle on size is not needed. *)
(* This would be very large, three induction principles. *)
(* And the only thing Dan seems to induct on is the length of a context,
  not its full size. So unless I need this I won't make it. *)

End TMP.

