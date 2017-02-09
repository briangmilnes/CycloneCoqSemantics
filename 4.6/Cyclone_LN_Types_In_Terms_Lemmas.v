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
Import TMP.
Import TTM.
(* This is the version just for the lemmas manipulating types in terms. *)
Module TTMP. (* T = Types TM = Term P = Proof. *)

(* With the new typeclass based propositions, you'll find some of them in the 
Terms lemmas. *)

(* ====================================================================== *)
(** ** Proofs *)

(* ********************************************************************** *)
(** Variable closing and variable opening are reciprocal of one another *)

(** Showing that [close_var] after [open_var] is the identity is easy *)

Function close_open_prop (In : Type) (H: LangFuns Tau Tau In) :=
  fun (t : In) =>
  forall (x : Variables.var) (n : nat),
    x \notin fv' t -> 
    close_rec' n x (open_rec' n (ftvar x) t) = t.
Hint Unfold close_open_prop.

Lemma close_open_v :
  forall (t : V), close_open_prop TauTermVLangFuns t.
Proof.
  introv.
  induction t; simpl; introv Fr; fequals~.
Qed.

Ltac close_open_proof :=
  simpl;
  intros*;
  fequals~;
  try applys* close_open_v;
  try case_nat~;
  simpl;
  try case_var~;
  try case_var~.

Lemma close_open_st:
  forall (t : St), close_open_prop TauTermStLangFuns t.
Proof.
  StEF_Tau_Induction Tau_St_ind_mutual close_open_prop;
  close_open_proof.
Qed.

Lemma close_open_e:
  forall (t : E), close_open_prop TauTermELangFuns t.
Proof.
  StEF_Tau_Induction Tau_E_ind_mutual close_open_prop;
  close_open_proof.
Qed.

Lemma close_open_f:
  forall (t : F), close_open_prop TauTermFLangFuns t.
Proof.
  StEF_Tau_Induction Tau_F_ind_mutual close_open_prop;
  close_open_proof.
Qed.

Lemma close_open_tau:
  forall (t : Tau), close_open_prop TauTermTauLangFuns t.
Proof.
  StEF_Tau_Induction Tau_Tau_ind_mutual close_open_prop;
  close_open_proof.
Qed.

Lemma close_open :
  forall (t : Term), close_open_prop TauTermLangFuns t.
Proof.
  lets*: close_open_st.
  lets*: close_open_e.
  lets*: close_open_f.
  lets*: close_open_tau.
  destruct t; simpl; intros; fequals*.
Qed.

(** The other direction is much harder; First, we first need
    to establish the injectivity of [open_var] *)

Function open_rec_inj_prop (In : Type) (H: LangFuns Tau Tau In) :=
  fun (t1 t2 : In) =>
    forall n alpha,
      alpha \notin (fv' t1) ->
      alpha \notin (fv' t2) -> 
      open_rec' n (ftvar alpha) t1 = open_rec' n (ftvar alpha) t2 ->
      (t1 = t2).
Hint Unfold open_rec_inj_prop.

Lemma open_rec_inj_v:
  forall (t1 t2 : V), open_rec_inj_prop TauTermVLangFuns t1 t2.
Proof.
  intros*.
Qed.

Ltac open_rec_inj_proof t1 t2 alpha n T H1:=
  intros*;
  rewrite* <- (@T t1 alpha n);
  rewrite* <- (@T t2 alpha n);
  rewrite* H1.

Lemma open_rec_inj_st:
  forall (t1 t2 : St), open_rec_inj_prop TauTermStLangFuns t1 t2.
Proof.
  open_rec_inj_proof t1 t2 alpha n close_open_st H1.
Qed.

Lemma open_rec_inj_e:
  forall (t1 t2 : E), open_rec_inj_prop TauTermELangFuns t1 t2.
Proof.
  open_rec_inj_proof t1 t2 alpha n close_open_e H1.
Qed.

Lemma open_rec_inj_f:
  forall (t1 t2: F), open_rec_inj_prop TauTermFLangFuns t1 t2.
Proof.
  open_rec_inj_proof t1 t2 alpha n close_open_f H1.
Qed.

Lemma open_rec_inj_tau:
  forall (t1 t2: Tau), open_rec_inj_prop TauTermTauLangFuns t1 t2.
Proof.
  open_rec_inj_proof t1 t2 alpha n close_open_tau H1.
Qed.

Lemma open_rec_st_inj :
  forall (t1 t2: Term), open_rec_inj_prop TauTermLangFuns t1 t2.
Proof.
  intros*.
  open_rec_inj_proof t1 t2 alpha n close_open H1.  
Qed.

(** We also need one (tricky) auxiliary lemma to handle the binder case *)

Function open_close_var_on_open_var_prop (In : Type) (H: LangFuns Tau Tau In) :=
  fun (t : In) =>
  forall alpha beta gamma i j,
    i <> j ->
    beta <> alpha ->
    beta \notin (fv' t) ->
    open_rec' i (ftvar beta) (open_rec' j (ftvar gamma) (close_rec' j alpha t))
  = open_rec' j (ftvar gamma) (close_rec' j alpha (open_rec' i (ftvar beta) t)).
Hint Unfold open_close_var_on_open_var_prop.

Lemma open_close_var_on_open_var_v:
  forall (t : V), open_close_var_on_open_var_prop TauTermVLangFuns t.
Proof.
  intros*.
Qed.

Ltac open_close_var_on_open_var_proof :=
  try solve[simpl; intros*; try solve [ fequals~ ]];
  try repeat (simpl; intros*; try case_nat*; try case_var*).

Lemma open_close_var_on_open_var_st:
  forall (t : St), open_close_var_on_open_var_prop TauTermStLangFuns t.
Proof.
  StEF_Tau_Induction Tau_St_ind_mutual open_close_var_on_open_var_prop;
  open_close_var_on_open_var_proof.
Qed.

Lemma open_close_var_on_open_var_e:
  forall (t : E), open_close_var_on_open_var_prop TauTermELangFuns t.
Proof.
  StEF_Tau_Induction Tau_E_ind_mutual open_close_var_on_open_var_prop;
  open_close_var_on_open_var_proof.
Qed.

Lemma open_close_var_on_open_var_f:
  forall (t : F), open_close_var_on_open_var_prop TauTermFLangFuns t.
Proof.
  StEF_Tau_Induction Tau_F_ind_mutual open_close_var_on_open_var_prop;
  open_close_var_on_open_var_proof.
Qed.

Lemma open_close_var_on_open_var_tau:
  forall (t : Tau), open_close_var_on_open_var_prop TauTermTauLangFuns t.
Proof.
  StEF_Tau_Induction Tau_Tau_ind_mutual open_close_var_on_open_var_prop;
  open_close_var_on_open_var_proof.
Qed.

Lemma open_close_var_on_open_var:
  forall (t : Term), open_close_var_on_open_var_prop TauTermLangFuns t.
Proof.
  intros*.
  lets*: open_close_var_on_open_var_st.
  lets*: open_close_var_on_open_var_e.
  lets*: open_close_var_on_open_var_f.
  lets*: open_close_var_on_open_var_tau.
  destruct t; simpl; intros*; fequals*.
Qed.

(** Now we can prove that [open_var] after [close_var] is the identity *)

Function open_close_var_prop
   (In : Type) (H: LangFuns Tau Tau In) (L : LcJudgement In) :=
  fun (t : In) (_ : lc' t) =>
  forall alpha n, 
    open_rec' n (ftvar alpha) (close_rec' n alpha t)  = t.
Hint Unfold open_close_var_prop.

Lemma open_close_var_v:
 forall (t : V) (l : lc' t), open_close_var_prop TauTermVLangFuns LcVJudgement t l.
Proof.
  intros*.
Qed.

Ltac invert_lc_btvar :=
  match goal with
    | H : T.lc (btvar _) |- _  => inversion H
  end.

Hint Extern 1 (T.lc (btvar _)) => (* idtac "(T.lc (btvar _))";*) trace_goal; invert_lc_btvar.

Ltac inversion_on_lc :=
  match goal with
    | H : T.lc (_ _)    |- _ => inversions~ H
    | H : T.lc (_ _ _)    |- _ => inversions~ H
    | H : TTM.lc (_ _)    |- _ => inversions~ H
    | H : TTM.lc (_ _ _)    |- _ => inversions~ H
end.

Hint Extern 1 (T.lc (_ _)) => inversion_on_lc.
Hint Extern 1 (T.lc (_ _ _)) => inversion_on_lc.

Ltac open_close_var_proof t :=
  intros*;
  lets: open_close_var_v;
  lets~ M: TP.open_close_var;
  try solve[simpl; intros; fequals~];
  simpl;
  intros;
  fequals~;
  try induction t; simpl; intros; fequals~;
  try solve[case_var~; simpl; case_nat~].

Lemma open_close_var_st:
 forall (t : St) (l : lc' t), open_close_var_prop TauTermStLangFuns LcTauStJudgement t l.
Proof.
  LCSt_Tau_Induction lc_st_ind_mutual open_close_var_prop;
  open_close_var_proof t.
Qed.

Lemma open_close_var_e:
 forall (t : E) (l : lc' t), open_close_var_prop TauTermELangFuns LcTauEJudgement t l.
Proof.
  LCSt_Tau_Induction lc_e_ind_mutual open_close_var_prop;
  open_close_var_proof t.
Qed.

Lemma open_close_var_f:
 forall (t : F) (l : lc' t), open_close_var_prop TauTermFLangFuns LcTauFJudgement t l.
Proof.
  LCSt_Tau_Induction lc_f_ind_mutual open_close_var_prop;
  open_close_var_proof t.
Qed.

Lemma open_close_var:
 forall (t : Term) (l : lc' t), open_close_var_prop TauTermLangFuns LcTauTermJudgement t l.
Proof.
  lets*: open_close_var_st.
  lets*: open_close_var_e.
  lets*: open_close_var_f.
  destruct t; intros; inversion l; intros; simpl; fequals*.
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
  rewrite~ <- (@open_close_var t1 T1 alpha 0).
  rewrite~ <- (@open_close_var t2 T2 alpha 0).
  fequals~.
Qed.

(* ********************************************************************** *)
(** Interaction of [fv] with [open_var] and [close_var] *)

(** Opening with [u] adds [fv u] to the set of free variables *)


Function fv_open_prop (In : Type) (H: LangFuns Tau Tau In) := 
  fun (t : In) =>
  forall (u : var) (n: nat),
    fv' (open_rec' n (ftvar u) t) \c  fv' t \u \{u}.
Hint Unfold fv_open_prop.

Lemma fv_open_v:
  forall (t : V), fv_open_prop TauTermVLangFuns t.
Proof.
  intros*.
  destruct t; simpl; try case_nat; simpl; fset.
Qed.

Ltac fv_open_proof := 
  simpl;
  intros*;
  try case_nat*;
  fset.

Lemma fv_open_st:
  forall (t: St), fv_open_prop TauTermStLangFuns t.
Proof.
  intros*.
  StEF_Tau_Induction Tau_St_ind_mutual fv_open_prop;
  fv_open_proof.
Qed.

Lemma fv_open_e:
  forall (t: E), fv_open_prop TauTermELangFuns t.
Proof.
  intros*.
  StEF_Tau_Induction Tau_E_ind_mutual fv_open_prop;
  fv_open_proof.
Qed.

Lemma fv_open_f:
  forall (t: F), fv_open_prop TauTermFLangFuns t.
Proof.
  intros*.
  StEF_Tau_Induction Tau_F_ind_mutual fv_open_prop;
  fv_open_proof.
Qed.

Lemma fv_open_tau:
  forall (t: Tau), fv_open_prop TauTermTauLangFuns t.
Proof.
  intros*.
  StEF_Tau_Induction Tau_Tau_ind_mutual fv_open_prop;
  fv_open_proof.
Qed.

Lemma fv_open : forall t u,
  fv (open (ftvar u) t) \c fv t \u \{u}.
Proof.
  lets*: fv_open_st.
  lets*: fv_open_e.
  lets*: fv_open_f.
  lets*: fv_open_tau.
  destruct t; simpl; intros*.
Qed.

(** In particular, opening with variable [x] adds [x] to the set 
    of free variables *)

Function open_var_fv_prop (In : Type) (H: LangFuns Tau Tau In) := 
  fun (t : In) =>
    forall alpha,
      fv' (open_rec' 0 (ftvar alpha) t) \c (fv' t \u \{alpha}).
Hint Unfold open_var_fv_prop.

Lemma open_var_fv_v:
  forall (t : V), open_var_fv_prop TauTermVLangFuns t.
Proof.
  lets*:fv_open_v. 
Qed.

Lemma open_var_fv_st:
  forall (t : St), open_var_fv_prop TauTermStLangFuns t.
Proof.
  lets*:fv_open_st.
Qed.

Lemma open_var_fv_e:
  forall (t : E), open_var_fv_prop TauTermELangFuns t.
Proof.
  lets*:fv_open_e.
Qed.

Lemma open_var_fv_f:
  forall (t : F), open_var_fv_prop TauTermFLangFuns t.
Proof.
  lets*:fv_open_f.
Qed.

Lemma open_var_fv_tau:
  forall (t : Tau), open_var_fv_prop TauTermTauLangFuns t.
Proof.
  lets*:fv_open_tau.
Qed.

Lemma open_var_fv : 
  forall (t : Term), open_var_fv_prop TauTermLangFuns t.
Proof.
  lets*: fv_open.
Qed.

(** Closing w.r.t variable [x] removes [x] from the set of free variables *)

Function close_var_fv_prop (In : Type) (H: LangFuns Tau Tau In) := 
  fun (t : In) =>
    forall alpha n,
      fv' (close_rec' n alpha t) \c (fv' t \- \{alpha}).
Hint Unfold close_var_fv_prop.

Lemma close_var_fv_v:
  forall (t : V), close_var_fv_prop TauTermVLangFuns t.
Proof.
  intros*.
  destruct t; simpl; fset.
Qed.

Ltac close_var_fv_proof :=
  lets*: close_var_fv_v;
  lets*: TP.close_fv;
  simpl;
  intros;
  try case_var*;
  try fset.

Lemma close_var_fv_st:
  forall (t : St), close_var_fv_prop TauTermStLangFuns t.
Proof.
  StEF_Tau_Induction Tau_St_ind_mutual close_var_fv_prop;
  close_var_fv_proof.
Qed.

Lemma close_var_fv_e:
  forall (t : E), close_var_fv_prop TauTermELangFuns t.
Proof.
  StEF_Tau_Induction Tau_E_ind_mutual close_var_fv_prop;
  close_var_fv_proof.
Qed.

Lemma close_var_fv_f:
  forall (t : F), close_var_fv_prop TauTermFLangFuns t.
Proof.
  StEF_Tau_Induction Tau_F_ind_mutual close_var_fv_prop;
  close_var_fv_proof.
Qed.

Lemma close_var_fv_tau:
  forall (t : Tau), close_var_fv_prop TauTermTauLangFuns t.
Proof.
  StEF_Tau_Induction Tau_Tau_ind_mutual close_var_fv_prop;
  close_var_fv_proof.
Qed.

Lemma close_var_fv : 
  forall (t : Term), close_var_fv_prop TauTermLangFuns t.
Proof.
  lets*: close_var_fv_st.
  lets*: close_var_fv_e.
  lets*: close_var_fv_f.
  lets*: close_var_fv_tau.
  destruct t; simpl; intros*.
Qed.

(* ********************************************************************** *)
(** Properties of substitution *)

(** Distributivity of [subst] on [open].
    Two (tricky) intermediate lemmas are required *)

Function open_rec_lc_ind_prop (In : Type) (H: LangFuns Tau Tau In) := 
  fun (t : In) =>
  forall j v i u,
    i <> j ->
    open_rec' i u (open_rec' j v t) = open_rec' j v t ->
    open_rec' i u t = t.
Hint Unfold open_rec_lc_ind_prop.

Lemma open_rec_lc_ind_v:
  forall (t : V), open_rec_lc_ind_prop TauTermVLangFuns t.
Proof.
  intros*.
Qed.

Ltac open_rec_lc_ind_proof :=
  lets*: open_rec_lc_ind_v;
  lets*: TP.close_fv;
  simpl;
  intros*;
  try inversion_on_equated_constructors;
  fequals*;
  try repeat case_nat*.

Lemma open_rec_lc_ind_st:
  forall (t : St), open_rec_lc_ind_prop TauTermStLangFuns t.
Proof.
  StEF_Tau_Induction Tau_St_ind_mutual open_rec_lc_ind_prop;
  open_rec_lc_ind_proof.
Qed.

Lemma open_rec_lc_ind_e:
  forall (t : E), open_rec_lc_ind_prop TauTermELangFuns t.
Proof.
  StEF_Tau_Induction Tau_E_ind_mutual open_rec_lc_ind_prop;
  open_rec_lc_ind_proof.
Qed.

Lemma open_rec_lc_ind_f:
  forall (t : F), open_rec_lc_ind_prop TauTermFLangFuns t.
Proof.
  StEF_Tau_Induction Tau_F_ind_mutual open_rec_lc_ind_prop;
  open_rec_lc_ind_proof.
Qed.

Lemma open_rec_lc_ind_tau:
  forall (t : Tau), open_rec_lc_ind_prop TauTermTauLangFuns t.
Proof.
  StEF_Tau_Induction Tau_Tau_ind_mutual open_rec_lc_ind_prop;
  open_rec_lc_ind_proof.
Qed.

Lemma open_rec_lc_ind: 
  forall (t : Term), open_rec_lc_ind_prop TauTermLangFuns t.
Proof.
  lets*: open_rec_lc_ind_st.
  lets*: open_rec_lc_ind_e.
  lets*: open_rec_lc_ind_f.
  lets*: open_rec_lc_ind_tau.
  destruct t;
  simpl;
  intros*; 
  try inversion_on_equated_constructors;
  fequals*.
Qed.

Function open_rec_lc_prop 
   (In : Type) (H: LangFuns Tau Tau In) (L : LcJudgement In) :=
  fun (t : In) (_ : lc' t) =>
    forall u k,
      open_rec' k u t = t.
Hint Unfold open_rec_lc_prop.

Lemma open_rec_lc_v: 
  forall (t : V) (l : lc' t), open_rec_lc_prop TauTermVLangFuns LcTauVJudgement t l.
Proof.
  destruct t; intros; simpls~.
Qed.

Ltac open_rec_lc_proof := 
  lets: open_rec_lc_v;
  lets: TP.open_rec_lc;
  intros*;
  simpl; 
  fequals~.

Lemma open_rec_lc_st: 
  forall (t : St) (l : lc' t), open_rec_lc_prop TauTermStLangFuns LcTauStJudgement t l.
Proof.
  LCSt_Tau_Induction lc_st_ind_mutual open_rec_lc_prop;
  open_rec_lc_proof.
Qed.

Lemma open_rec_lc_e: 
  forall (t : E) (l : lc' t), open_rec_lc_prop TauTermELangFuns LcTauEJudgement t l.
Proof.
  LCSt_Tau_Induction lc_e_ind_mutual open_rec_lc_prop;
  open_rec_lc_proof.
Qed.

Lemma open_rec_lc_f: 
  forall (t : F) (l : lc' t), open_rec_lc_prop TauTermFLangFuns LcTauFJudgement t l.
Proof.
  LCSt_Tau_Induction lc_f_ind_mutual open_rec_lc_prop;
  open_rec_lc_proof.
Qed.

Lemma open_rec_lc : 
  forall (t : Term) (l : lc' t), open_rec_lc_prop TauTermLangFuns LcTauTermJudgement t l.
Proof.
  lets*: open_rec_lc_st.
  lets*: open_rec_lc_e.
  lets*: open_rec_lc_f.
  destruct t; intros; simpl; inversion l; fequals~.
Qed.

Function subst_open_prop (In : Type) (H: LangFuns Tau Tau In) :=
  fun (t : In) =>
  forall alpha u v n, 
    T.lc u ->
    subst' u alpha (open_rec' n v t) = 
    open_rec' n (T.subst u alpha v) (subst' u alpha t).
Hint Unfold subst_open_prop.

Lemma subst_open_v:
  forall (t : V), subst_open_prop TauTermVLangFuns t.
Proof.
  intros*.
Qed.

Ltac subst_open_proof :=
  intros*;
  lets: TP.subst_open_rec;
  intros*; simpl; fequals~.

Lemma subst_open_st:
  forall (t : St), subst_open_prop TauTermStLangFuns t.
Proof.
  StEF_Tau_Induction Tau_St_ind_mutual subst_open_prop;
  subst_open_proof.
Qed.

Lemma subst_open_e:
  forall (t : E), subst_open_prop TauTermELangFuns t.
Proof.
  StEF_Tau_Induction Tau_E_ind_mutual subst_open_prop;
  subst_open_proof.
Qed.

Lemma subst_open_f:
  forall (t : F), subst_open_prop TauTermFLangFuns t.
Proof.
  StEF_Tau_Induction Tau_F_ind_mutual subst_open_prop;
  subst_open_proof.
Qed.

Lemma subst_open_tau:
  forall (t : Tau), subst_open_prop TauTermTauLangFuns t.
Proof.
  StEF_Tau_Induction Tau_Tau_ind_mutual subst_open_prop;
  subst_open_proof.
Qed.

Lemma subst_open:
  forall (t : Term), subst_open_prop TauTermLangFuns t.
Proof.
  lets*: subst_open_st.
  lets*: subst_open_e.
  lets*: subst_open_f.
  lets*: subst_open_tau.
  destruct t;
  simpl;
  intros;
  fequals~.
Qed.

(** In particular, we can distribute [subst] on [open_var] *)

Function subst_open_var_prop (In : Type) (H: LangFuns Tau Tau In) :=
  fun (t : In) =>
  forall alpha beta u, 
    alpha <> beta ->
    T.lc u -> 
    subst' u alpha (open_rec' 0 (ftvar beta) t) =
    open_rec' 0 (ftvar beta) (subst' u alpha t).
Hint Unfold subst_open_var_prop.

Lemma subst_open_var_v:
  forall (t : V), subst_open_var_prop TauTermVLangFuns t.
Proof.
  intros*.
Qed.

Ltac subst_open_var_proof:=
  intros*;
  try rewrite~ subst_open_st;
  try rewrite~ subst_open_e;
  try rewrite~ subst_open_f;
  try rewrite~ subst_open_tau;
  try rewrite~ subst_open;
  fequals;
  simpl;
  case_var~.

Lemma subst_open_var_st:
  forall (t : St), subst_open_var_prop TauTermStLangFuns t.
Proof.
  subst_open_var_proof.
Qed.

Lemma subst_open_var_e:
  forall (t : E), subst_open_var_prop TauTermELangFuns t.
Proof.
  subst_open_var_proof.
Qed.

Lemma subst_open_var_f:
  forall (t : F), subst_open_var_prop TauTermFLangFuns t.
Proof.
  subst_open_var_proof.
Qed.

Lemma subst_open_var_tau:
  forall (t : Tau), subst_open_var_prop TauTermTauLangFuns t.
Proof.
  subst_open_var_proof.
Qed.

Lemma subst_open_var:
  forall (t : Term), subst_open_var_prop TauTermLangFuns t.
Proof.
  subst_open_var_proof.
Qed.

(** For the distributivity of [subst] on [close_var],
    one simple intermediate lemmas is required to 
    say that closing on a fresh name is the identity *)

Function close_var_rec_fresh_prop (In : Type) (H: LangFuns Tau Tau In) :=
  fun (t : In) =>
  forall alpha k,
    alpha \notin fv' t -> close_rec' k alpha t = t.
Hint Unfold close_var_rec_fresh_prop.

Lemma close_var_rec_fresh_v:
  forall (t : V), close_var_rec_fresh_prop TauTermVLangFuns t.
Proof.
  intros*.
Qed.

Ltac close_var_rec_fresh_proof :=
  lets*: close_var_rec_fresh_v;
  lets*: TP.close_rec_fresh;
  simpl;
  intros*;
  fequals~.  

Lemma close_var_rec_fresh_st:
  forall (t : St), close_var_rec_fresh_prop TauTermStLangFuns t.
Proof.
  StEF_Tau_Induction Tau_St_ind_mutual close_var_rec_fresh_prop;
  close_var_rec_fresh_proof.
Qed.

Lemma close_var_rec_fresh_e:
  forall (t : E), close_var_rec_fresh_prop TauTermELangFuns t.
Proof.
  StEF_Tau_Induction Tau_E_ind_mutual close_var_rec_fresh_prop;
  close_var_rec_fresh_proof.
Qed.

Lemma close_var_rec_fresh_f:
  forall (t : F), close_var_rec_fresh_prop TauTermFLangFuns t.
Proof.
  StEF_Tau_Induction Tau_F_ind_mutual close_var_rec_fresh_prop;
  close_var_rec_fresh_proof.
Qed.

Lemma close_var_rec_fresh_tau:
  forall (t : Tau), close_var_rec_fresh_prop TauTermTauLangFuns t.
Proof.
  StEF_Tau_Induction Tau_Tau_ind_mutual close_var_rec_fresh_prop;
  close_var_rec_fresh_proof.
Qed.

Lemma close_rec_fresh:
  forall (t : Term), close_var_rec_fresh_prop TauTermLangFuns t.
Proof.
  lets*: close_var_rec_fresh_st.
  lets*: close_var_rec_fresh_e.
  lets*: close_var_rec_fresh_f.
  lets*: close_var_rec_fresh_tau.
  destruct t; simpl; intros; fequals~.
Qed.

(** Distributivity of [subst] on [close_var] *)

Function subst_close_var_prop (In : Type) (H: LangFuns Tau Tau In) :=
  fun (t : In) =>
  forall (alpha beta : var) (u : Tau),
    alpha <> beta ->
    beta \notin T.fv u ->
    forall n, 
      subst' u alpha (close_rec' n beta t) = 
      close_rec' n beta (subst' u alpha t).
Hint Unfold subst_close_var_prop.

Lemma subst_close_var_v:
  forall (t : V), subst_close_var_prop TauTermVLangFuns t.
Proof.
  intros*.
Qed.

Ltac subst_close_var_proof :=
  lets*: TP.subst_close_rec;
  simpl;
  intros*;
  fequals~.

Lemma subst_close_var_st:
  forall (t : St), subst_close_var_prop TauTermStLangFuns t.
Proof.
  StEF_Tau_Induction Tau_St_ind_mutual subst_close_var_prop;
  subst_close_var_proof.
Qed.

Lemma subst_close_var_e:
  forall (t : E), subst_close_var_prop TauTermELangFuns t.
Proof.
  StEF_Tau_Induction Tau_E_ind_mutual subst_close_var_prop;
  subst_close_var_proof.
Qed.

Lemma subst_close_var_f:
  forall (t : F), subst_close_var_prop TauTermFLangFuns t.
Proof.
  StEF_Tau_Induction Tau_F_ind_mutual subst_close_var_prop;
  subst_close_var_proof.
Qed.

Lemma subst_close_var_tau:
  forall (t : Tau), subst_close_var_prop TauTermTauLangFuns t.
Proof.
  StEF_Tau_Induction Tau_Tau_ind_mutual subst_close_var_prop;
  subst_close_var_proof.
Qed.

Lemma subst_close_var_fresh:
  forall (t : Term), subst_close_var_prop TauTermLangFuns t.
Proof.
  lets*: subst_close_var_st.
  lets*: subst_close_var_e.
  lets*: subst_close_var_f.
  lets*: subst_close_var_tau.
  destruct t; simpl; intros; fequals~.
Qed.

(** Substitution for a fresh name is the identity *)

Function subst_fresh_prop (In : Type) (H: LangFuns Tau Tau In) :=
  fun (t : In) =>
    forall alpha u, 
    alpha \notin fv' t -> subst' u alpha t = t.
Hint Unfold subst_fresh_prop.

Lemma subst_fresh_v:
  forall (t : V), subst_fresh_prop TauTermVLangFuns t.
Proof.
  intros*.
Qed.

Ltac subst_fresh_proof :=
  lets*: subst_fresh;
  lets*: TP.subst_fresh;
  simpl;
  intros;
  fequals~.

Lemma subst_fresh_st:
  forall (t : St), subst_fresh_prop TauTermStLangFuns t.
Proof.
  StEF_Tau_Induction Tau_St_ind_mutual subst_fresh_prop;
  subst_fresh_proof.
Qed.

Lemma subst_fresh_e:
  forall (t : E), subst_fresh_prop TauTermELangFuns t.
Proof.
  StEF_Tau_Induction Tau_E_ind_mutual subst_fresh_prop;
  subst_fresh_proof.
Qed.

Lemma subst_fresh_f:
  forall (t : F), subst_fresh_prop TauTermFLangFuns t.
Proof.
  StEF_Tau_Induction Tau_F_ind_mutual subst_fresh_prop;
  subst_fresh_proof.
Qed.

Lemma subst_fresh_tau:
  forall (t : Tau), subst_fresh_prop TauTermTauLangFuns t.
Proof.
  StEF_Tau_Induction Tau_Tau_ind_mutual subst_fresh_prop;
  subst_fresh_proof.
Qed.

Lemma subst_fresh :
  forall (t : Term), subst_fresh_prop TauTermLangFuns t.
Proof.
  lets*: subst_fresh_st.
  lets*: subst_fresh_e.
  lets*: subst_fresh_f.
  lets*: subst_fresh_tau.
  destruct t; simpl; intros; fequals~.
Qed.

(** Substitution can be introduced to decompose an opening *)

Function subst_intro_prop (In : Type) (H: LangFuns Tau Tau In) (L : LcJudgement In) :=
 fun (t : In) =>
   forall alpha u n, 
     alpha \notin (fv' t) -> 
     T.lc u -> 
     open_rec' n u t = subst' u alpha (open_rec' n (ftvar alpha) t).
Hint Unfold subst_intro_prop.

Lemma subst_intro_v:
  forall (t : V), subst_intro_prop TauTermVLangFuns LcVJudgement t.
Proof.
  intros*.
Qed.

Ltac subst_intro_proof :=
  intros*;
  try rewrite~ subst_open_st;
  try rewrite~ subst_open_e;
  try rewrite~ subst_open_f;
  try rewrite~ subst_open_tau;
  fequals;
  simpl;
  try case_var*;
  try rewrite~ subst_fresh_st;
  try rewrite~ subst_fresh_e;
  try rewrite~ subst_fresh_f;
  try rewrite~ subst_fresh_tau.

Lemma subst_intro_st:
  forall (t : St), subst_intro_prop TauTermStLangFuns LcStJudgement t.
Proof.
  subst_intro_proof.
Qed.

Lemma subst_intro_e:
  forall (t : E), subst_intro_prop TauTermELangFuns LcEJudgement t.
Proof.
  subst_intro_proof.
Qed.

Lemma subst_intro_f:
  forall (t : F), subst_intro_prop TauTermFLangFuns LcFJudgement t.
Proof.
  subst_intro_proof.
Qed.

Lemma subst_intro_tau:
  forall (t : Tau), subst_intro_prop TauTermTauLangFuns LcTauJudgement t.
Proof.
  subst_intro_proof.
Qed.

Lemma subst_intro :
  forall (t : Term), subst_intro_prop TauTermLangFuns LcTermJudgement t.
Proof.
  lets*: subst_intro_st.
  lets*: subst_intro_e.
  lets*: subst_intro_f.
  lets*: subst_intro_tau.
  destruct t; simpl; intros; fequals~.
Qed.

(** An alternative, longer proof, but with fewer hypotheses *)

Function subst_intro_alternative_prop (In : Type) (H: LangFuns Tau Tau In) :=
 fun (t : In) =>
   forall alpha  u n, 
     alpha \notin (fv' t) -> 
     open_rec' n u t = subst' u alpha (open_rec' n (ftvar alpha) t).
Hint Unfold subst_intro_alternative_prop.

Lemma subst_intro_alternative_v:
  forall (t : V), subst_intro_alternative_prop TauTermVLangFuns t.
Proof.
  intros*.
Qed.

Ltac subst_intro_alternative_proof := 
  lets*: TP.subst_intro_alternative;
  simpl;
  intros;
  fequals~.

Lemma subst_intro_alternative_st:
  forall (t : St), subst_intro_alternative_prop TauTermStLangFuns t.
Proof.
  StEF_Tau_Induction Tau_St_ind_mutual subst_intro_alternative_prop;
  subst_intro_alternative_proof.
Qed.

Lemma subst_intro_alternative_e:
  forall (t : E), subst_intro_alternative_prop TauTermELangFuns t.
Proof.
  StEF_Tau_Induction Tau_E_ind_mutual subst_intro_alternative_prop;
  subst_intro_alternative_proof.
Qed.

Lemma subst_intro_alternative_f:
  forall (t : F), subst_intro_alternative_prop TauTermFLangFuns t.
Proof.
  StEF_Tau_Induction Tau_F_ind_mutual subst_intro_alternative_prop;
  subst_intro_alternative_proof.
Qed.

Lemma subst_intro_alternative_tau:
  forall (t : Tau), subst_intro_alternative_prop TauTermTauLangFuns t.
Proof.
  StEF_Tau_Induction Tau_Tau_ind_mutual subst_intro_alternative_prop;
  subst_intro_alternative_proof.
Qed.

Lemma subst_intro_alternative :
  forall (t : Term), subst_intro_alternative_prop TauTermLangFuns t.
Proof.
  lets*: subst_intro_alternative_st.
  lets*: subst_intro_alternative_e.
  lets*: subst_intro_alternative_f.
  lets*: subst_intro_alternative_tau.
  destruct t; simpl; intros; fequals~.
Qed.

(** Substitution can be introduced to decompose a variable
    closing in terms of another one using a different name *)

Function close_var_rename_prop (In : Type) (H: LangFuns Tau Tau In) :=
 fun (t : In) =>
  forall alpha beta n,
    alpha \notin fv' t ->
    close_rec' n beta t =
    close_rec' n alpha (subst' (ftvar alpha) beta t).
Hint Unfold close_var_rename_prop.

Lemma close_var_rename_v:
  forall (t : V), close_var_rename_prop TauTermVLangFuns t.
Proof.
  intros*.
Qed.

Ltac close_var_rename_proof := 
  simpl;
  intros;
  fequals~;
  simpl;
  intros*;
  repeat (try case_var*; simpl).

Lemma close_var_rename_st:
  forall (t : St), close_var_rename_prop TauTermStLangFuns t.
Proof.
  StEF_Tau_Induction Tau_St_ind_mutual close_var_rename_prop;
  close_var_rename_proof.
Qed.

Lemma close_var_rename_e:
  forall (t : E), close_var_rename_prop TauTermELangFuns t.
Proof.
  StEF_Tau_Induction Tau_E_ind_mutual close_var_rename_prop;
  close_var_rename_proof.
Qed.

Lemma close_var_rename_f:
  forall (t : F), close_var_rename_prop TauTermFLangFuns t.
Proof.
  StEF_Tau_Induction Tau_F_ind_mutual close_var_rename_prop;
  close_var_rename_proof.
Qed.

Lemma close_var_rename_tau:
  forall (t : Tau), close_var_rename_prop TauTermTauLangFuns t.
Proof.
  StEF_Tau_Induction Tau_Tau_ind_mutual close_var_rename_prop;
  close_var_rename_proof.
Qed.

Lemma close_var_rename :
  forall (t : Term), close_var_rename_prop TauTermLangFuns t.
Proof.
  lets*: close_var_rename_st.
  lets*: close_var_rename_e.
  lets*: close_var_rename_f.
  lets*: close_var_rename_tau.
  destruct t; simpl; intros; fequals~.
Qed.

(* ********************************************************************** *)
(** Preservation of local closure through substitution and opening *)

(** Substitution of a locally closed terms into another one produces
    a locally closed term *)

Function subst_lc_prop (In : Type) (H: LangFuns Tau Tau In) (L : LcJudgement In) :=
  fun (t : In) (_ : lc' t) =>
  forall alpha u,
    T.lc u -> lc' (subst' u alpha t).
Hint Unfold subst_lc_prop.

Lemma subst_lc_v:
 forall (t : V) (l : lc' t), subst_lc_prop TauTermVLangFuns LcVJudgement t l.
Proof.
  intros*.
Qed.

Ltac subst_lc_proof :=
  simpl;
  intros*;
  fequals~;
  lets: TP.subst_lc;
  constructor~.

Lemma subst_lc_st:
 forall (t : St) (l : lc' t), subst_lc_prop TauTermStLangFuns LcTauStJudgement t l.
Proof.
  LCSt_Tau_Induction lc_st_ind_mutual subst_lc_prop;
  subst_lc_proof.
Qed.

Lemma subst_lc_e:
 forall (t : E) (l : lc' t), subst_lc_prop TauTermELangFuns LcTauEJudgement t l.
Proof.
  LCSt_Tau_Induction lc_e_ind_mutual subst_lc_prop;
  subst_lc_proof.
Qed.

Lemma subst_lc_f:
 forall (t : F) (l : lc' t), subst_lc_prop TauTermFLangFuns LcTauFJudgement t l.
Proof.
  LCSt_Tau_Induction lc_f_ind_mutual subst_lc_prop;
  subst_lc_proof.
Qed.

Lemma subst_lc:
 forall (t : Term) (l : lc' t), subst_lc_prop TauTermLangFuns LcTauTermJudgement t l.
Proof.
  lets*: subst_lc_st.
  lets*: subst_lc_e.
  lets*: subst_lc_f.
  simpl;
  intros;
  destruct t;
  inversion_on_lc;
  constructor~.
Qed.

(** Substitution of a locally closed terms into a body one produces
    another body *)

(* We need a lemma that Arthur only proved for his alternate inductive lc. *)

Function lc_open_var_prop (In : Type) (H: LangFuns Tau Tau In) (L : LcJudgement In) :=
  fun (t : In) (_ : lc' t) =>
  forall alpha,
    lc' (open_rec' 0 (ftvar alpha) t).
Hint Unfold lc_open_var_prop.

Lemma lc_open_var_v:
 forall (t : V) (l : lc' t), lc_open_var_prop TauTermVLangFuns LcVJudgement t l.
Proof.
  intros*.
Qed.

Ltac inversion_on_lc_term :=
  match goal with
    | H : lc_st (_)    |- _ => inversions~ H
    | H : lc_st (_)     |- _ => inversions~ H
    | H : lc_e (_)     |- _ => inversions~ H
    | H : lc_f (_)     |- _ => inversions~ H
    | H : lc_f (_)      |- _=> inversions~ H
end.  

Ltac lc_open_var_proof :=
  lets*: lc_open_var_v;
  simpl;
  intros*;
  simpl;
  constructor~;
  lets* M: TP.lc_open_var_rec.

Lemma lc_open_var_st:
 forall (t : St) (l : lc' t), lc_open_var_prop TauTermStLangFuns LcTauStJudgement t l.
Proof.
  LCSt_Tau_Induction lc_st_ind_mutual lc_open_var_prop;
  lc_open_var_proof.
Qed.

Lemma lc_open_var_e:
 forall (t : E) (l : lc' t), lc_open_var_prop TauTermELangFuns LcTauEJudgement t l.
Proof.
  LCSt_Tau_Induction lc_e_ind_mutual lc_open_var_prop;
  lc_open_var_proof.
Qed.

Lemma lc_open_var_f:
 forall (t : F) (l : lc' t), lc_open_var_prop TauTermFLangFuns LcTauFJudgement t l.
Proof.
  LCSt_Tau_Induction lc_f_ind_mutual lc_open_var_prop;
  lc_open_var_proof.
Qed.

Lemma lc_open_var:
 forall (t : Term) (l : lc' t), lc_open_var_prop TauTermLangFuns LcTauTermJudgement t l.
Proof.
  lets*: lc_open_var_st.
  lets*: lc_open_var_e.
  lets*: lc_open_var_f.
  simpl;
  intros;
  destruct t;
  inversion_on_lc;
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
  assert(alpha <> y).
  auto.
  contradiction.
Qed.

(** Opening of a body with a locally closed terms produces a 
    locally closed term *)

Lemma open_lc : forall t u,
  body t -> T.lc u -> lc (open_rec 0 u t).
Proof.
  introv [L H] U.
  pick_fresh alpha.
  rewrite~ (@subst_intro_alternative t alpha).
  apply~ subst_lc. 
Qed.

(* ********************************************************************** *)
(** Properties of [body] *)

(** An abstraction is locally closed iff it satifies the predicate [body] *) 

Lemma open_var_lc:
  forall t1 x,
    body t1 -> lc (open_rec 0 (ftvar x) t1).
Proof.
  lets* M: open_lc.
Qed.

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
  applys~ lc_open_var_st.

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
  applys~ lc_open_var_st.

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
  applys~ lc_open_var_st.

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
  applys~ lc_open_var_st.

  unfold body in A.
  simpl in A.
  constructor.
  assumption.
  assumption.
Qed.

(* ====================================================================== *)
(** ** An induction principle for locally closed terms *)

(** Interaction of [size] with [open_var] *)

Function size_open_prop (In : Type) (H: LangFuns Tau Tau In) :=
 fun (t : In) =>
  forall alpha n, 
    size' (open_rec' n (ftvar alpha) t) = size' t.
Hint Unfold size_open_prop.

Lemma size_open_v:
  forall (t : V), size_open_prop TauTermVLangFuns t.
Proof.
  intros*.
Qed.

Ltac size_open_proof := 
  intros*;
  lets*: TP.size_open_var;
  lets*: TMP.size_open_rec;
  simpl;
  intros;
  fequals~;
  auto.

Lemma size_open_st:
  forall (t : St), size_open_prop TauTermStLangFuns t.
Proof.
  StEF_Tau_Induction Tau_St_ind_mutual size_open_prop;
  size_open_proof.
Qed.

Lemma size_open_e:
  forall (t : E), size_open_prop TauTermELangFuns t.
Proof.
  StEF_Tau_Induction Tau_E_ind_mutual size_open_prop;
  size_open_proof.
Qed.

Lemma size_open_f:
  forall (t : F), size_open_prop TauTermFLangFuns t.
Proof.
  StEF_Tau_Induction Tau_F_ind_mutual size_open_prop;
  size_open_proof.
Qed.

Lemma size_open_tau:
  forall (t : Tau), size_open_prop TauTermTauLangFuns t.
Proof.
  StEF_Tau_Induction Tau_Tau_ind_mutual size_open_prop;
  size_open_proof.
Qed.

Lemma size_open :
  forall (t : Term), size_open_prop TauTermLangFuns t.
Proof.
  lets*: size_open_st.
  lets*: size_open_e.
  lets*: size_open_f.
  lets*: size_open_tau.
  destruct t; simpl; intros; fequals~.
Qed.

(** Interaction of [size] with [close_var] *)

Function size_close_var_prop (In : Type) (H: LangFuns Tau Tau In) :=
 fun (t : In) =>
  forall alpha n,
  size' (close_rec' n alpha t) = size' t.
Hint Unfold size_close_var_prop.

Lemma size_close_var_v:
  forall (t : V), size_close_var_prop TauTermVLangFuns t.
Proof.
  intros*.
Qed.

Ltac size_close_var_proof := 
  intros*;
  lets*: TP.size_close_var;
  lets*: TMP.size_close_var;
  simpl;
  intros;
  fequals~;
  auto.

Lemma size_close_var_st:
  forall (t : St), size_close_var_prop TauTermStLangFuns t.
Proof.
  StEF_Tau_Induction Tau_St_ind_mutual size_close_var_prop;
  size_close_var_proof.
Qed.

Lemma size_close_var_e:
  forall (t : E), size_close_var_prop TauTermELangFuns t.
Proof.
  StEF_Tau_Induction Tau_E_ind_mutual size_close_var_prop;
  size_close_var_proof.
Qed.

Lemma size_close_var_f:
  forall (t : F), size_close_var_prop TauTermFLangFuns t.
Proof.
  StEF_Tau_Induction Tau_F_ind_mutual size_close_var_prop;
  size_close_var_proof.
Qed.

Lemma size_close_var_tau:
  forall (t : Tau), size_close_var_prop TauTermTauLangFuns t.
Proof.
  StEF_Tau_Induction Tau_Tau_ind_mutual size_close_var_prop;
  size_close_var_proof.
Qed.

Lemma size_close_var :
  forall (t : Term), size_close_var_prop TauTermLangFuns t.
Proof.
  lets*: size_close_var_st.
  lets*: size_close_var_e.
  lets*: size_close_var_f.
  lets*: size_close_var_tau.
  destruct t; simpl; intros; fequals~.
Qed.

(** The induction principle *)
(* This would be very large, three induction principles. *)
(* And the only thing Dan seems to induct on is the length of a context,
  not its full size. So unless I need this I won't make it. *)

End TTMP.