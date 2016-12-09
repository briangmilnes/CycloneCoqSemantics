(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION".   Daniel Grossman, August 2003 *)
(* Definitions from Section 3.5.1 *)
(* Brian Milnes *)

Set Implicit Arguments.
Require Export TLC.LibLN TLC.LibNat TLC.LibEnv.

(* Question: can var be the same for types and programming variables? He does so in ML. *)

Inductive V : Set :=
 | bevar      : nat -> V                 
 | fevar      : var -> V.                 

Inductive Kappa : Set :=
 | B                         (* 'boxed' kind. *)
 | A.                        (* 'any'   kind. *)

Inductive St : Set :=                    
 | e_s       : E   -> St                 
 | letx      : E   -> St -> St           
with E : Set :=                          
 | v_e        : V -> E                   
 | call       : St -> E  
with F : Set :=
 | dfun       : Tau -> Tau -> St -> F    
with Tau : Set :=
 | btvar  : nat -> Tau                   (* A bound type variable, a de Bruijn index. *)
 | ftvar  : var -> Tau                   (* A free type variable. *)
 | utype  : Kappa -> Tau -> Tau.

Inductive Term : Set := 
  | term_st : St -> Term 
  | term_e :  E -> Term 
  | term_f :  F -> Term.

Scheme St_ind_mutual := Induction for St Sort Prop
with    E_ind_mutual := Induction for E Sort Prop
with    F_ind_mutual := Induction for F Sort Prop.
Combined Scheme Term_ind_mutual from St_ind_mutual, E_ind_mutual, F_ind_mutual.

Scheme Tau_St_ind_mutual := Induction for St Sort Prop
with   Tau_E_ind_mutual := Induction for E Sort Prop
with   Tau_F_ind_mutual := Induction for F Sort Prop
with   Tau_Tau_ind_mutual := Induction for Tau Sort Prop.
Combined Scheme Tau_Term_ind_mutual from Tau_St_ind_mutual, Tau_E_ind_mutual, Tau_F_ind_mutual, Tau_Tau_ind_mutual.

Module T. (* T = Types *)

Fixpoint subst  (tau : Tau) (alpha : var) (t : Tau) {struct t} : Tau := 
  match t with 
    | btvar i      => btvar i
    | ftvar beta   => (ftvar beta)
    | utype k t0   => utype k (subst tau alpha t0)
end.

Hint Resolve subst.

Notation "[ t 'T>' alpha ] tm" := (subst t alpha tm) (at level 68) : cyclone_scope.

Fixpoint open_rec  (k : nat) (t : Tau) (tau : Tau)  {struct tau}  : Tau :=
 match tau with 
   | btvar i       => btvar i
   | ftvar i       => ftvar i
   | utype kp t0   => utype kp (open_rec (S k) t t0)
  end.

Definition open t tau := open_rec 0 t tau.

Notation "{ k T> u } t" := (open_rec k u t)        (at level 67) : cyclone_scope.
Notation "t 'T^^' u"    := (open u t)              (at level 67) : cyclone_scope.
Notation "t 'T^' alpha" := (open (ftvar alpha) t)  (at level 67) : cyclone_scope.

(** Closing a type. *)

Fixpoint close_rec (k : nat) (v : var) (t : Tau) : Tau :=
  match t with 
    | btvar i       => t
    | ftvar x       => t
    | utype k' t0   => utype k' (close_rec (S k) v t0)
end.  

Definition close v t := close_rec 0 v t.

Notation "{ k <T u } t" := (close_rec k u t) (at level 67) : cyclone_scope.

(* Free variables of types. *)

Fixpoint fv (tau : Tau) {struct tau} : vars :=
 match tau with
    | btvar i      => \{}
    | ftvar x      => \{x}
    | utype k t0   => (fv t0)
end.

Hint Extern 1 (_ \notin fv _) => simpl; notin_solve.

Definition closed t := fv t = \{}.

End T.

Module TM. (* TM = Terms *)

(* Am I wrong to substitute at the var level instead of the V level? *)

Function subst_v (x y : var) (v : V) : V :=
  match v with
   | (bevar y)   => (bevar y)
   | (fevar z)   => If (z = y) then (fevar x) else (fevar z)
end.

Fixpoint subst_e (x y : var) (e : E) {struct e} : E := 
 match e with 
   | v_e v         => v_e (subst_v x y v)
   | call s        => call   (subst_st  x y s)
 end 
with subst_st (x y : var ) (s: St) {struct s} : St :=
  match s with
    | e_s e         => e_s      (subst_e x y e)
    | letx e s      => letx     (subst_e x y e)   (subst_st x y s)
end
with subst_f (x y : var) (f : F) {struct f} : F  := 
 match f with 
   | (dfun tau1 tau2 s) => (dfun tau1 tau2 (subst_st x y s))
 end.

Notation "[ x 'TM_v>' y ] tm" := (subst_v x y tm) (at level 68) : cyclone_scope.
Notation "[ x 'TM_e>' y ] tm" := (subst_e x y tm) (at level 68) : cyclone_scope.
Notation "[ x 'TM_st>' y ] tm" := (subst_st x y tm) (at level 68) : cyclone_scope.
Notation "[ x 'TM_f>' y ] tm" := (subst_f x y tm) (at level 68) : cyclone_scope.

Function subst (x y : var) (t : Term) {struct t} :=
  match t with
    | term_st s => term_st (subst_st x y s)
    | term_e  e => term_e  (subst_e  x y e)
    | term_f  f => term_f  (subst_f  x y f)
end.

Notation "[ x 'TM>' y ] tm" := (subst x y tm) (at level 68) : cyclone_scope.

(* Open a term binding in a term. *)

Function open_rec_v   (k : nat) (v : var) (v' : V) {struct v'} : V :=
  match v' with
    | (bevar i)   => If k = i then (fevar v) else bevar i
    | (fevar i)   => fevar i
end.

Fixpoint open_rec_st  (k : nat) (v : var) (s : St)  {struct s}  : St :=
 match s with 
    | e_s  e        => e_s      (open_rec_e  k v e)
    | letx e s      => letx     (open_rec_e k v e)   (open_rec_st (S k) v s)
  end 
with open_rec_e   (k : nat) (v : var) (e : E) {struct e}  : E :=
  match e with 
    | v_e v'          => v_e (open_rec_v k v v')
    | call s          => call   (open_rec_st k v s)
end 
with open_rec_f   (k : nat) (v : var) (f : F) {struct f} : F :=
  match f with 
    | dfun tau1 tau2 s => dfun tau1 tau2 (open_rec_st (S k) v s)
  end.

Function open_rec (k : nat) (v : var) (t : Term) {struct t} : Term :=
  match t with 
    | term_st s    => term_st (open_rec_st k v s)
    | term_e  e    => term_e  (open_rec_e  k v e)
    | term_f  f    => term_f  (open_rec_f  k v f)
  end.

Definition open v t := open_rec 0 v t.

Notation "{ k TM_v> u } t"  := (open_rec_v k u t) (at level 67) : cyclone_scope.
Notation "{ k TM_e> u } t"  := (open_rec_e k u t) (at level 67) : cyclone_scope.
Notation "{ k TM_st> u } t" := (open_rec_st k u t) (at level 67) : cyclone_scope.
Notation "{ k TM_f> u } t"  := (open_rec_f k u t) (at level 67) : cyclone_scope.
Notation "{ k TM> u }   t"  := (open_rec k u t) (at level 67) : cyclone_scope.

Notation "t 'TM^^' u"    := (open u t)       (at level 67) : cyclone_scope.
Notation "t 'TM^' alpha" := (open alpha t)   (at level 67) : cyclone_scope.

(* Closing a term on a term variable. *)

Function close_rec_v (k : nat) (z : var) (v : V) : V :=
  match v with
    | (bevar i) => v
    | (fevar x) => If x = z then (bevar k) else v
  end.

Fixpoint close_rec_st (k : nat) (z : var) (s : St) : St :=
  match s with
    | e_s  e       => e_s  (close_rec_e k z e)
    | letx e s     => letx  (close_rec_e k z e) (close_rec_st (S k) z s)
  end
with close_rec_e  (k : nat) (z : var) (e : E) : E :=
  match e with 
    | v_e v         => v_e (close_rec_v k z v)
    | call s        => call (close_rec_st k z s)
  end
with close_rec_f  (k : nat) (z : var) (f : F) : F :=
  match f with
  | dfun t1 t2 s    => dfun t1 t2 (close_rec_st (S k) z s)
end.

Notation "{ k <vtm_v alpha } t" := (close_rec_e k alpha t) (at level 67) : cyclone_scope.
Notation "{ k <vtm_e alpha } t" := (close_rec_e k alpha t) (at level 67) : cyclone_scope.
Notation "{ k <vtm_st alpha } t" := (close_rec_st k alpha t) (at level 67) : cyclone_scope.
Notation "{ k <vtm_f alpha } t" := (close_rec_f k alpha t) (at level 67) : cyclone_scope.


Function close_rec (k : nat) (z : var) (t : Term) : Term :=
  match t with 
    | term_st s    => term_st (close_rec_st k z s)
    | term_e  e    => term_e  (close_rec_e k z e)
    | term_f  f    => term_f  (close_rec_f k z f)
  end.

Definition close z t := close_rec 0 z t.

Notation "{ k <vtm alpha } t" := (close_rec k alpha t) (at level 67) : cyclone_scope.

(* Free term variables of terms. *)

Function fv_v (v : V) {struct v} : vars := 
  match v with
    | (bevar i) => \{}
    | (fevar x) => \{x}
  end.

Hint Extern 1 (_ \notin fv_v _) => simpl; notin_solve.

Fixpoint fv_st (t : St) {struct t} : vars :=
  match t with
    | e_s  e       => fv_e e
    | letx e s     => (fv_e e) \u (fv_st s)
  end
with  fv_e (e : E) {struct e} : vars := 
  match e with 
    | v_e v         => fv_v v
    | call s        => fv_st s 
  end
with  fv_f (f : F) {struct f} : vars := 
  match f with
  | dfun t1 t2 s => (fv_st s)
end.

Hint Extern 1 (_ \notin fv_st _) => simpl; notin_solve.
Hint Extern 1 (_ \notin fv_e _) => simpl; notin_solve.
Hint Extern 1 (_ \notin fv_f _) => simpl; notin_solve.

Function fv (t : Term) {struct t} : vars :=
  match t with 
    | term_st s    => fv_st s
    | term_e  e    => fv_e e
    | term_f  f    => fv_f f 
  end.

Hint Extern 1 (_ \notin fv _) => simpl; notin_solve.

End TM.

Module TTM. (* T = Types TM = Terms *)

Fixpoint subst_e (tau : Tau) (alpha : var) (e : E) {struct e} : E :=
 match e with 
   | v_e v         => v_e v
   | call s        => call   (subst_st    tau alpha s)
 end 
with subst_st (tau : Tau) (alpha : var) (s: St) {struct s} : St :=
  match s with
    | e_s e         => e_s      (subst_e tau alpha e)
    | letx e s      => letx     (subst_e tau alpha e)   (subst_st tau alpha s)
end
with subst_f (tau : Tau) (alpha : var) (f : F) {struct f} : F  := 
 match f with 
   | (dfun tau1 tau2 s) => 
     (dfun (T.subst tau alpha tau1) (T.subst tau alpha tau2) (subst_st tau alpha s))
end.


Hint Resolve subst_e.
Hint Resolve subst_st.
Hint Resolve subst_f.

Notation "[ t 'TTM_e>'  alpha ] tm" := (subst_e  t alpha tm) (at level 68) : cyclone_scope.
Notation "[ t 'TTM_st>' alpha ] tm" := (subst_st t alpha tm) (at level 68) : cyclone_scope.
Notation "[ t 'TTM_f>'  alpha ] tm" := (subst_f  t alpha tm) (at level 68) : cyclone_scope.

Function subst (tau : Tau) (alpha : var) (t: Term) {struct t} : Term :=
  match t with
    | term_st s => term_st (subst_st tau alpha s)
    | term_e  e => term_e  (subst_e tau alpha e)
    | term_f  f => term_f  (subst_f tau alpha f)
  end.

Hint Resolve subst.

Notation "[ t 'TTM>' alpha ] tm" := (subst t alpha tm) (at level 68) : cyclone_scope.

(* Open a type binder in a term. *)

Definition open_rec_v (k : nat) (t : Tau) (v : V)  : V :=
  match v with
    | fevar i => fevar i
    | bevar i => bevar i
  end.

Fixpoint open_rec_st  (k : nat) (t : Tau) (s : St)  {struct s}  : St :=
 match s with 
    | e_s  e        => e_s      (open_rec_e  k t e)
    | letx e s      => letx     (open_rec_e  k t e)  (open_rec_st k t s)
  end 
with open_rec_e   (k : nat) (t : Tau) (e : E) {struct e}  : E :=
  match e with 
    | v_e v         => v_e (open_rec_v k t v)
    | call s        => call   (open_rec_st k t s)
end 
with open_rec_f   (k : nat) (t : Tau) (f : F) {struct f} : F :=
  match f with 
    | dfun tau1 tau2 s => dfun (T.open_rec k t tau1) (T.open_rec k t tau2) 
                               (open_rec_st k t s)
  end.

Function open_rec  (k : nat) (t : Tau) (T : Term) : Term :=
  match T with
    | term_st s    => term_st (open_rec_st k t s)
    | term_e  e    => term_e  (open_rec_e  k t e)
    | term_f  f    => term_f  (open_rec_f  k t f)
  end.

Definition open t T := open_rec 0 t T.

Notation "{ k TTM_v> u } t"  := (open_rec_v k u t) (at level 67) : cyclone_scope.
Notation "{ k TTM_e> u } t"  := (open_rec_e k u t) (at level 67) : cyclone_scope.
Notation "{ k TTM_st> u } t" := (open_rec_st k u t) (at level 67) : cyclone_scope.
Notation "{ k TTM_f> u } t"  := (open_rec_f k u t) (at level 67) : cyclone_scope.
Notation "{ k TTM> u }   t"  := (open_rec k u t) (at level 67) : cyclone_scope.

Notation "t 'TTM^^' u"    := (open u t)       (at level 67) : cyclone_scope.
Notation "t 'TTM^' alpha" := (open alpha t)   (at level 67) : cyclone_scope.


(* Closing a type variable in a term. *)

Function close_rec_v (k : nat) (v : var) (v' : V) {struct v}  : V := v'.

Fixpoint close_rec_st  (k : nat) (v : var) (s : St)  {struct s}  : St :=
 match s with 
    | e_s  e        => e_s      (close_rec_e  k v e)
    | letx e s      => letx     (close_rec_e  k v e)  (close_rec_st k v s)
  end 
with close_rec_e   (k : nat) (v : var) (e : E) {struct e}  : E :=
  match e with 
    | v_e v'        => v_e (close_rec_v k v v')
    | call s        => call   (close_rec_st k v s)
end 
with close_rec_f   (k : nat) (v : var) (f : F) {struct f} : F :=
  match f with 
    | dfun tau1 tau2 s => dfun (T.close_rec k v tau1) (T.close_rec k v tau2) 
                               (close_rec_st k v s)
  end.


Notation "{ k <TTM_e alpha } t" := (close_rec_e k alpha t) (at level 67) : cyclone_scope.
Notation "{ k <TTM_st alpha } t" := (close_rec_st k alpha t) (at level 67) : cyclone_scope.
Notation "{ k <TTM_f alpha } t" := (close_rec_f k alpha t) (at level 67) : cyclone_scope.

Function close_rec  (k : nat) (v : var) (t : Term) : Term :=
  match t with 
    | term_st s    => term_st (close_rec_st k v s)
    | term_e  e    => term_e  (close_rec_e  k v e)
    | term_f  f    => term_f  (close_rec_f  k v f)
  end.

Definition close v t := close_rec 0 v t.

Notation "{ k <TTM alpha } t" := (T.close_rec k alpha t) (at level 67) : cyclone_scope.

(* Free type variables of a term. *)

Function fv_v (v : V) : vars := 
  match v with 
    | (bevar i) => \{} 
    | (fevar x) => \{}
  end.

Hint Extern 1 (_ \notin fv_v _) => simpl; notin_solve.

Fixpoint fv_st (t : St) {struct t} : vars :=
  match t with
    | e_s  e       => fv_e e
    | letx e s     => (fv_e e) \u (fv_st s)
  end
with  fv_e (e : E) {struct e} : vars := 
  match e with 
    | v_e v         => fv_v v
    | call s        => fv_st s 
  end
with  fv_f (f : F) {struct f} : vars := 
  match f with
  | dfun t1 t2 s    => (T.fv t1) \u (T.fv t2) \u (fv_st s) 
end.

Hint Extern 1 (_ \notin fv_st _) => simpl; notin_solve.
Hint Extern 1 (_ \notin fv_e _) => simpl; notin_solve.
Hint Extern 1 (_ \notin fv_f _) => simpl; notin_solve.

Function fv (t : Term) {struct t} : vars :=
  match t with 
    | term_st s    => fv_st s
    | term_e  e    => fv_e e
    | term_f  f    => fv_f f 
 end.

Hint Extern 1 (_ \notin fv _) => simpl; notin_solve.

Definition closed x := fv x = \{}.

End TTM.


Lemma close_v_tm_v_open_v_tm_v :
  forall t x n,
  x \notin TM.fv_v t -> 
  TM.close_rec_v n x (TM.open_rec_v n x t) = t.
Proof.
  introv.
  induction t; simpl; introv Fr; fequals~.
  case_nat~. simpl. 
  case_var~.
  case_var~.
Qed.

Function close_v_tm_st_open_v_tm_st_pred (t : St) :=
  forall x n, 
    x \notin TM.fv_st t ->
    TM.close_rec_st n x (TM.open_rec_st n x t) = t.
Hint Unfold close_v_tm_st_open_v_tm_st_pred.

Function close_v_tm_e_open_v_tm_e_pred (t : E) :=
  forall x n, 
    x \notin TM.fv_e t ->
    TM.close_rec_e n x (TM.open_rec_e n x t) = t.
Hint Unfold close_v_tm_e_open_v_tm_e_pred.

Function close_v_tm_f_open_v_tm_f_pred (t : F) :=
  forall x n, 
    x \notin TM.fv_f t ->
    TM.close_rec_f n x (TM.open_rec_f n x t) = t.
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
  x \notin TM.fv t -> 
  TM.close_rec n x (TM.open_rec n x t) = t.
Proof.
  destruct t; simpl; intros; fequals~.
  applys~ close_v_tm_st_open_v_tm_st.
  applys~ close_v_tm_e_open_v_tm_e.
  applys~ close_v_tm_f_open_v_tm_f.
Qed.

Lemma test1:
  forall t, close_v_tm_f_open_v_tm_f_pred t.
Proof.
  assert(forall t, close_v_tm_e_open_v_tm_e_pred t).
  abstract(close_v_tm_X_open_v_tm_X_induction E_ind_mutual; close_v_tm_X_open_v_tm_X_proof)
      using test1_e.

  close_v_tm_X_open_v_tm_X_induction F_ind_mutual;
  close_v_tm_X_open_v_tm_X_proof.
Qed exporting test1_e.
Check test1_e.
Check test1.

(* The type, what can substitute/open on. *)
Class Fun (VorT T : Type) :=
  {
    fv        : T -> vars;
    subst     : VorT -> var -> T -> T;
    open_rec  : nat -> VorT -> T -> T;
    close_rec : nat -> var -> T -> T;
  }.

Instance TauTermFun : Fun Tau Term :=
  {
    fv        := TTM.fv;
    subst     := TTM.subst;
    open_rec  := TTM.open_rec;
    close_rec := TTM.close_rec;
  }.

Instance TauFun : Fun Tau Tau :=
  {
    fv        := T.fv;
    subst     := T.subst;
    open_rec  := T.open_rec;
    close_rec := T.close_rec;
  }.

Instance TermFun : Fun var Term :=
  {
    fv        := TM.fv;
    subst     := TM.subst;
    open_rec  := TM.open_rec;
    close_rec := TM.close_rec;
  }.

Instance TermVFun : Fun var V :=
  {
    fv        := TM.fv_v;
    subst     := TM.subst_v;
    open_rec  := TM.open_rec_v;
    close_rec := TM.close_rec_v;
  }.





Function close_open_prop (VorT T : Type) (H: Fun VorT T) : Prop :=
  forall t x n,
  x \notin fv t -> 
  close_rec n x (open_rec n x t) = t.

Lemma close_open:
  close_open_prop TermFun.
Proof.
(*
  ============================
  close_open_prop TermFun
*)
  unfold close_open_prop.
(*
  ============================
  forall (t : Term) (x : var) (n : nat),
  x \notin fv t -> close_rec n x (open_rec n x t) = t
*)
  simpl.
(*
  ============================
  forall (t : Term) (x : var) (n : nat),
  x \notin TM.fv t -> TM.close_rec n x (TM.open_rec n x t) = t
*)

(* assert and prove it then export a lemma of the name below. *)
  assert(close_open_prop TauFun);
  abstract(close_open_proof_script) using close_open_tau.
  
Qed.











(* Fail, can't adhoc dispatch on a type. It won't unify. 
(* Try kinding the predicates and simplifying to get what I need. *)
Inductive TypeKind : Type :=
 | type.
(*
 | variable
 | statement
 | expression
 | function
 | term.
*)

(* It's just not clear yet if Coq will let me return something here. *)
Function FV (tk : TypeKind) (T : Type) :  T -> vars :=
  match tk in TypeKind return (match tk with | type => Tau -> vars end) with
  | type  =>  T.fv
  end.


Fixpoint fv (tau : Tau) : vars :=
Function fv_v (v : V) : vars := 
Fixpoint fv_st (t : St) : vars :=
with  fv_e (e : E) : vars := 
with  fv_f (f : F) : vars := 
Function fv (t : Term) : vars :=
Function fv_v (v : V) : vars :=         
Fixpoint fv_st (t : St) : vars :=
with  fv_e (e : E) : vars := 
with  fv_f (f : F) : vars := 
Function fv (t : Term) : vars :=

Fixpoint subst  (tau : Tau) (alpha : var) (t : Tau) {struct t} : Tau := 
Function subst_v (x y : var) (v : V) : V :=
Fixpoint subst_e (x y : var) (e : E) {struct e} : E := 
with subst_st (x y : var ) (s: St) {struct s} : St :=
with subst_f (x y : var) (f : F) {struct f} : F  := 
Function subst (x y : var) (t : Term) {struct t} :=
Fixpoint subst_e (tau : Tau) (alpha : var) (e : E) {struct e} : E :=
with subst_st (tau : Tau) (alpha : var) (s: St) {struct s} : St :=
with subst_f (tau : Tau) (alpha : var) (f : F) {struct f} : F  := 
Function subst (tau : Tau) (alpha : var) (t: Term) {struct t} : Term :=

Fixpoint open_rec  (k : nat) (t : Tau) (tau : Tau)  {struct tau}  : Tau :=
Function open_rec_v   (k : nat) (v : var) (v' : V) {struct v'} : V :=
Fixpoint open_rec_st  (k : nat) (v : var) (s : St)  {struct s}  : St :=
with open_rec_e   (k : nat) (v : var) (e : E) {struct e}  : E :=
with open_rec_f   (k : nat) (v : var) (f : F) {struct f} : F :=
Function open_rec (k : nat) (v : var) (t : Term) {struct t} : Term :=
Definition open_rec_v (k : nat) (t : Tau) (v : V)  : V :=
Fixpoint open_rec_st  (k : nat) (t : Tau) (s : St)  {struct s}  : St :=
with open_rec_e   (k : nat) (t : Tau) (e : E) {struct e}  : E :=
with open_rec_f   (k : nat) (t : Tau) (f : F) {struct f} : F :=
Function open_rec  (k : nat) (t : Tau) (T : Term) : Term :=


Fixpoint close_rec (k : nat) (v : var) (t : Tau) : Tau :=
Function close_rec_v (k : nat) (z : var) (v : V) : V :=
Fixpoint close_rec_st (k : nat) (z : var) (s : St) : St :=
with close_rec_e  (k : nat) (z : var) (e : E) : E :=
with close_rec_f  (k : nat) (z : var) (f : F) : F :=
Function close_rec (k : nat) (z : var) (t : Term) : Term :=
Function close_rec_v (k : nat) (v : var) (v' : V) {struct v}  : V := v'.
Fixpoint close_rec_st  (k : nat) (v : var) (s : St)  {struct s}  : St :=
with close_rec_e   (k : nat) (v : var) (e : E) {struct e}  : E :=
with close_rec_f   (k : nat) (v : var) (f : F) {struct f} : F :=
Function close_rec  (k : nat) (v : var) (t : Term) : Term :=
*)



(*Fixpoint fv_st (t : St) {struct t} : vars :=
(* from the manual *)Fixpoint subst_e (tau : Tau) (alpha : var) (e : E) {struct e} : E :=
Ltac f x :=Fixpoint open_rec_st  (k : nat) (t : Tau) (s : St)  {struct s}  : St :=
        match x withFixpoint close_rec_st  (k : nat) (v : var) (s : St)  {struct s}  : St :=
          context f [S ?X] => Fixpoint fv_st (t : St) {struct t} : vars :=
          idtac X;                    (* To display the evaluation order *Fixpoint subst  (tau : Tau) (alpha : var) (t : Tau) {struct t} : Tau :=)
          assert (p := eq_refl 1 : X=1);    (* To filter the case X=1 *)
          let x:= context f[O] in assert (x=O) (* To observe the context *)
        end.

Ltac e2s :=
  match goal with
    | |- ?P => idtac P;
      match P with
      | context f [TM.fv_f ?X] => context f [TM.fv_st X]
      end
  end.

Ltac e2s' f P :=
  match P with
  | context f [TM.fv_f ?X] => context f [TM.fv_st X]
  end.

Lemma test2:
  forall t, close_v_tm_f_open_v_tm_f_pred t.
Proof.
  autounfold in *.
(*  e2s (forall t, close_v_tm_f_open_v_tm_f_pred t).*)
Abort.

(* from http://adam.chlipala.net/cpdt/html/Match.html *)

(* Fails to match into the proposition. *)
Ltac find_fv_f_inside :=
  match goal with
    | [ |- context[?x \notin TM.fv_f ?X] ] => destruct X
  end.
Lemma test3:
  forall t, close_v_tm_f_open_v_tm_f_pred t.
Proof.
  autounfold in *.
  (* find_fv_f_inside.*)
Abort.

Ltac find_open_f_inside :=
  match goal with
    | [ |- context[(TM.open_rec_f _ _ ?T)] ] => destruct T
  end.

Lemma test4:
  forall t, close_v_tm_f_open_v_tm_f_pred t.
Proof.
  autounfold in *.
  (* find_open_f_inside. fails *)
  intros.
  find_open_f_inside.
  (* Matches and destructs, but it is not recursing through quantifiers. *)
Abort.

(* 
    | context F [(TM.open_rec_st ?n ?x ?T)] =>
      replace (TM.open_rec_st n x T) with (TM.open_rec_f n x T)
  end.
*)

Ltac r e :=
  match e with
    | fun t : St => @?E1 t = @?E2 t =>
    idtac "Es" E1 E2; 
   let E1' := r uconstr:(E1) in
    idtac "E1'" E1';
    let E2' := r uconstr:(E2) in 
    idtac "E2'" E2';
     uconstr:(True)
(* uconstr:(fun x : F => (E1' x) = (E2' x)) *)
    | fun p : ?S => @?P p =>
      let V:=  uconstr:(fun p => (P p)) in
      idtac "modifying" V;
      V
end.

Ltac S f :=
  let f' := (r f) in
  assert(forall t : F, f' t).

Lemma test5:
    forall (t : St),
     (fun t => t = t) t.
Proof.
  S (fun t : St => t = t).
Abort.

(
  prompt>test5 < 1614 |test5| 0 < </prompt>S (fun t : St => t = t).
<infomsg>Es (fun t : St => t) (fun t : St => t)</infomsg>
<infomsg>modifying (fun t : F => t)</infomsg>
Toplevel input, characters 0-23:
> S (fun t : St => t = t).
> ^^^^^^^^^^^^^^^^^^^^^^^
In nested Ltac calls to "S" and "r", last call failed.
Error: No matching clauses for match.

 Note that we stop before the idtac "E1".

 Asked Arnaud Spiwack.
*)

(* Works without recursing. *)

Ltac R :=
  match goal with
  | |- forall t : St, ?P =>
    assert(forall t : F, P)
  end.

Lemma test5:
 forall (t : St),
   t = t.
Proof.
  R.
Abort.
*)