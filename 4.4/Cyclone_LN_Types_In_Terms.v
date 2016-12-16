(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION".   Daniel Grossman, August 2003 *)
(* This is all of the LN infrastructure packed in a module for types. *)
(* Brian Milnes 2016 *)

Set Implicit Arguments.
Require Export Cyclone_Formal_Syntax.
Require Export Cyclone_LN_Types.
Require Export Cyclone_LN_Terms.
(* Substituting a type into a term for a type variable. *)

Module TTM. (* T = Types TM = Terms *)

Function subst_v (tau : Tau) (alpha : var) (v : V) {struct v} : V := v.

Fixpoint subst_e (tau : Tau) (alpha : var) (e : E) {struct e} : E :=
 match e with 
   | v_e v         => v_e (subst_v tau alpha v)
   | i_e i         => i_e i
   | p_e x p       => p_e x p
   | f_e f         =>        (f_e (subst_f  tau alpha f))
   | amp e'        => amp    (subst_e     tau alpha e')
   | star e'       => star   (subst_e     tau alpha e')
   | cpair e1 e2   => cpair  (subst_e     tau alpha e1) (subst_e tau alpha e2)
   | dot e' i      => dot    (subst_e     tau alpha e') i
   | assign e1 e2  => assign (subst_e     tau alpha e1) (subst_e tau alpha e2)
   | appl  e1 e2   => appl   (subst_e     tau alpha e1) (subst_e tau alpha e2)
   | call s        => call   (subst_st    tau alpha s)
   | inst e' t     => inst   (subst_e     tau alpha e') (T.subst tau alpha t)
   | pack t e' t'  => pack   (T.subst tau alpha t) (subst_e tau alpha e')
                             (T.subst tau alpha t')
 end 
with subst_st (tau : Tau) (alpha : var) (s: St) {struct s} : St :=
  match s with
    | e_s e         => e_s      (subst_e tau alpha e)
    | retn e        => retn     (subst_e tau alpha e)
    | seqx s1 s2    => seqx      (subst_st tau alpha s1) (subst_st tau alpha s2)
    | if_s e s1 s2  => if_s     (subst_e tau alpha e)
                                (subst_st tau alpha s1) (subst_st tau alpha s2)
    | while e s     => while    (subst_e tau alpha e)   (subst_st tau alpha s)
    | letx e s      => letx     (subst_e tau alpha e)   (subst_st tau alpha s)
    | openx     e s  => openx     (subst_e tau alpha e)   (subst_st tau alpha s)
    | openstar e s  => openstar (subst_e tau alpha e)   (subst_st tau alpha s)
end
with subst_f (tau : Tau) (alpha : var) (f : F) {struct f} : F  := 
 match f with 
   | (dfun tau1 tau2 s) => 
     (dfun (T.subst tau alpha tau1) (T.subst tau alpha tau2) (subst_st tau alpha s))
   | ufun k f => (ufun k (subst_f tau alpha f))
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

Definition open_rec_v (k : nat) (t : Tau) (v : V)  : V := v.

Fixpoint open_rec_st  (k : nat) (t : Tau) (s : St)  {struct s}  : St :=
 match s with 
    | e_s  e        => e_s      (open_rec_e  k t e)
    | retn e        => retn     (open_rec_e  k t e)
    | seqx s0 s1    => seqx     (open_rec_st k t s0) (open_rec_st k t s1)
    | if_s e s1 s2  => if_s     (open_rec_e  k t e) 
                                (open_rec_st k t s1) (open_rec_st k t s2)
    | while e s     => while    (open_rec_e  k t e)  (open_rec_st k t s)
    | letx e s      => letx     (open_rec_e  k t e)  (open_rec_st k t s)
    | openx e s      => openx     (open_rec_e  k t e)  (open_rec_st k t s)
    | openstar e s  => openstar (open_rec_e  k t e)  (open_rec_st k t s)
  end 
with open_rec_e   (k : nat) (t : Tau) (e : E) {struct e}  : E :=
  match e with 
    | v_e v         => v_e (open_rec_v k t v)
    | i_e i         => i_e i
    | p_e x p       => p_e x p 
    | f_e f         => f_e    (open_rec_f  k t f)
    | amp e         => amp    (open_rec_e  k t e)
    | star e        => star   (open_rec_e  k t e)
    | cpair e1 e2   => cpair  (open_rec_e  k t e1) (open_rec_e k t e2)
    | dot  e ipe    => dot    (open_rec_e  k t e) ipe
    | assign e1 e2  => assign (open_rec_e  k t e1) (open_rec_e k t e2)
    | appl e1 e2    => appl   (open_rec_e  k t e1) (open_rec_e k t e2)
    | call s        => call   (open_rec_st k t s)
    | inst e t'      => inst   (open_rec_e  k t e) (T.open_rec k t t')
    | pack t0 e t1  => pack   (T.open_rec k t t0) (open_rec_e k t e) (T.open_rec k t t1)
end 
with open_rec_f   (k : nat) (t : Tau) (f : F) {struct f} : F :=
  match f with 
    | dfun tau1 tau2 s => dfun (T.open_rec k t tau1) (T.open_rec k t tau2) 
                               (open_rec_st k t s)
    | ufun k' f        => ufun k' (open_rec_f k t f) 
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
    | retn e        => retn     (close_rec_e  k v e)
    | seqx s0 s1    => seqx     (close_rec_st k v s0) (close_rec_st k v s1)
    | if_s e s1 s2  => if_s     (close_rec_e  k v e) 
                                (close_rec_st k v s1) (close_rec_st k v s2)
    | while e s     => while    (close_rec_e  k v e)  (close_rec_st k v s)
    | letx e s      => letx     (close_rec_e  k v e)  (close_rec_st k v s)
    | openx e s     => openx    (close_rec_e  k v e)  (close_rec_st k v s)
    | openstar e s  => openstar (close_rec_e  k v e)  (close_rec_st k v s)
  end 
with close_rec_e   (k : nat) (v : var) (e : E) {struct e}  : E :=
  match e with 
    | v_e v'        => v_e (close_rec_v k v v')
    | i_e i         => i_e i
    | p_e x p       => p_e (close_rec_v k v x) p
    | f_e f         => f_e    (close_rec_f  k v f)
    | amp e         => amp    (close_rec_e  k v e)
    | star e        => star   (close_rec_e  k v e)
    | cpair e1 e2   => cpair  (close_rec_e  k v e1) (close_rec_e k v e2)
    | dot  e ipe    => dot    (close_rec_e  k v e) ipe
    | assign e1 e2  => assign (close_rec_e  k v e1) (close_rec_e k v e2)
    | appl e1 e2    => appl   (close_rec_e  k v e1) (close_rec_e k v e2)
    | call s        => call   (close_rec_st k v s)
    | inst e t      => inst   (close_rec_e  k v e) (T.close_rec k v t)
    | pack t0 e t1  => pack   (T.close_rec     k v t0)
                              (close_rec_e  k v e) (T.close_rec k v t1)
end 
with close_rec_f   (k : nat) (v : var) (f : F) {struct f} : F :=
  match f with 
    | dfun tau1 tau2 s => dfun (T.close_rec k v tau1) (T.close_rec k v tau2) 
                               (close_rec_st k v s)
    | ufun k' f        => ufun k' (close_rec_f k v f) 
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
    | retn e       => fv_e e
    | seqx s0 s1   => (fv_st s0) \u (fv_st s1)
    | if_s e s0 s1 => (fv_e e) \u (fv_st s0) \u (fv_st s1)
    | while e s0   => (fv_e e) \u (fv_st s0)
    | letx e s     => (fv_e e) \u (fv_st s)
    | openx e s     => (fv_e e) \u (fv_st s)
    | openstar e s => (fv_e e) \u (fv_st s)
  end
with  fv_e (e : E) {struct e} : vars := 
  match e with 
    | v_e v         => fv_v v
    | i_e  i        => \{}
    | p_e x _       => \{}
    | f_e f         => fv_f f
    | amp e         => fv_e e
    | star e        => fv_e e
    | cpair e0 e1   => (fv_e e0) \u (fv_e e1)
    | dot e _       => fv_e e
    | assign e1 e2  => (fv_e e1) \u (fv_e e2)
    | appl e1 e2    => (fv_e e1) \u (fv_e e2)
    | call s        => fv_st s 
    | inst e t      => (fv_e e) \u (T.fv t)
    | pack t0 e t1  => (T.fv t0) \u (fv_e e) \u (T.fv t1)
  end
with  fv_f (f : F) {struct f} : vars := 
  match f with
  | dfun t1 t2 s    => (T.fv t1) \u (T.fv t2) \u (fv_st s) 
  | ufun k f        => fv_f f
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

(* Is a term locally closed on type variables. *)

Inductive lc_v : V -> Prop :=
 | lc_fevar : forall x, lc_v (fevar x).

Inductive lc_st : St -> Prop := 
 | lc_st_e_s  : forall e, lc_e  e -> lc_st (e_s e)
 | lc_retn    : forall e, lc_e  e -> lc_st (retn e)
 | lc_seqx    : forall s0 s1, lc_st s0 -> lc_st s1 -> lc_st (seqx s0 s1)
 | lc_if      : forall e s0 s1, lc_e  e -> lc_st s0 -> lc_st s1 ->
                                    lc_st (if_s e s0 s1)
 | lc_while   : forall e s, lc_e  e -> lc_st s -> lc_st (while e s)
 | lc_st_letx : forall e s,
                       lc_e  e -> lc_st s ->
                       lc_st (letx e s)
 | lc_open   : forall e s,
                     lc_e  e -> lc_st s -> lc_st (openx e s)
 | lc_openstar  : forall e s, 
                        lc_e  e -> lc_st s -> lc_st (openstar e s)
with      lc_e : E -> Prop :=
 | lc_v_e     : forall v, lc_v v -> lc_e (v_e v)
 | lc_i_e     : forall i, lc_e  (i_e i)
 | lc_p_e     : forall x p, lc_e  (v_e (fevar x)) -> lc_e  (p_e (fevar x) p)
 | lc_f_e     : forall f, lc_f f -> lc_e  (f_e f)
 | lc_amp     : forall e, lc_e  e -> lc_e  (amp e)
 | lc_star    : forall e, lc_e  e -> lc_e  (star e)
 | lc_cpair   : forall e0 e1, lc_e  e0 -> lc_e  e1 -> lc_e  (cpair e0 e1)
 | lc_dot     : forall e ipe, lc_e  e -> lc_e  (dot e ipe)
 | lc_assign  : forall e1 e2, lc_e  e1 -> lc_e  e2 -> lc_e  (appl e1 e2) 
 | lc_appl    : forall e1 e2, lc_e  e1 -> lc_e  e2 -> lc_e  (appl e1 e2)
 | lc_call    : forall s, lc_st s -> lc_e  (call s)
 | lc_inst    : forall e t, lc_e  e -> T.lc t -> lc_e  (inst e t)
 | lc_pack    : forall t0 e t1, T.lc t0 -> lc_e  e -> T.lc t1 -> 
                                lc_e  (pack t0 e t1)
with      lc_f : F -> Prop :=
 | lc_dfun : forall t1 t2 s, T.lc t1 -> T.lc t2 -> lc_st s ->
                                     lc_f (dfun t1 t2 s)
 | lc_ufun : forall k f, lc_f f -> lc_f (ufun k f).

Inductive lc : Term -> Prop := 
  | lc_as_st : forall s, lc_st s -> lc (term_st s)
  | lc_as_e  : forall e, lc_e  e -> lc (term_e  e)
  | lc_as_f  : forall f, lc_f  f -> lc (term_f  f).

Scheme lc_st_ind_mutual := Induction for lc_st Sort Prop
with   lc_e_ind_mutual  := Induction for lc_e Sort Prop
with   lc_f_ind_mutual  := Induction for lc_f Sort Prop.
Combined Scheme lc_ind_mutual from lc_st_ind_mutual, lc_e_ind_mutual, lc_f_ind_mutual.

Hint Constructors lc_st.
Hint Constructors lc_e.
Hint Constructors lc_f.
Hint Constructors lc.


Definition body t :=
  exists L, forall alpha, alpha \notin L -> lc (open (ftvar alpha) t).

Definition body_st t :=
  exists L, forall alpha, alpha \notin L -> lc_st (open_rec_st 0 (ftvar alpha) t).

End TTM.