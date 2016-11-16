(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION".   Daniel Grossman, August 2003 *)
(* Open/Close LN infrastructure. *)
(* Brian Milnes 2016 *)

Set Implicit Arguments.
Require Export Cyclone_Formal_Syntax LibVarPathEnv.

(* Open/Close of variables in binders. *)

(* Open a type binder in a type. *)

Fixpoint open_rec_t_t  (k : nat) (t : Tau) (tau : Tau)  {struct tau}  : Tau :=
 match tau with 
   | btvar i       => If k = i then t else btvar i
   | ftvar i       => ftvar i
   | cint          => cint
   | cross t0 t1   => cross (open_rec_t_t k t t0) (open_rec_t_t k t t1)
   | arrow t0 t1   => arrow (open_rec_t_t k t t0) (open_rec_t_t k t t1)
   | ptype t0      => ptype (open_rec_t_t k t t0)
   | utype kp t0   => utype kp (open_rec_t_t (S k) t t0)
   | etype p kp t0 => etype p kp (open_rec_t_t (S k) t t0)
  end.

Definition open_t_t t tau := open_rec_t_t 0 t tau.

Notation "{ k tt> u } t" := (open_rec_t_t k u t) (at level 67) : cyclone_scope.
Notation "t 'tt^^' u"    := (open_t_t u t)       (at level 67) : cyclone_scope.
Notation "t 'tt^' alpha" := (open_t_t alpha t)   (at level 67) : cyclone_scope.

(* Open a type binder in a term. *)

Definition open_rec_t_tm_v (k : nat) (t : Tau) (v : V)  : V :=
  match v with
    | fevar i => fevar i
    | bevar i => bevar i
  end.

Fixpoint open_rec_t_tm_st  (k : nat) (t : Tau) (s : St)  {struct s}  : St :=
 match s with 
    | e_s  e        => e_s      (open_rec_t_tm_e  k t e)
    | retn e        => retn     (open_rec_t_tm_e  k t e)
    | seq s0 s1     => seq      (open_rec_t_tm_st k t s0) (open_rec_t_tm_st k t s1)
    | if_s e s1 s2  => if_s     (open_rec_t_tm_e  k t e) 
                                (open_rec_t_tm_st k t s1) (open_rec_t_tm_st k t s2)
    | while e s     => while    (open_rec_t_tm_e  k t e)  (open_rec_t_tm_st k t s)
    | letx e s      => letx     (open_rec_t_tm_e  k t e)  (open_rec_t_tm_st k t s)
    | open e s      => open     (open_rec_t_tm_e  k t e)  (open_rec_t_tm_st k t s)
    | openstar e s  => openstar (open_rec_t_tm_e  k t e)  (open_rec_t_tm_st k t s)
  end 
with open_rec_t_tm_e   (k : nat) (t : Tau) (e : E) {struct e}  : E :=
  match e with 
    | v_e v         => v_e (open_rec_t_tm_v k t v)
    | i_e i         => i_e i
    | p_e x p       => p_e x p 
    | f_e f         => f_e    (open_rec_t_tm_f  k t f)
    | amp e         => amp    (open_rec_t_tm_e  k t e)
    | star e        => star   (open_rec_t_tm_e  k t e)
    | cpair e1 e2   => cpair  (open_rec_t_tm_e  k t e1) (open_rec_t_tm_e k t e2)
    | dot  e ipe    => dot    (open_rec_t_tm_e  k t e) ipe
    | assign e1 e2  => assign (open_rec_t_tm_e  k t e1) (open_rec_t_tm_e k t e2)
    | appl e1 e2    => appl   (open_rec_t_tm_e  k t e1) (open_rec_t_tm_e k t e2)
    | call s        => call   (open_rec_t_tm_st k t s)
    | inst e t'      => inst   (open_rec_t_tm_e  k t e) (open_rec_t_t k t t')
    | pack t0 e t1  => pack   (open_rec_t_t k t t0) (open_rec_t_tm_e k t e) (open_rec_t_t k t t1)
end 
with open_rec_t_tm_f   (k : nat) (t : Tau) (f : F) {struct f} : F :=
  match f with 
    | dfun tau1 tau2 s => dfun (open_rec_t_t k t tau1) (open_rec_t_t k t tau2) 
                               (open_rec_t_tm_st k t s)
    | ufun k' f        => ufun k' (open_rec_t_tm_f k t f) 
  end.

Function open_rec_t_tm  (k : nat) (t : Tau) (T : Term) : Term :=
  match T with
    | term_st s    => term_st (open_rec_t_tm_st k t s)
    | term_e  e    => term_e  (open_rec_t_tm_e  k t e)
    | term_f  f    => term_f  (open_rec_t_tm_f  k t f)
  end.

Definition open_t_tm t T := open_rec_t_tm 0 t T.

Notation "{ k ttm_v> u } t"  := (open_rec_t_tm_v k u t) (at level 67) : cyclone_scope.
Notation "{ k ttm_e> u } t"  := (open_rec_t_tm_e k u t) (at level 67) : cyclone_scope.
Notation "{ k ttm_st> u } t" := (open_rec_t_tm_st k u t) (at level 67) : cyclone_scope.
Notation "{ k ttm_f> u } t"  := (open_rec_t_tm_f k u t) (at level 67) : cyclone_scope.
Notation "{ k ttm> u }   t"  := (open_rec_t_tm k u t) (at level 67) : cyclone_scope.

Notation "t 'ttm^^' u"    := (open_t_tm u t)       (at level 67) : cyclone_scope.
Notation "t 'ttm^' alpha" := (open_t_tm alpha t)   (at level 67) : cyclone_scope.

(* Open a term binding in a term. *)

Function open_rec_v_tm_v   (k : nat) (v : var) (v' : V) {struct v'} : V :=
  match v' with
    | (bevar i)   => If k = i then (fevar v) else bevar i
    | (fevar i)   => fevar i
end.

Function open_rec_v_tm_p (k : nat) (v : var) (v' : V) {struct v}  : V :=
  match v' with
  | (bevar i) => If k = i then (fevar v) else v' 
  | (fevar i) => (fevar i) 
end.


Fixpoint open_rec_v_tm_st  (k : nat) (v : var) (s : St)  {struct s}  : St :=
 match s with 
    | e_s  e        => e_s      (open_rec_v_tm_e  k v e)
    | retn e        => retn     (open_rec_v_tm_e k v e)
    | seq s0 s1     => seq      (open_rec_v_tm_st k v s0) (open_rec_v_tm_st k v s1)
    | if_s e s1 s2  => if_s     (open_rec_v_tm_e k v e) 
                                (open_rec_v_tm_st k v s1) (open_rec_v_tm_st k v s2)
    | while e s     => while    (open_rec_v_tm_e k v e)   (open_rec_v_tm_st k v s)
    | letx e s      => letx     (open_rec_v_tm_e k v e)   (open_rec_v_tm_st (S k) v s)
    | open e s      => open     (open_rec_v_tm_e k v e)   (open_rec_v_tm_st (S k) v s)
    | openstar e s  => openstar (open_rec_v_tm_e k v e)   (open_rec_v_tm_st (S k) v s)
  end 
with open_rec_v_tm_e   (k : nat) (v : var) (e : E) {struct e}  : E :=
  match e with 
    | v_e v'          => v_e (open_rec_v_tm_v k v v')
    | i_e i           => i_e i
    | p_e x p         => p_e (open_rec_v_tm_p k v x) p 
    | f_e f           => f_e    (open_rec_v_tm_f (S k) v f)
    | amp e           => amp    (open_rec_v_tm_e k v e)
    | star e          => star   (open_rec_v_tm_e k v e)
    | cpair e1 e2     => cpair  (open_rec_v_tm_e k v e1) (open_rec_v_tm_e k v e2)
    | dot  e ipe      => dot    (open_rec_v_tm_e k v e) ipe
    | assign e1 e2    => assign (open_rec_v_tm_e k v e1) (open_rec_v_tm_e k v e2)
    | appl e1 e2      => appl   (open_rec_v_tm_e k v e1) (open_rec_v_tm_e k v e2)
    | call s          => call   (open_rec_v_tm_st k v s)
    | inst e t        => inst   (open_rec_v_tm_e k v e) t 
    | pack t0 e t1    => pack    t0 (open_rec_v_tm_e k v e) t1  
end 
with open_rec_v_tm_f   (k : nat) (v : var) (f : F) {struct f} : F :=
  match f with 
    | dfun tau1 tau2 s => dfun tau1 tau2 (open_rec_v_tm_st k v s)
    | ufun k' f        => ufun k' (open_rec_v_tm_f k v f) 
  end.

Function open_rec_v_tm (k : nat) (v : var) (t : Term) {struct t} : Term :=
  match t with 
    | term_st s    => term_st (open_rec_v_tm_st k v s)
    | term_e  e    => term_e  (open_rec_v_tm_e  k v e)
    | term_f  f    => term_f  (open_rec_v_tm_f  k v f)
  end.

Definition open_tm v t := open_rec_v_tm 0 v t.

Notation "{ k ttm_v> u } t"  := (open_rec_t_tm_v k u t) (at level 67) : cyclone_scope.
Notation "{ k ttm_e> u } t"  := (open_rec_t_tm_e k u t) (at level 67) : cyclone_scope.
Notation "{ k ttm_st> u } t" := (open_rec_t_tm_st k u t) (at level 67) : cyclone_scope.
Notation "{ k ttm_f> u } t"  := (open_rec_t_tm_f k u t) (at level 67) : cyclone_scope.
Notation "{ k ttm> u }   t"  := (open_rec_t_tm k u t) (at level 67) : cyclone_scope.

Notation "t 'ttm^^' u"    := (open_t_tm u t)       (at level 67) : cyclone_scope.
Notation "t 'ttm^' alpha" := (open_t_tm alpha t)   (at level 67) : cyclone_scope.

(** Closing a type. *)

Fixpoint close_rec_tv_t (k : nat) (v : var) (t : Tau) : Tau :=
  match t with 
    | btvar i       => t
    | ftvar x       => If x = v then (btvar k) else t
    | cint          => cint
    | cross t0 t1   => cross (close_rec_tv_t k v t0) (close_rec_tv_t k v t1)
    | arrow t0 t1   => arrow (close_rec_tv_t k v t0) (close_rec_tv_t k v t1)
    | ptype t0      => ptype (close_rec_tv_t k v t0)
    | utype k' t0   => utype k' (close_rec_tv_t (S k) v t0)
    | etype p k' t0 => etype p k' (close_rec_tv_t (S k) v t0)
end.  

Definition close_tv_t v t := close_rec_tv_t 0 v t.

Notation "{ k <tvt u } t" := (close_rec_tv_t k u t) (at level 67) : cyclone_scope.

(* Closing a type variable in a term. *)

Fixpoint close_rec_tv_tm_st  (k : nat) (v : var) (s : St)  {struct s}  : St :=
 match s with 
    | e_s  e        => e_s      (close_rec_tv_tm_e  k v e)
    | retn e        => retn     (close_rec_tv_tm_e  k v e)
    | seq s0 s1     => seq      (close_rec_tv_tm_st k v s0) (close_rec_tv_tm_st k v s1)
    | if_s e s1 s2  => if_s     (close_rec_tv_tm_e  k v e) 
                                (close_rec_tv_tm_st k v s1) (close_rec_tv_tm_st k v s2)
    | while e s     => while    (close_rec_tv_tm_e  k v e)  (close_rec_tv_tm_st k v s)
    | letx e s      => letx     (close_rec_tv_tm_e  k v e)  (close_rec_tv_tm_st k v s)
    | open e s      => open     (close_rec_tv_tm_e  k v e)  (close_rec_tv_tm_st k v s)
    | openstar e s  => openstar (close_rec_tv_tm_e  k v e)  (close_rec_tv_tm_st k v s)
  end 
with close_rec_tv_tm_e   (k : nat) (v : var) (e : E) {struct e}  : E :=
  match e with 
    | v_e _         => e 
    | i_e i         => i_e i
    | p_e x p       => p_e x p
    | f_e f         => f_e    (close_rec_tv_tm_f  k v f)
    | amp e         => amp    (close_rec_tv_tm_e  k v e)
    | star e        => star   (close_rec_tv_tm_e  k v e)
    | cpair e1 e2   => cpair  (close_rec_tv_tm_e  k v e1) (close_rec_tv_tm_e k v e2)
    | dot  e ipe    => dot    (close_rec_tv_tm_e  k v e) ipe
    | assign e1 e2  => assign (close_rec_tv_tm_e  k v e1) (close_rec_tv_tm_e k v e2)
    | appl e1 e2    => appl   (close_rec_tv_tm_e  k v e1) (close_rec_tv_tm_e k v e2)
    | call s        => call   (close_rec_tv_tm_st k v s)
    | inst e t      => inst   (close_rec_tv_tm_e  k v e) (close_rec_tv_t k v t)
    | pack t0 e t1  => pack   (close_rec_tv_t     k v t0)
                              (close_rec_tv_tm_e  k v e) (close_rec_tv_t k v t1)
end 
with close_rec_tv_tm_f   (k : nat) (v : var) (f : F) {struct f} : F :=
  match f with 
    | dfun tau1 tau2 s => dfun (close_rec_tv_t k v tau1) (close_rec_tv_t k v tau2) 
                               (close_rec_tv_tm_st k v s)
    | ufun k' f        => ufun k' (close_rec_tv_tm_f k v f) 
  end.


Notation "{ k <tvtm_e alpha } t" := (close_rec_tv_tm_e k alpha t) (at level 67) : cyclone_scope.
Notation "{ k <tvtm_st alpha } t" := (close_rec_tv_tm_st k alpha t) (at level 67) : cyclone_scope.
Notation "{ k <tvtm_f alpha } t" := (close_rec_tv_tm_f k alpha t) (at level 67) : cyclone_scope.

Function close_rec_tv_tm  (k : nat) (v : var) (t : Term) : Term :=
  match t with 
    | term_st s    => term_st (close_rec_tv_tm_st k v s)
    | term_e  e    => term_e  (close_rec_tv_tm_e  k v e)
    | term_f  f    => term_f  (close_rec_tv_tm_f  k v f)
  end.

Definition close_t_tm v t := close_rec_tv_tm 0 v t.

Notation "{ k <tvtm alpha } t" := (close_rec_tv_t k alpha t) (at level 67) : cyclone_scope.


(* Closing a term on a term variable. *)

Function close_rec_v_tm_v (k : nat) (z : var) (v : V) : V :=
  match v with
    | (bevar i) => v
    | (fevar x) => If x = z then (bevar k) else v
  end.

Fixpoint close_rec_v_tm_st (k : nat) (z : var) (s : St) : St :=
  match s with
    | e_s  e       => e_s  (close_rec_v_tm_e k z e)
    | retn e       => retn (close_rec_v_tm_e k z e)
    | seq s0 s1    => seq (close_rec_v_tm_st k z s0) (close_rec_v_tm_st k z s1)
    | if_s e s0 s1 => if_s (close_rec_v_tm_e k z e) 
                           (close_rec_v_tm_st k z s0)
                           (close_rec_v_tm_st k z s1)
    | while e s0   => while (close_rec_v_tm_e k z e) (close_rec_v_tm_st k z s0)
    | letx e s     => letx (close_rec_v_tm_e k z e) (close_rec_v_tm_st (S k) z s)
    | open e s     => open (close_rec_v_tm_e k z e) (close_rec_v_tm_st (S k) z s)
    | openstar e s => openstar (close_rec_v_tm_e k z e) (close_rec_v_tm_st (S k) z s)
  end
with close_rec_v_tm_e  (k : nat) (z : var) (e : E) : E :=
  match e with 
    | v_e v         => v_e (close_rec_v_tm_v k z v)
    | i_e  i        => i_e i
    | p_e x p       => p_e (close_rec_v_tm_v k z x) p
    | f_e f         => f_e (close_rec_v_tm_f k z f)
    | amp e         => amp (close_rec_v_tm_e k z e)
    | star e        => star (close_rec_v_tm_e k z e)
    | cpair e0 e1   => cpair (close_rec_v_tm_e k z e0) (close_rec_v_tm_e k z e1)
    | dot e ipe     => dot (close_rec_v_tm_e k z e) ipe
    | assign e0 e1  => assign (close_rec_v_tm_e k z e0) (close_rec_v_tm_e k z e1)
    | appl e0 e1    => appl   (close_rec_v_tm_e k z e0) (close_rec_v_tm_e k z e1)
    | call s        => call (close_rec_v_tm_st k z s)
    | inst e t      => inst (close_rec_v_tm_e k z e) t
    | pack t0 e t1  => pack t0 (close_rec_v_tm_e k z e) t1
  end
with close_rec_v_tm_f  (k : nat) (z : var) (f : F) : F :=
  match f with
  | dfun t1 t2 s    => dfun t1 t2 (close_rec_v_tm_st (S k) z s)
  | ufun k' f       => ufun k' (close_rec_v_tm_f k z f)
end.

Notation "{ k <vtm_v alpha } t" := (close_rec_v_tm_e k alpha t) (at level 67) : cyclone_scope.
Notation "{ k <vtm_e alpha } t" := (close_rec_v_tm_e k alpha t) (at level 67) : cyclone_scope.
Notation "{ k <vtm_st alpha } t" := (close_rec_v_tm_st k alpha t) (at level 67) : cyclone_scope.
Notation "{ k <vtm_f alpha } t" := (close_rec_v_tm_f k alpha t) (at level 67) : cyclone_scope.


Function close_rec_v_tm (k : nat) (z : var) (t : Term) : Term :=
  match t with 
    | term_st s    => term_st (close_rec_v_tm_st k z s)
    | term_e  e    => term_e  (close_rec_v_tm_e k z e)
    | term_f  f    => term_f  (close_rec_v_tm_f k z f)
  end.

Definition close_v_tm z t := close_rec_v_tm 0 z t.

Notation "{ k <vtm alpha } t" := (close_rec_tv_t k alpha t) (at level 67) : cyclone_scope.
