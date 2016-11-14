(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION".   Daniel Grossman, August 2003 *)
(* Locally closed and body. *)
(* Brian Milnes 2016 *)

Set Implicit Arguments.
Require Export LibVarPathEnv Cyclone_Formal_Syntax Cyclone_LN_Open_Close.

(* Is a type locally closed? *)

Inductive lc_tau : Tau -> Prop := 
 | lc_tau_ftvar : forall x, lc_tau (ftvar x)
 | lc_tau_cint  : lc_tau cint
 | lc_tau_cross : forall t0 t1, lc_tau t0 -> lc_tau t1 -> lc_tau (cross t0 t1)
 | lc_tau_arrow : forall t0 t1, lc_tau t0 -> lc_tau t1 -> lc_tau (arrow t0 t1)
 | lc_tau_ptype : forall t0, lc_tau t0 -> lc_tau (ptype t0)
 | lc_tau_utype : forall L' k t0,
                    (forall alpha, alpha \notin L' ->
                       lc_tau (open_rec_tau 0 (ftvar alpha) t0)) ->
                    lc_tau (utype k t0)
 | lc_tau_etype : forall L' p k t0,
                  (forall alpha, alpha \notin L' ->
                  lc_tau (open_rec_tau 0 (ftvar alpha) t0)) ->
                  lc_tau (etype p k t0).

Definition body_tau t :=
  forall L, forall alpha, alpha \notin L -> lc_tau (open_tau alpha t).


(* Is a term locally closed on type variables. *)

Inductive lc_tau_term_st : St -> Prop := 
 | lc_tau_term_st_e_s  : forall e, lc_tau_term_e  e -> lc_tau_term_st (e_s e)
 | lc_tau_term_retn    : forall e, lc_tau_term_e  e -> lc_tau_term_st (retn e)
 | lc_tau_term_seq     : forall s0 s1, lc_tau_term_st s0 -> lc_tau_term_st s1 -> lc_tau_term_st (seq s0 s1)
 | lc_tau_term_if      : forall e s0 s1, lc_tau_term_e  e -> lc_tau_term_st s0 -> lc_tau_term_st s1 ->
                                    lc_tau_term_st (if_s e s0 s1)
 | lc_tau_term_while   : forall e s, lc_tau_term_e  e -> lc_tau_term_st s -> lc_tau_term_st (while e s)
 | lc_tau_term_st_letx : forall e s,
                    lc_tau_term_e  e -> lc_tau_term_st s -> lc_tau_term_st (letx e s)
 | lc_tau_term_open   : forall e s,
                     lc_tau_term_e  e -> lc_tau_term_st s -> lc_tau_term_st (open e s)
 | lc_tau_term_openstar  : forall e s, 
                        lc_tau_term_e  e -> lc_tau_term_st s -> lc_tau_term_st (openstar e s)
with      lc_tau_term_e : E -> Prop :=
 | lc_tau_term_term_fevar : forall x, lc_tau_term_e  (v_e (fevar x))
 | lc_tau_term_i_e     : forall i, lc_tau_term_e  (i_e i)
 | lc_tau_term_p_e     : forall x p, lc_tau_term_e  (v_e (fevar x)) -> lc_tau_term_e  (p_e (fevar x) p)
 | lc_tau_term_f_e     : forall f, lc_tau_term_f f -> lc_tau_term_e  (f_e f)
 | lc_tau_term_amp     : forall e, lc_tau_term_e  e -> lc_tau_term_e  (amp e)
 | lc_tau_term_star    : forall e, lc_tau_term_e  e -> lc_tau_term_e  (star e)
 | lc_tau_term_cpair   : forall e0 e1, lc_tau_term_e  e0 -> lc_tau_term_e  e1 -> lc_tau_term_e  (cpair e0 e1)
 | lc_tau_term_dot     : forall e ipe, lc_tau_term_e  e -> lc_tau_term_e  (dot e ipe)
 | lc_tau_term_assign  : forall e1 e2, lc_tau_term_e  e1 -> lc_tau_term_e  e2 -> lc_tau_term_e  (appl e1 e2) 
 | lc_tau_term_appl    : forall e1 e2, lc_tau_term_e  e1 -> lc_tau_term_e  e2 -> lc_tau_term_e  (appl e1 e2)
 | lc_tau_term_call    : forall s, lc_tau_term_st s -> lc_tau_term_e  (call s)
 | lc_tau_term_inst    : forall e t, lc_tau_term_e  e -> lc_tau t -> lc_tau_term_e  (inst e t)
 | lc_tau_term_pack    : forall t0 e t1, lc_tau t0 -> lc_tau_term_e  e -> lc_tau t1 -> 
                                lc_tau_term_e  (pack t0 e t1)
with      lc_tau_term_f : F -> Prop :=
| lc_tau_term_dfun : forall t1 t2 s, lc_tau t1 -> lc_tau t2 -> lc_tau_term_st s ->
                                     lc_tau_term_f (dfun t1 t2 s)
 | lc_tau_term_ufun : forall k f, lc_tau_term_f f -> lc_tau_term_f (ufun k f).

Inductive lc_tau_term : Term -> Prop := 
  | lc_tau_term_as_st : forall s, lc_tau_term_st s -> lc_tau_term (term_st s)
  | lc_tau_term_as_e  : forall e, lc_tau_term_e  e -> lc_tau_term (term_e  e)
  | lc_tau_term_as_f  : forall f, lc_tau_term_f  f -> lc_tau_term (term_f  f).

Definition body_term t :=
  forall L, forall alpha, alpha \notin L -> lc_tau_term (open_tau_term alpha t).

(* Is a term locally closed on term variables. *)

Inductive lc_V : V -> Prop :=
  | lc_V_fevar  : forall x,  lc_V (fevar x).

Inductive lc_st : St -> Prop := 
 | lc_st_e_s  : forall e, lc_e e -> lc_st (e_s e)
 | lc_retn    : forall e, lc_e e -> lc_st (retn e)
 | lc_seq     : forall s0 s1, lc_st s0 -> lc_st s1 -> lc_st (seq s0 s1)
 | lc_if      : forall e s0 s1, lc_e e -> lc_st s0 -> lc_st s1 -> lc_st (if_s e s0 s1)
 | lc_while   : forall e s, lc_e e -> lc_st s -> lc_st (while e s)
 | lc_st_letx : forall e (s1 : St),
                  lc_e e ->
                  forall L' s1,
                  (forall x, x \notin L' -> 
                             lc_st (open_rec_term_st 0 x s1 )) ->
                  lc_st (letx e s1)
 | lc_open   : forall e (s1 : St),
                  lc_e e ->
                  forall L' s1,
                  (forall x, x \notin L' -> 
                             lc_st (open_rec_term_st 0 x s1 )) ->
                  lc_st (open e s1)
 | lc_openstar  : forall e (s1 : St),
                  lc_e e ->
                  forall L' s1,
                  (forall x, x \notin L' -> 
                             lc_st (open_rec_term_st 0 x s1 )) ->
                  lc_st (openstar e s1)
with      lc_e : E -> Prop :=
 | lc_v_e : forall x, lc_V (fevar x) -> lc_e (v_e (fevar x))
 | lc_i_e     : forall i, lc_e (i_e i)
 | lc_p_e     : forall x p, lc_e (v_e (fevar x)) -> lc_e (p_e (fevar x) p)
 | lc_f_e     : forall f, lc_f f -> lc_e (f_e f)
 | lc_amp     : forall e, lc_e e -> lc_e (amp e)
 | lc_star    : forall e, lc_e e -> lc_e (star e)
 | lc_cpair   : forall e0 e1, lc_e e0 -> lc_e e1 -> lc_e (cpair e0 e1)
 | lc_dot     : forall e ipe, lc_e e -> lc_e (dot e ipe)
 | lc_assign  : forall e1 e2, lc_e e1 -> lc_e e2 -> lc_e (appl e1 e2) 
 | lc_appl    : forall e1 e2, lc_e e1 -> lc_e e2 -> lc_e (appl e1 e2)
 | lc_call    : forall s, lc_st s -> lc_e (call s)
 | lc_inst    : forall e t, lc_e e -> lc_tau t -> lc_e (inst e t)
 | lc_pack    : forall t0 e t1, lc_tau t0 -> lc_e e -> lc_tau t1 -> 
                                lc_e (pack t0 e t1)
with      lc_f : F -> Prop :=
 | lc_dfun : forall t1 t2 s L',
               (forall x, x \notin L' -> 
                          lc_st (open_rec_term_st 0 x s)) ->
               lc_f (dfun t1 t2 s)
 | lc_ufun : forall k f, lc_f f -> lc_f (ufun k f).

Inductive lc_term : Term -> Prop := 
  | lc_term_st : forall s, lc_st s -> lc_term (term_st s)
  | lc_term_e  : forall e, lc_e  e -> lc_term (term_e  e)
  | lc_term_f  : forall f, lc_f  f -> lc_term (term_f  f).

Definition body_tau_term t :=
  forall L, forall x, x \notin L -> lc_term (open_term x t).

(* And now a predicate to check that terms are closed both ways. *)

Definition LC t := lc_term t /\ lc_tau_term t.
