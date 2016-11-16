(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION".   Daniel Grossman, August 2003 *)
(* Locally closed and body. *)
(* Brian Milnes 2016 *)

Set Implicit Arguments.
Require Export LibVarPathEnv Cyclone_Formal_Syntax Cyclone_LN_Open_Close.

(* Is a type locally closed? *)

Inductive lc_t : Tau -> Prop := 
 | lc_t_ftvar : forall x, lc_t (ftvar x)
 | lc_t_cint  : lc_t cint
 | lc_t_cross : forall t0 t1, lc_t t0 -> lc_t t1 -> lc_t (cross t0 t1)
 | lc_t_arrow : forall t0 t1, lc_t t0 -> lc_t t1 -> lc_t (arrow t0 t1)
 | lc_t_ptype : forall t0, lc_t t0 -> lc_t (ptype t0)
 | lc_t_utype : forall L' k t0,
                    (forall alpha, alpha \notin L' ->
                       lc_t (open_rec_t_t 0 (ftvar alpha) t0)) ->
                    lc_t (utype k t0)
 | lc_t_etype : forall L' p k t0,
                  (forall alpha, alpha \notin L' ->
                  lc_t (open_rec_t_t 0 (ftvar alpha) t0)) ->
                  lc_t (etype p k t0).

Definition body_t t :=
  forall L, forall alpha, alpha \notin L -> lc_t (open_t_t alpha t).


(* Is a term locally closed on type variables. *)

Inductive lc_t_tm_st : St -> Prop := 
 | lc_t_tm_st_e_s  : forall e, lc_t_tm_e  e -> lc_t_tm_st (e_s e)
 | lc_t_tm_retn    : forall e, lc_t_tm_e  e -> lc_t_tm_st (retn e)
 | lc_t_tm_seq     : forall s0 s1, lc_t_tm_st s0 -> lc_t_tm_st s1 -> lc_t_tm_st (seq s0 s1)
 | lc_t_tm_if      : forall e s0 s1, lc_t_tm_e  e -> lc_t_tm_st s0 -> lc_t_tm_st s1 ->
                                    lc_t_tm_st (if_s e s0 s1)
 | lc_t_tm_while   : forall e s, lc_t_tm_e  e -> lc_t_tm_st s -> lc_t_tm_st (while e s)
 | lc_t_tm_st_letx : forall e s,
                    lc_t_tm_e  e -> lc_t_tm_st s -> lc_t_tm_st (letx e s)
 | lc_t_tm_open   : forall e s,
                     lc_t_tm_e  e -> lc_t_tm_st s -> lc_t_tm_st (open e s)
 | lc_t_tm_openstar  : forall e s, 
                        lc_t_tm_e  e -> lc_t_tm_st s -> lc_t_tm_st (openstar e s)
with      lc_t_tm_e : E -> Prop :=
 | lc_t_tm_fevar : forall x, lc_t_tm_e  (v_e (fevar x))
 | lc_t_tm_i_e     : forall i, lc_t_tm_e  (i_e i)
 | lc_t_tm_p_e     : forall x p, lc_t_tm_e  (v_e (fevar x)) -> lc_t_tm_e  (p_e (fevar x) p)
 | lc_t_tm_f_e     : forall f, lc_t_tm_f f -> lc_t_tm_e  (f_e f)
 | lc_t_tm_amp     : forall e, lc_t_tm_e  e -> lc_t_tm_e  (amp e)
 | lc_t_tm_star    : forall e, lc_t_tm_e  e -> lc_t_tm_e  (star e)
 | lc_t_tm_cpair   : forall e0 e1, lc_t_tm_e  e0 -> lc_t_tm_e  e1 -> lc_t_tm_e  (cpair e0 e1)
 | lc_t_tm_dot     : forall e ipe, lc_t_tm_e  e -> lc_t_tm_e  (dot e ipe)
 | lc_t_tm_assign  : forall e1 e2, lc_t_tm_e  e1 -> lc_t_tm_e  e2 -> lc_t_tm_e  (appl e1 e2) 
 | lc_t_tm_appl    : forall e1 e2, lc_t_tm_e  e1 -> lc_t_tm_e  e2 -> lc_t_tm_e  (appl e1 e2)
 | lc_t_tm_call    : forall s, lc_t_tm_st s -> lc_t_tm_e  (call s)
 | lc_t_tm_inst    : forall e t, lc_t_tm_e  e -> lc_t t -> lc_t_tm_e  (inst e t)
 | lc_t_tm_pack    : forall t0 e t1, lc_t t0 -> lc_t_tm_e  e -> lc_t t1 -> 
                                lc_t_tm_e  (pack t0 e t1)
with      lc_t_tm_f : F -> Prop :=
| lc_t_tm_dfun : forall t1 t2 s, lc_t t1 -> lc_t t2 -> lc_t_tm_st s ->
                                     lc_t_tm_f (dfun t1 t2 s)
 | lc_t_tm_ufun : forall k f, lc_t_tm_f f -> lc_t_tm_f (ufun k f).

Inductive lc_t_tm : Term -> Prop := 
  | lc_t_tm_as_st : forall s, lc_t_tm_st s -> lc_t_tm (term_st s)
  | lc_t_tm_as_e  : forall e, lc_t_tm_e  e -> lc_t_tm (term_e  e)
  | lc_t_tm_as_f  : forall f, lc_t_tm_f  f -> lc_t_tm (term_f  f).

Definition body_tm t :=
  forall L, forall alpha, alpha \notin L -> lc_t_tm (open_t_tm alpha t).

(* Is a term locally closed on term variables. *)

Inductive lc_v : V -> Prop :=
  | lc_v_fevar  : forall x,  lc_v (fevar x).

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
                             lc_st (open_rec_v_tm_st 0 x s1 )) ->
                  lc_st (letx e s1)
 | lc_open   : forall e (s1 : St),
                  lc_e e ->
                  forall L' s1,
                  (forall x, x \notin L' -> 
                             lc_st (open_rec_v_tm_st 0 x s1 )) ->
                  lc_st (open e s1)
 | lc_openstar  : forall e (s1 : St),
                  lc_e e ->
                  forall L' s1,
                  (forall x, x \notin L' -> 
                             lc_st (open_rec_v_tm_st 0 x s1 )) ->
                  lc_st (openstar e s1)
with      lc_e : E -> Prop :=
 | lc_v_e : forall x, lc_v (fevar x) -> lc_e (v_e (fevar x))
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
 | lc_inst    : forall e t, lc_e e -> lc_t t -> lc_e (inst e t)
 | lc_pack    : forall t0 e t1, lc_t t0 -> lc_e e -> lc_t t1 -> 
                                lc_e (pack t0 e t1)
with      lc_f : F -> Prop :=
 | lc_dfun : forall t1 t2 s L',
               (forall x, x \notin L' -> 
                          lc_st (open_rec_v_tm_st 0 x s)) ->
               lc_f (dfun t1 t2 s)
 | lc_ufun : forall k f, lc_f f -> lc_f (ufun k f).

Inductive lc_term : Term -> Prop := 
  | lc_term_st : forall s, lc_st s -> lc_term (term_st s)
  | lc_term_e  : forall e, lc_e  e -> lc_term (term_e  e)
  | lc_term_f  : forall f, lc_f  f -> lc_term (term_f  f).

Definition body_t_tm t :=
  forall L, forall x, x \notin L -> lc_term (open_tm x t).

(* And now a predicate to check that terms are closed both ways. *)

Definition LC t := lc_term t /\ lc_t_tm t.
