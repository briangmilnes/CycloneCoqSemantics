
(* This totally not necessary, LC is what we want. *)

(* And well formedness of types and terms. *)
(* Bug on notation. *)

Notation "t ^ x" := (open_tau x t).
Inductive type : Tau -> Prop :=
 | type_btvar  : forall x, type (btvar x)
 | type_ftvar  : forall x, type (ftvar x)
 | type_cint   : type cint
 | type_cross  : forall t0 t1, type t0 -> type t1 -> type (cross t0 t1)
 | type_arrow  : forall t0 t1, type t0 -> type t1 -> type (arrow t0 t1)
 | type_ptype  : forall t, type t -> type (ptype t)
 | type_utype  : forall L k t,
                   (forall alpha, alpha \notin L -> type (t ^ alpha)) -> 
                   type (utype k t)
 | type_etype  : forall L p k t, 
                   (forall alpha, alpha \notin L -> type (t ^ alpha)) -> 
                   type (etype p k t).

Notation "t ^tt x" := (open_tau_term x t) (at level 67).
Notation "t ^t x" := (open_term x t) (at level 67).

Inductive term_V : V -> Prop :=
 | term_V_bevar   : forall n, term_V (bevar n)
 | term_V_fevar   : forall v, term_V (fevar v).

Inductive term_St : St -> Prop :=
 | term_St_e_s       : forall e, term_E e -> term_St (e_s e)
 | term_St_retn      : forall e, term_E e -> term_St (retn e)
 | term_St_seq       : forall s0 s1, term_St s0 -> term_St s1 -> term_St (seq s0 s1)
 | term_St_if_s      : forall e s0 s1, term_E e -> term_St s0 -> term_St s1 -> term_St (if_s e s0 s1)
 | term_St_while     : forall e s, term_E e -> term_St s -> term_St (while e s)
 | term_St_letx      : forall L e s, term_E e -> term_St s -> 
                                   (forall x, x \notin L -> term_St (open_rec_term_st 0 x s)) ->
                                   term_St (letx e s) 
 | term_St_open      : forall L e s, term_E e -> term_St s ->
                                     (forall x, x \notin L -> term_St (open_rec_term_st 0 x s)) ->
                                     term_St (open e s)
 | term_St_openstar  : forall L e s, term_E e -> term_St s -> 
                                     (forall x, x \notin L -> term_St (open_rec_term_st 0 x s)) ->
                                     term_St (openstar e s)
with term_E       : E  -> Prop :=
 | term_E_v_e     : forall v, term_V v -> term_E (v_e v)
 | term_E_i_e     : forall i, term_E (i_e i)
 | term_E_p_e     : forall v p, term_E (p_e v p)
 | term_E_f_e     : forall f, term_F f -> term_E (f_e f)
 | term_E_amp     : forall e, term_E e -> term_E (amp e)
 | term_E_star    : forall e, term_E e -> term_E (star e)
 | term_E_cpair   : forall e0 e1, term_E e0 -> term_E e0 -> term_E (cpair e0 e1)
 | term_E_dot     : forall e ipe, term_E e -> term_E (dot e ipe)
 | term_E_assign  : forall e0 e1, term_E e0 -> term_E e1 -> term_E (assign e0 e1)
 | term_E_appl    : forall e0 e1, term_E e0 -> term_E e1 -> term_E (appl e0 e1)
 | term_E_call    : forall s, term_St s -> term_E (call s)
 | term_E_inst    : forall e t, term_E e -> type t -> term_E (inst e t)
 | term_E_pack    : forall t0 e t1, type t0 -> term_E e -> type t1 -> term_E (pack t0 e t1)
with term_F       : F  -> Prop := 
 | term_F_dfun    : forall t0 t1 s, type t0 -> type t1 -> term_F (dfun t0 t1 s)
 | term_F_ufun    : forall k f, term_F f -> term_F (ufun k f).
  
Inductive term : Term -> Prop :=
  | term_term_st : forall s, term_St s -> term (term_st s)
  | term_term_e  : forall e, term_E e  -> term (term_e e)
  | term_term_f  : forall f, term_F f  -> term (term_f f).

