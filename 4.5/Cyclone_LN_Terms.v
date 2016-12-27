(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION".   Daniel Grossman, August 2003 *)
(* This is all of the LN infrastructure packed in a module for types. *)
(* Brian Milnes 2016 *)

Set Implicit Arguments.
Require Export Cyclone_Formal_Syntax.
Require Export Cyclone_LN_Types.
(* Subtituting an expression into a term for a term variable. *)

(* Cyclone semantics are odd in that &xp is used as a value and 
 explicitly defined syntactically. So to put an expression into
 a term for a variable, it can be substituted in two places:
 v_e (fevar x) and p_e x p in our abstract syntax.

 v_e (fevar x) can be replaced with a new expression, e, as v_e e.
  
 But p_e x p can not and so must be translated to (e.i0).i1... where
 p = i0 i1 ...
 and for each u we must insert a pack.

 It's not worth finishing this unless I actually need it.
 *)

(* However the more limited substitution of variables for variables works. *)

Module TM. (* TM = Terms *)

Function subst_V (x : V) (y : V) (v : V) : V :=
  match x with
    | bevar _ => v
    | fevar _ =>
      match v with
        | (bevar y)   => (bevar y)
        | (fevar z)   => If (v = y) then x else (fevar z)
      end
end.

(* Am I wrong to substitute at the var level instead of the V level? *)

Function subst_v (x y : var) (v : V) : V :=
  match v with
   | (bevar y)   => (bevar y)
   | (fevar z)   => If (z = y) then (fevar x) else (fevar z)
end.

Fixpoint subst_e (x y : var) (e : E) {struct e} : E := 
 match e with 
   | v_e v         => v_e (subst_v x y v)
   | i_e i         => e
   | p_e v p       => p_e (subst_v x y v) p
   | f_e f         =>        (f_e (subst_f x y f))
   | amp e'        => amp    (subst_e   x y e')
   | star e'       => star   (subst_e   x y e')
   | cpair e1 e2   => cpair  (subst_e   x y e1) (subst_e x y e2)
   | dot e' i      => dot    (subst_e   x y e') i
   | assign e1 e2  => assign (subst_e   x y e1) (subst_e x y e2)
   | appl   e1 e2  => appl   (subst_e   x y e1) (subst_e x y e2)
   | call s        => call   (subst_st  x y s)
   | inst e' t     => inst   (subst_e   x y e') t
   | pack t e' t'  => pack   t (subst_e x y e') t'
 end 
with subst_st (x y : var ) (s: St) {struct s} : St :=
  match s with
    | e_s e         => e_s      (subst_e x y e)
    | retn e        => retn     (subst_e x y e)
    | seqx s1 s2    => seqx      (subst_st x y s1) (subst_st x y s2)
    | if_s e s1 s2  => if_s     (subst_e x y e) 
                                (subst_st x y s1) (subst_st x y s2)
    | while e s     => while    (subst_e x y e)   (subst_st x y s)
    | letx e s      => letx     (subst_e x y e)   (subst_st x y s)
    | openx    e s  => openx    (subst_e x y e)   (subst_st x y s)
    | openstar e s  => openstar (subst_e x y e)   (subst_st x y s)
end
with subst_f (x y : var) (f : F) {struct f} : F  := 
 match f with 
   | (dfun tau1 tau2 s) => (dfun tau1 tau2 (subst_st x y s))
   | ufun k f => (ufun k (subst_f x y f))
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
    | retn e        => retn     (open_rec_e k v e)
    | seqx s0 s1    => seqx      (open_rec_st k v s0) (open_rec_st k v s1)
    | if_s e s1 s2  => if_s     (open_rec_e k v e) 
                                (open_rec_st k v s1) (open_rec_st k v s2)
    | while e s     => while    (open_rec_e k v e)   (open_rec_st k v s)
    (* BUG: don't open at a higher level in the E. *)
    | letx e s      => letx     (open_rec_e k v e)   (open_rec_st (S k) v s)
    | openx e s     => openx    (open_rec_e k v e)   (open_rec_st (S k) v s)
    | openstar e s  => openstar (open_rec_e k v e)   (open_rec_st (S k) v s)
  end 
with open_rec_e   (k : nat) (v : var) (e : E) {struct e}  : E :=
  match e with 
    | v_e v'          => v_e (open_rec_v k v v')
    | i_e i           => i_e i
    | p_e x p         => p_e (open_rec_v k v x) p 
    | f_e f           => f_e    (open_rec_f k v f)
    | amp e           => amp    (open_rec_e k v e)
    | star e          => star   (open_rec_e k v e)
    | cpair e1 e2     => cpair  (open_rec_e k v e1) (open_rec_e k v e2)
    | dot  e ipe      => dot    (open_rec_e k v e) ipe
    | assign e1 e2    => assign (open_rec_e k v e1) (open_rec_e k v e2)
    | appl e1 e2      => appl   (open_rec_e k v e1) (open_rec_e k v e2)
    | call s          => call   (open_rec_st k v s)
    | inst e t        => inst   (open_rec_e k v e) t 
    | pack t0 e t1    => pack    t0 (open_rec_e k v e) t1  
end 
with open_rec_f   (k : nat) (v : var) (f : F) {struct f} : F :=
  match f with 
    | dfun tau1 tau2 s => dfun tau1 tau2 (open_rec_st (S k) v s)
    | ufun k' f        => ufun k' (open_rec_f k v f) 
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
    | retn e       => retn (close_rec_e k z e)
    | seqx s0 s1   => seqx (close_rec_st k z s0) (close_rec_st k z s1)
    | if_s e s0 s1 => if_s (close_rec_e k z e) 
                           (close_rec_st k z s0)
                           (close_rec_st k z s1)
    | while e s0   => while (close_rec_e k z e) (close_rec_st k z s0)
    | letx e s     => letx  (close_rec_e k z e) (close_rec_st (S k) z s)
    | openx e s    => openx (close_rec_e k z e) (close_rec_st (S k) z s)
    | openstar e s => openstar (close_rec_e k z e) (close_rec_st (S k) z s)
  end
with close_rec_e  (k : nat) (z : var) (e : E) : E :=
  match e with 
    | v_e v         => v_e (close_rec_v k z v)
    | i_e  i        => i_e i
    | p_e x p       => p_e (close_rec_v k z x) p
    | f_e f         => f_e (close_rec_f k z f)
    | amp e         => amp (close_rec_e k z e)
    | star e        => star (close_rec_e k z e)
    | cpair e0 e1   => cpair (close_rec_e k z e0) (close_rec_e k z e1)
    | dot e ipe     => dot (close_rec_e k z e) ipe
    | assign e0 e1  => assign (close_rec_e k z e0) (close_rec_e k z e1)
    | appl e0 e1    => appl   (close_rec_e k z e0) (close_rec_e k z e1)
    | call s        => call (close_rec_st k z s)
    | inst e t      => inst (close_rec_e k z e) t
    | pack t0 e t1  => pack t0 (close_rec_e k z e) t1
  end
with close_rec_f  (k : nat) (z : var) (f : F) : F :=
  match f with
  | dfun t1 t2 s    => dfun t1 t2 (close_rec_st (S k) z s)
  | ufun k' f       => ufun k' (close_rec_f k z f)
end.

Notation "{ k <TM_v alpha } t" := (close_rec_e k alpha t) (at level 67) : cyclone_scope.
Notation "{ k <TM_e alpha } t" := (close_rec_e k alpha t) (at level 67) : cyclone_scope.
Notation "{ k <TM_st alpha } t" := (close_rec_st k alpha t) (at level 67) : cyclone_scope.
Notation "{ k <TM_f alpha } t" := (close_rec_f k alpha t) (at level 67) : cyclone_scope.

Function close_rec (k : nat) (z : var) (t : Term) : Term :=
  match t with 
    | term_st s    => term_st (close_rec_st k z s)
    | term_e  e    => term_e  (close_rec_e k z e)
    | term_f  f    => term_f  (close_rec_f k z f)
  end.

Definition close z t := close_rec 0 z t.

Notation "{ k <TM alpha } t" := (close_rec k alpha t) (at level 67) : cyclone_scope.

(* Free term variables of terms. *)

Function fv_v (v : V) {struct v} : vars := 
  match v with
    | (bevar i) => \{}
    | (fevar x) => \{x}
  end.

Hint Extern 1 (_ \notin fv_v _) => idtac "(_ \notin fv_v _)"; trace_goal; simpl; notin_solve.

Fixpoint fv_st (t : St) {struct t} : vars :=
  match t with
    | e_s  e       => fv_e e
    | retn e       => fv_e e
    | seqx s0 s1   => (fv_st s0) \u (fv_st s1)
    | if_s e s0 s1 => (fv_e e) \u ((fv_st s0) \u (fv_st s1))
    | while e s0   => (fv_e e) \u (fv_st s0)
    | letx e s     => (fv_e e) \u (fv_st s)
    | openx e s    => (fv_e e) \u (fv_st s)
    | openstar e s => (fv_e e) \u (fv_st s)
  end
with  fv_e (e : E) {struct e} : vars := 
  match e with 
    | v_e v         => fv_v v
    | i_e  i        => \{}
    | p_e v _       => (fv_v v)
    | f_e f         => fv_f f
    | amp e         => fv_e e
    | star e        => fv_e e
    | cpair e0 e1   => (fv_e e0) \u (fv_e e1)
    | dot e _       => fv_e e
    | assign e1 e2  => (fv_e e1) \u (fv_e e2)
    | appl e1 e2    => (fv_e e1) \u (fv_e e2)
    | call s        => fv_st s 
    | inst e t      => fv_e e
    | pack t0 e t1  => fv_e e
  end
with  fv_f (f : F) {struct f} : vars := 
  match f with
  | dfun t1 t2 s => (fv_st s)
  | ufun k f     => fv_f f
end.

Hint Extern 1 (_ \notin fv_st _) => idtac "(_ \notin fv_st _)"; trace_goal; simpl; notin_solve.
Hint Extern 1 (_ \notin fv_e _) => idtac "(_ \notin fv_e _)"; trace_goal; simpl; notin_solve.
Hint Extern 1 (_ \notin fv_f _) => idtac "(_ \notin fv_f _)"; trace_goal; simpl; notin_solve.

Function fv (t : Term) {struct t} : vars :=
  match t with 
    | term_st s    => fv_st s
    | term_e  e    => fv_e e
    | term_f  f    => fv_f f 
  end.

Hint Extern 1 (_ \notin fv _) => idtac "(_ \notin fv _)"; trace_goal; simpl; notin_solve.

Definition closed_c_tm x := fv x = \{}.

(* Is a term locally closed on term variables. *)

Inductive lc_v : V -> Prop :=
  | lc_v_fevar  : forall x,  lc_v (fevar x).

Hint Constructors lc_v.

Inductive lc_st : St -> Prop := 
 | lc_st_e_s  : forall e, lc_e e -> lc_st (e_s e)
 | lc_retn    : forall e, lc_e e -> lc_st (retn e)
 | lc_seqx    : forall s0 s1, lc_st s0 -> lc_st s1 -> lc_st (seqx s0 s1)
 | lc_if      : forall e s0 s1, lc_e e -> lc_st s0 -> lc_st s1 -> lc_st (if_s e s0 s1)
 | lc_while   : forall e s, lc_e e -> lc_st s -> lc_st (while e s)
 | lc_st_letx : forall L' e (s1 : St),
                  lc_e e ->
                  (forall x, x \notin L' -> 
                             lc_st (open_rec_st 0 x s1 )) ->
                  lc_st (letx e s1)
 | lc_open   : forall L' e (s1 : St),
                  lc_e e ->
                  (forall x, x \notin L' -> 
                             lc_st (open_rec_st 0 x s1 )) ->
                  lc_st (openx e s1)
 | lc_openstar  : forall L' e (s1 : St),
                  lc_e e ->
                  (forall x, x \notin L' -> 
                             lc_st (open_rec_st 0 x s1 )) ->
                  lc_st (openstar e s1)
with      lc_e : E -> Prop :=
 | lc_v_e     : forall x, lc_v (fevar x) -> lc_e (v_e (fevar x))
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
 | lc_inst    : forall e t, lc_e e -> T.lc t -> lc_e (inst e t)
 | lc_pack    : forall t0 e t1, T.lc t0 -> lc_e e -> T.lc t1 -> 
                                lc_e (pack t0 e t1)
with      lc_f : F -> Prop :=
 | lc_dfun : forall L' s t1 t2,
               (forall x, x \notin L' -> 
                          lc_st (open_rec_st 0 x s)) ->
               lc_f (dfun t1 t2 s)
 | lc_ufun : forall k f, lc_f f -> lc_f (ufun k f).

Hint Constructors lc_e.
Hint Constructors lc_st.
Hint Constructors lc_f.

Inductive lc : Term -> Prop := 
  | lc_tm_st : forall s, lc_st s -> lc (term_st s)
  | lc_tm_e  : forall e, lc_e  e -> lc (term_e  e)
  | lc_tm_f  : forall f, lc_f  f -> lc (term_f  f).
Hint Constructors lc.

Scheme lc_st_ind_mutual := Induction for lc_st Sort Prop
with   lc_e_ind_mutual  := Induction for lc_e Sort Prop
with   lc_f_ind_mutual  := Induction for lc_f Sort Prop.
Combined Scheme lc_ind_mutual from lc_st_ind_mutual, lc_e_ind_mutual, lc_f_ind_mutual.

Definition body t :=
  exists L, forall x, x \notin L -> lc (open x t).

Function size_v (v : V) : nat :=  1.

Fixpoint size_st (t : St) {struct t} : nat :=
  match t with
    | e_s  e       => 1 + size_e e
    | retn e       => 1 + size_e e
    | seqx s0 s1   => 1 + (size_st s0) + (size_st s1)
    | if_s e s0 s1 => 1 + (size_e e) + (size_st s0) + (size_st s1)
    | while e s0   => 1 + (size_e e) + (size_st s0)
    | letx e s     => 1 + (size_e e) + (size_st s)
    | openx e s    => 1 + (size_e e) + (size_st s)
    | openstar e s => 1 + (size_e e) + (size_st s)
  end
with  size_e (e : E) {struct e} : nat := 
  match e with 
    | v_e v         => 1 + size_v v
    | i_e  i        => 1
    | p_e x p       => 1 + (length p)
    | f_e f         => 1 + size_f f
    | amp e         => 1 + size_e e
    | star e        => 1 + size_e e
    | cpair e0 e1   => 1 + (size_e e0) + (size_e e1)
    | dot e ipe     => 1 + size_e e
    | assign e1 e2  => 1 + (size_e e1) + (size_e e2)
    | appl e1 e2    => 1 + (size_e e1) + (size_e e2)
    | call s        => 1 + size_st s 
    | inst e t      => 1 + (size_e e) + (T.size t)
    | pack t0 e t1  => 1 + (T.size t0) + (size_e e) + (T.size t1)
  end
with  size_f (f : F) {struct f} : nat := 
  match f with
  | dfun t1 t2 s    => 1 + (T.size t1) + (T.size t2) + (size_st s) 
  | ufun k f        => 1 + size_f f
end.

Function size (t : Term) {struct t} : nat :=
  match t with 
    | term_st s    => 1 + size_st s
    | term_e  e    => 1 + size_e e
    | term_f  f    => 1 + size_f f 
 end.

Ltac inversion_on_lc :=
  match goal with
    | H : lc_tm_st _ |- _ => inversions H
    | H : lc_tm_e  _ |- _ => inversions H
    | H : lc_tm_f  _ |- _ => inversions H                                        
  end.

(* Sometimes one needs to invert lc (C ...) to get a simpler LC. *)

Ltac inversions_tilde_on_lc_of_concrete_term := 
  match goal with
   | H: lc_v  (_ _) |- _     => inversions~ H; inversions_tilde_on_lc_of_concrete_term
   | H: lc_st (_ _) |- _     => inversions~ H; inversions_tilde_on_lc_of_concrete_term
   | H: lc_st (_ _ _) |- _   => inversions~ H; inversions_tilde_on_lc_of_concrete_term
   | H: lc_e  (_ _) |- _     => inversions~ H; inversions_tilde_on_lc_of_concrete_term
   | H: lc_e  (_ _ _) |- _   => inversions~ H; inversions_tilde_on_lc_of_concrete_term
   | H: lc_e  (_ _ _ _) |- _ => inversions~ H; inversions_tilde_on_lc_of_concrete_term
   | H: lc_f  (_ _ _) |- _   => inversions~ H; inversions_tilde_on_lc_of_concrete_term
   | H: lc_f  (_ _ _ _) |- _ => inversions~ H; inversions_tilde_on_lc_of_concrete_term
   | |- _ => idtac
  end.

End TM.
