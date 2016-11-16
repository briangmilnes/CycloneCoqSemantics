(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION".   Daniel Grossman, August 2003 *)
(* Definitions from Section 3.5.2 *)
(* Brian Milnes 2016 *)

(* Questions:
   Do I need context substitution?  Yes, two forms.
*)

Set Implicit Arguments.
Require Export Cyclone_Formal_Syntax.

(* Substituting a type into a type for a type variable. *)

Fixpoint subst_t_tv_t  (tau : Tau) (alpha : var) (t : Tau) {struct t} : Tau := 
  match t with 
    | btvar i      => btvar i
    | ftvar beta   => If (alpha = beta) then tau else (ftvar beta)
    | cint         => cint
    | cross t0 t1  => cross (subst_t_tv_t tau alpha t0) (subst_t_tv_t tau alpha t1)
    | arrow t0 t1  => arrow (subst_t_tv_t tau alpha t0) (subst_t_tv_t tau alpha t1)
    | ptype t0     => ptype (subst_t_tv_t tau alpha t0)
    | utype k t0   => utype k (subst_t_tv_t tau alpha t0)
    | etype p k t0 => etype p k (subst_t_tv_t tau alpha t0)
end.

Hint Resolve subst_t_tv_t.

Notation "[ t 'ttvt>' alpha ] tm" := (subst_t_tv_t t alpha tm) (at level 68) : cyclone_scope.

(* Substituting a type variable into a term. *)

(* This is identity but I fill it out in the hopes it affects inversion. *)
Function subst_t_tv_tm_v (tau : Tau) (alpha : var) (v : V) {struct v} : V := 
  match v with
    | fevar i => fevar i
    | bevar i => bevar i
  end.

Hint Resolve subst_t_tv_tm_v.

Fixpoint subst_t_tv_tm_e (tau : Tau) (alpha : var) (e : E) {struct e} : E :=
 match e with 
   | v_e v         => v_e (subst_t_tv_tm_v tau alpha v)
   | i_e i         => i_e i
   | p_e x p       => p_e x p
   | f_e f         =>        (f_e (subst_t_tv_tm_f  tau alpha f))
   | amp e'        => amp    (subst_t_tv_tm_e     tau alpha e')
   | star e'       => star   (subst_t_tv_tm_e     tau alpha e')
   | cpair e1 e2   => cpair  (subst_t_tv_tm_e     tau alpha e1) (subst_t_tv_tm_e tau alpha e2)
   | dot e' i      => dot    (subst_t_tv_tm_e     tau alpha e') i
   | assign e1 e2  => assign (subst_t_tv_tm_e     tau alpha e1) (subst_t_tv_tm_e tau alpha e2)
   | appl  e1 e2   => appl   (subst_t_tv_tm_e     tau alpha e1) (subst_t_tv_tm_e tau alpha e2)
   | call s        => call   (subst_t_tv_tm_st    tau alpha s)
   | inst e' t     => inst   (subst_t_tv_tm_e     tau alpha e') (subst_t_tv_t tau alpha t)
   | pack t e' t'  => pack   (subst_t_tv_t tau alpha t) (subst_t_tv_tm_e tau alpha e')
                             (subst_t_tv_t tau alpha t')
 end 
with subst_t_tv_tm_st (tau : Tau) (alpha : var) (s: St) {struct s} : St :=
  match s with
    | e_s e         => e_s      (subst_t_tv_tm_e tau alpha e)
    | retn e        => retn     (subst_t_tv_tm_e tau alpha e)
    | seq s1 s2     => seq      (subst_t_tv_tm_st tau alpha s1) (subst_t_tv_tm_st tau alpha s2)
    | if_s e s1 s2  => if_s     (subst_t_tv_tm_e tau alpha e)
                                (subst_t_tv_tm_st tau alpha s1) (subst_t_tv_tm_st tau alpha s2)
    | while e s     => while    (subst_t_tv_tm_e tau alpha e)   (subst_t_tv_tm_st tau alpha s)
    | letx e s      => letx     (subst_t_tv_tm_e tau alpha e)   (subst_t_tv_tm_st tau alpha s)
    | open     e s  => open     (subst_t_tv_tm_e tau alpha e)   (subst_t_tv_tm_st tau alpha s)
    | openstar e s  => openstar (subst_t_tv_tm_e tau alpha e)   (subst_t_tv_tm_st tau alpha s)
end
with subst_t_tv_tm_f (tau : Tau) (alpha : var) (f : F) {struct f} : F  := 
 match f with 
   | (dfun tau1 tau2 s) => 
     (dfun (subst_t_tv_t tau alpha tau1) (subst_t_tv_t tau alpha tau2) (subst_t_tv_tm_st tau alpha s))
   | ufun k f => (ufun k (subst_t_tv_tm_f tau alpha f))
end.


Hint Resolve subst_t_tv_tm_e.
Hint Resolve subst_t_tv_tm_st.
Hint Resolve subst_t_tv_tm_f.

Notation "[ t 'ttvtm_v>'  alpha ] tm" := (subst_t_tv_tm_v  t alpha tm) (at level 68) : cyclone_scope.
Notation "[ t 'ttvtm_e>'  alpha ] tm" := (subst_t_tv_tm_e  t alpha tm) (at level 68) : cyclone_scope.
Notation "[ t 'ttvtm_st>' alpha ] tm" := (subst_t_tv_tm_st t alpha tm) (at level 68) : cyclone_scope.
Notation "[ t 'ttvtm_f>'  alpha ] tm" := (subst_t_tv_tm_f  t alpha tm) (at level 68) : cyclone_scope.

Function subst_t_tv_tm (tau : Tau) (alpha : var) (t: Term) {struct t} : Term :=
  match t with
    | term_st s => term_st (subst_t_tv_tm_st tau alpha s)
    | term_e  e => term_e  (subst_t_tv_tm_e tau alpha e)
    | term_f  f => term_f  (subst_t_tv_tm_f tau alpha f)
  end.

Hint Resolve subst_t_tv_tm.

Notation "[ t 'ttvtm>' alpha ] tm" := (subst_t_tv_tm t alpha tm) (at level 68) : cyclone_scope.
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

Function subst_v_v_tm_v (x y : var) (v : V) : V :=
  match v with
   | (bevar y)   => (bevar y)
   | (fevar y)   => If (x = y) then (fevar x) else (fevar y)
end.

Fixpoint subst_v_v_tm_e (x y : var) (e : E) {struct e} : E := 
 match e with 
   | v_e v         => v_e (subst_v_v_tm_v x y v)
   | i_e i         => e
   | p_e v p       => p_e (subst_v_v_tm_v x y v) p
   | f_e f         =>        (f_e (subst_v_v_tm_f x y f))
   | amp e'        => amp    (subst_v_v_tm_e   x y e')
   | star e'       => star   (subst_v_v_tm_e   x y e')
   | cpair e1 e2   => cpair  (subst_v_v_tm_e   x y e1) (subst_v_v_tm_e x y e2)
   | dot e' i      => dot    (subst_v_v_tm_e   x y e') i
   | assign e1 e2  => assign (subst_v_v_tm_e   x y e1) (subst_v_v_tm_e x y e2)
   | appl   e1 e2  => appl   (subst_v_v_tm_e   x y e1) (subst_v_v_tm_e x y e2)
   | call s        => call   (subst_v_v_tm_st  x y s)
   | inst e' t     => inst   (subst_v_v_tm_e   x y e') t
   | pack t e' t'  => pack   t (subst_v_v_tm_e x y e') t'
 end 
with subst_v_v_tm_st (x y : var ) (s: St) {struct s} : St :=
  match s with
    | e_s e         => e_s      (subst_v_v_tm_e x y e)
    | retn e        => retn     (subst_v_v_tm_e x y e)
    | seq s1 s2     => seq      (subst_v_v_tm_st x y s1) (subst_v_v_tm_st x y s2)
    | if_s e s1 s2  => if_s     (subst_v_v_tm_e x y e) 
                                (subst_v_v_tm_st x y s1) (subst_v_v_tm_st x y s2)
    | while e s     => while    (subst_v_v_tm_e x y e)   (subst_v_v_tm_st x y s)
    | letx e s      => letx     (subst_v_v_tm_e x y e)   (subst_v_v_tm_st x y s)
    | open     e s  => open     (subst_v_v_tm_e x y e)   (subst_v_v_tm_st x y s)
    | openstar e s  => openstar (subst_v_v_tm_e x y e)   (subst_v_v_tm_st x y s)
end
with subst_v_v_tm_f (x y : var) (f : F) {struct f} : F  := 
 match f with 
   | (dfun tau1 tau2 s) => (dfun tau1 tau2 (subst_v_v_tm_st x y s))
   | ufun k f => (ufun k (subst_v_v_tm_f x y f))
 end.

Notation "[ x 'vtm_v>' y ] tm" := (subst_v_v_tm_v x y tm) (at level 68) : cyclone_scope.
Notation "[ x 'vtm_e>' y ] tm" := (subst_v_v_tm_e x y tm) (at level 68) : cyclone_scope.
Notation "[ x 'vtm_st>' y ] tm" := (subst_v_v_tm_st x y tm) (at level 68) : cyclone_scope.
Notation "[ x 'vtm_f>' y ] tm" := (subst_v_v_tm_f x y tm) (at level 68) : cyclone_scope.

Function subst_v_v_tm (x y : var) (t : Term) {struct t} :=
  match t with
    | term_st s => term_st (subst_v_v_tm_st x y s)
    | term_e  e => term_e  (subst_v_v_tm_e  x y e)
    | term_f  f => term_f  (subst_v_v_tm_f  x y f)
end.

Notation "[ x 'vtm>' y ] tm" := (subst_v_v_tm x y tm) (at level 68) : cyclone_scope.
