(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION".   Daniel Grossman, August 2003 *)
(* Definitions from Section 3.5.2 *)
(* Brian Milnes 2016 *)

(* Questions:
   Do I need context substitution?  Yes, two forms.
*)

Set Implicit Arguments.
Require Export Cyclone_Formal_Syntax.

(* BUG: I should correctly reorder things: this for that in X. *)

(* Substituting a type into a type for a type variable. *)

Fixpoint subst_tau  (tau : Tau) (alpha : var) (t : Tau) {struct t} : Tau := 
  match t with 
    | btvar i      => btvar i
    | ftvar beta   => If (alpha = beta) then tau else (ftvar beta)
    | cint         => cint
    | cross t0 t1  => cross (subst_tau tau alpha t0) (subst_tau tau alpha t1)
    | arrow t0 t1  => arrow (subst_tau tau alpha t0) (subst_tau tau alpha t1)
    | ptype t0     => ptype (subst_tau tau alpha t0)
    | utype k t0   => utype k (subst_tau tau alpha t0)
    | etype p k t0 => etype p k (subst_tau tau alpha t0)
end.

(* Notation "[ tau0 ~ty~> alpha ] trm" := (subst_tau tau0 alpha trm) (at level 68). *)

(* Substituting a type variable into a term. *)

(* This is identity but I fill it out in the hopes it affects inversion. *)
Function subst_tau_v (tau : Tau) (alpha : var) (v : V) {struct v} : V := 
  match v with
    | fevar i => fevar i
    | bevar i => bevar i
  end.

Fixpoint subst_tau_e (tau : Tau) (alpha : var) (e : E) {struct e} : E :=
 match e with 
   | v_e v         => v_e (subst_tau_v tau alpha v)
   | i_e i         => i_e i
   | p_e x p       => p_e x p
   | f_e f         =>        (f_e (subst_tau_f  tau alpha f))
   | amp e'        => amp    (subst_tau_e     tau alpha e')
   | star e'       => star   (subst_tau_e     tau alpha e')
   | cpair e1 e2   => cpair  (subst_tau_e     tau alpha e1) (subst_tau_e tau alpha e2)
   | dot e' i      => dot    (subst_tau_e     tau alpha e') i
   | assign e1 e2  => assign (subst_tau_e     tau alpha e1) (subst_tau_e tau alpha e2)
   | appl  e1 e2   => appl   (subst_tau_e     tau alpha e1) (subst_tau_e tau alpha e2)
   | call s        => call   (subst_tau_st    tau alpha s)
   | inst e' t     => inst   (subst_tau_e     tau alpha e') (subst_tau tau alpha t)
   | pack t e' t'  => pack   (subst_tau tau alpha t) (subst_tau_e tau alpha e')
                             (subst_tau tau alpha t')
 end 
with subst_tau_st (tau : Tau) (alpha : var) (s: St) {struct s} : St :=
  match s with
    | e_s e         => e_s      (subst_tau_e tau alpha e)
    | retn e        => retn     (subst_tau_e tau alpha e)
    | seq s1 s2     => seq      (subst_tau_st tau alpha s1) (subst_tau_st tau alpha s2)
    | if_s e s1 s2  => if_s     (subst_tau_e tau alpha e)
                                (subst_tau_st tau alpha s1) (subst_tau_st tau alpha s2)
    | while e s     => while    (subst_tau_e tau alpha e)   (subst_tau_st tau alpha s)
    | letx e s      => letx     (subst_tau_e tau alpha e)   (subst_tau_st tau alpha s)
    | open     e s  => open     (subst_tau_e tau alpha e)   (subst_tau_st tau alpha s)
    | openstar e s  => openstar (subst_tau_e tau alpha e)   (subst_tau_st tau alpha s)
end
with subst_tau_f (tau : Tau) (alpha : var) (f : F) {struct f} : F  := 
 match f with 
   | (dfun tau1 tau2 s) => 
     (dfun (subst_tau tau alpha tau1) (subst_tau tau alpha tau2) (subst_tau_st tau alpha s))
   | ufun k f => (ufun k (subst_tau_f tau alpha f))
end.

(*
Notation "[ tau0 ~tyv~> alpha ] trm"  := (subst_tau_v  tau0 alpha trm) (at level 68).
Notation "[ tau0 ~tye~> alpha ] trm"  := (subst_tau_e  tau0 alpha trm) (at level 68).
Notation "[ tau0 ~tyst~> alpha ] trm" := (subst_tau_st tau0 alpha trm) (at level 68).
Notation "[ tau0 ~tyf~> alpha ] trm"  := (subst_tau_f  tau0 alpha trm) (at level 68).
*)

Function subst_tau_term (tau : Tau) (alpha : var) (t: Term) {struct t} : Term :=
  match t with
    | term_st s => term_st (subst_tau_st tau alpha s)
    | term_e  e => term_e  (subst_tau_e tau alpha e)
    | term_f  f => term_f  (subst_tau_f tau alpha f)
  end.

(* Notation "[ tau0 ~tytm~> alpha ] trm" := (subst_tau_term tau0 alpha trm) (at level 68).*)

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

(*
Fixpoint p_e_x_p_to_e_dot_i (e : E) (p: list PE) {struct p} : E :=
  match p with
   | nil => e
   | (cons i p') => p_e_x_p_to_e_dot_i (dot e i) p'
  end.

Fixpoint subst_e_e (e : E) (e' : E) (x : var) {struct e} : E :=
 match e with 
   | v_e (bevar y)   => e
   | v_e (fevar y)   => If (x = y) then e' else e
   | i_e i           => e
   | p_e (bevar y) p => e
   | p_e (fevar y) p => If (x = y) then p_e_x_p_to_e_dot_i e' p else e (* wrong *)
   | f_e f         =>        (f_e (subst_e_f   f e' x))
   | amp e'        => amp    (subst_e_e   e'     e' x)
   | star e'       => star   (subst_e_e   e'     e' x)
   | cpair e1 e2   => cpair  (subst_e_e   e1     e' x) (subst_e_e e2 e' x)
   | dot e' i      => dot    (subst_e_e   e'     e' x) i
   | assign e1 e2  => assign (subst_e_e   e1     e' x) (subst_e_e e2 e' x)
   | appl  e1 e2   => appl   (subst_e_e   e1     e' x) (subst_e_e e2 e' x)
   | call s        => call   (subst_e_st  s      e' x)
   | inst e' t     => inst   (subst_e_e   e'     e' x) t 
   | pack t e' t'  => pack    t (subst_e_e e' e' x) t'
 end 
with subst_e_st (s: St) (e' : E) (x : var) {struct s} : St :=
  match s with
    | e_s e         => e_s      (subst_e_e e e' x)
    | retn e        => retn     (subst_e_e e e' x)
    | seq s1 s2     => seq      (subst_e_st s1 e' x) (subst_e_st s2 e' x)
    | if_s e s1 s2  => if_s     (subst_e_e e e' x)   (subst_e_st s1 e' x) (subst_e_st s2 e' x)
    | while e s     => while    (subst_e_e e e' x)   (subst_e_st s e' x)
    | letx e s      => letx     (subst_e_e e e' x)   (subst_e_st s e' x)
    | open     e s  => open     (subst_e_e e e' x)   (subst_e_st s e' x)
    | openstar e s  => openstar (subst_e_e e e' x)   (subst_e_st s e' x)
end
with subst_e_f (f : F) (e' : E) (x : var) {struct f} : F  := 
 match f with 
   | (dfun tau1 tau2 s) => (dfun tau1 tau2 (subst_e_st s e' x))
   | ufun k f => (ufun k (subst_e_f f e' x))
 end.

Fixpoint subst_e_term (t: Term) (e' : E) (x : var) {struct t} : Term :=
  match t with
    | term_st s => term_st (subst_e_st s e' x)
    | term_e  e => term_e  (subst_e_e  e e' x)
    | term_f  f => term_f  (subst_e_f  f e' x)
end.

Notation "[ tau0 ~ev~> x ] trm"  := (subst_e_v  tau0 x trm) (at level 68).
Notation "[ tau0 ~ee~> x ] trm"  := (subst_e_e  tau0 x trm) (at level 68).
Notation "[ tau0 ~est~> x ] trm" := (subst_e_st tau0 x trm) (at level 68).
Notation "[ tau0 ~ef~> x ] trm"  := (subst_e_f  tau0 x trm) (at level 68).
Notation "[ tau0 ~etm~> x ] trm" := (subst_e_term tau0 x trm) (at level 68).
 *)
