(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

 This defines the formal syntax, pg. 61.

*)

Set Implicit Arguments.
Require Export LanguageModuleDef.

Fixpoint subst_Tau (t : Tau) (tau : Tau) (alpha : TVar) {struct t} : Tau :=
  match t with
    | tv_t beta  => 
       if TV.eqb alpha beta then tau else T.tv_t beta
    | T.cint               => T.cint
    | T.cross t0 t1        => T.cross (subst_Tau t0 tau alpha) (subst_Tau t1 tau alpha)
    | T.arrow t0 t1        => T.arrow (subst_Tau t0 tau alpha) (subst_Tau t1 tau alpha)
    | T.ptype t0           => T.ptype (subst_Tau t0 tau alpha)
(* Bug 41, assuming beta != alpha ! Block not alpha convert.*)
    | T.utype   beta k t'  => 
       if TV.eqb alpha beta then t else T.utype beta k (subst_Tau t' tau alpha)
    | T.etype p beta k t'  => 
       if TV.eqb alpha beta then t else T.etype p beta k (subst_Tau t' tau alpha)
end.

Fixpoint subst_E (e : E) (tau : Tau) (alpha : TVar) {struct e} : E :=
 match e with 
   | i_e i        => i_e i    
   | p_e x p      => p_e x p  
   | f_e f        =>        (f_e (subst_F   f  tau alpha))
   | amp e'       => amp    (subst_E   e'     tau alpha)
   | star e'      => star   (subst_E   e'     tau alpha)
   | cpair e1 e2  => cpair  (subst_E   e1     tau alpha) (subst_E e2 tau alpha)
   | dot e' i     => dot    (subst_E   e'     tau alpha) i
   | assign e1 e2 => assign (subst_E   e1     tau alpha) (subst_E e2 tau alpha)
   | appl  e1 e2  => appl   (subst_E   e1     tau alpha) (subst_E e2 tau alpha)
   | call s       => call   (subst_St  s      tau alpha)
   | inst e' t    => inst   (subst_E   e'     tau alpha) (subst_Tau t tau alpha)
   | pack t e' t' => pack   (subst_Tau t tau alpha) (subst_E e' tau alpha) (subst_Tau t' tau alpha)
 end 
with subst_St (s: St) (tau : Tau) (alpha : TVar) {struct s} : St :=
  match s with
    | e_s e                => e_s      (subst_E e tau alpha)
    | retn e                => retn      (subst_E e tau alpha)
    | seq s1 s2            => seq      (subst_St s1 tau alpha) (subst_St s2 tau alpha)
    | if_s e s1 s2         => if_s     (subst_E e tau alpha)  (subst_St s1 tau alpha) (subst_St s2 tau alpha)
    | while e s            => while    (subst_E e tau alpha)  (subst_St s tau alpha)
    | letx x e s           => letx  x  (subst_E e tau alpha)  (subst_St s tau alpha)
    | open     e beta x s  => open     (subst_E e tau alpha) beta x (subst_St s tau alpha)
    | openstar e beta x s  => openstar (subst_E e tau alpha) beta x (subst_St s tau alpha)
end
with subst_F (f : F) (tau : Tau) (alpha : TVar) {struct f} : F  := 
 match f with 
   | (dfun tau1 x tau2 s) => 
     (dfun (subst_Tau tau1 tau alpha) x (subst_Tau tau2 tau alpha) (subst_St s tau alpha))
   (* Bug 7 from test. *)
   | ufun (TV.var b) k f => 
     match alpha with
         (TV.var a) => 
         if (beq_nat a b)
         then (ufun alpha k f)
         else  (ufun (TV.var b) k (subst_F f tau alpha))
     end
end.

Fixpoint subst_Gamma (g : Gamma) (tau : Tau) (alpha : TVar) : Gamma :=
  match g with
   | G.dot => G.dot
   | (G.ctxt x tau' g') => 
     (G.ctxt x (subst_Tau tau' tau alpha) (subst_Gamma g' tau alpha))
end.
Functional Scheme subst_Gamma_ind := Induction for subst_Gamma Sort Prop.

(* Probably should be in the tau module. *)
Function NotFreeInTau (beta : TVar) (tau : Tau) : Prop :=
  match tau with 
    | T.tv_t alpha => 
      if TV.eqb beta alpha then False else True
    | cint        => True 
    | cross t0 t1 => 
       (NotFreeInTau beta t0) /\ (NotFreeInTau beta t1)
    | arrow t0 t1 => 
        (NotFreeInTau beta t0) /\ (NotFreeInTau beta t1)
    | ptype t     => NotFreeInTau beta t
    | utype alpha _ t =>
      if TV.eqb beta alpha then True else NotFreeInTau beta t
    | etype _ alpha _ t =>  
      if TV.eqb beta alpha then True else NotFreeInTau beta t
  end.
