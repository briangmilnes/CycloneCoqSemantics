(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

 This defines the formal syntax, pg. 61.

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Coq.Bool.Bool.

Require Import FormalSyntax.

Fixpoint subst_Tau (t : Tau) (tau : Tau) (alpha : TVar) {struct t} : Tau :=
  match t with
    | tv_t (tvar b) => 
      match alpha with 
        | (tvar a) => if beq_nat a b then tau else tv_t (tvar b)
      end
    | cint               => cint
    | cross t0 t1        => cross (subst_Tau t0 tau alpha) (subst_Tau t1 tau alpha)
    | arrow t0 t1        => arrow (subst_Tau t0 tau alpha) (subst_Tau t1 tau alpha)
    | ptype t0           => ptype (subst_Tau t0 tau alpha)
    | utype   beta k t'  => utype   beta k (subst_Tau t' tau alpha)
    | etype p beta k t'  => etype p beta k (subst_Tau t' tau alpha)
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
   | ufun (tvar b) k f => 
     match alpha with
         (tvar a) => 
         if (beq_nat a b)
         then (ufun alpha k f)
         else  (ufun (tvar b) k (subst_F f tau alpha))
     end
end.

Fixpoint subst_Gamma (g : Gamma) (tau : Tau) (alpha : TVar) : Gamma :=
  match g with
   | [] => []
   | (x, tau') :: g' => 
     (x, (subst_Tau tau' tau alpha)) ::
           (subst_Gamma g' tau alpha)
end.

Fixpoint NotFreeInTau (beta : TVar) (tau : Tau) : bool :=
  let n1 := (match beta with tvar n1 => n1 end) in
  match tau with 
    | tv_t (tvar n0) => 
      if beq_nat n0 n1 then false else true
    | cint        => true 
    | cross t0 t1 => 
      if eqb true (NotFreeInTau beta t0) then NotFreeInTau beta t1 else false
    | arrow t0 t1 => 
      if eqb true (NotFreeInTau beta t0) then NotFreeInTau beta t1 else false
    | ptype t     => NotFreeInTau beta t
    | utype (tvar n0) _ t =>
      if beq_nat n0 n1 then true else NotFreeInTau beta t
    | etype _ (tvar n0) _ t =>  
      if beq_nat n0 n1 then true else NotFreeInTau beta t
  end.

