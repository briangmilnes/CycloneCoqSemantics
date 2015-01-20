(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Equalities over the FormalSyntax.

*)
Require Import List.
Export ListNotations.
Require Export ZArith.
Require Import Init.Datatypes.

Require Import DynamicSemanticsTypeSubstitution.
Require Export CpdtTactics.
Require Export Case.
Require Import FormalSyntax.

Set Implicit Arguments.



(* Equalities *)

Fixpoint beq_evar_p(ep ep' : EVar * P) : bool :=
  match ep, ep' with 
   | (e,p), (e',p') =>
     andb (beq_evar e e') (beq_path p p')
  end.

Fixpoint beq_phi (phi phi' : Phi) : bool :=
match phi, phi' with
   | witnesschanges, witnesschanges => true
   | aliases, aliases => true
   | _, _ => false
end.

Fixpoint beq_tau (t t' : Tau) : bool :=
 match t, t with
 | 
 | cint, cint => true
 | (cross t0 t1), (cross t0' t1') => andb (beq_tau t0 t0') (beq_tau t1 t1')
 | (arrow t0 t1), (arrow t0' t1') => andb (beq_tau t0 t0') (beq_tau t1 t1')
 | (ptype t0), (ptype t0')        => beq_tau t0 t0'
 | (utype alpha k t1), (utype beta k' t1') 
   => andb (beq_kappa k k') (beq_tau t1 (subst_Tau t1' (tv_t alpha) beta))
 | (etype phi alpha k t1), (etype phi' beta k' t1') 
   => 
   (andb 
      (andb (beq_phi phi phi') (beq_tvar alpha beta))
      (andb (beq_kappa k k') (beq_tau t1 t1')))
 | _ , _ => false
end.

Fixpoint beq_i (i i' : I) : bool :=
  match i, i' with
    | i_i i, i_i i' => Zeq_bool i i'
 end.

Fixpoint beq_ipe (ipe ipe' : IPE) : bool :=
 match ipe, ipe' with
  | zero_pe, zero_pe => true
  | one_pe, one_pe => true
  | _, _ => false
end.

Fixpoint beq_pe (pe pe': PE) : bool :=
 match pe, pe' with
  | i_pe ipe, i_pe ipe' => beq_ipe ipe ipe'
  | u_pe, u_pe          => true
  | _, _                => false
end.

Fixpoint beq_st (s s' : St) : bool := 
  match s, s' with
    | (e_s e), (e_s e') => beq_e e e'
    | retn e, retn e'   => beq_e e e'
    | seq s1 s2, seq s1' s2' => andb (beq_st s1 s1') (beq_st s2 s2')
    | if_s e s1 s2, if_s e' s1' s2' =>
      andb (andb (beq_e e e') (beq_st s1 s1'))
           (beq_st s2 s2')
    | while e s, while e' s' => andb (beq_e e e') (beq_st s s')
    | letx x e s, letx x' e' s' =>
       andb (andb (beq_evar x x') (beq_e e e')) (beq_st s s')
    | open e alpha x s, open e' beta x' s' =>
      andb (andb (beq_e e e')    (beq_tvar alpha beta))
           (andb (beq_evar x x') (beq_st s s'))
    | openstar e alpha x s, openstar e' beta x' s' =>
      andb (andb (beq_e e e')    (beq_tvar alpha beta))
           (andb (beq_evar x x') (beq_st s s'))
    | _, _ => false
  end
with beq_e (e e' : E) : bool := 
 match e, e' with 
 | i_e i, i_e i'                 => beq_i i i'
 | p_e x p, p_e x' p'            => andb (beq_evar x x') (beq_path p p')
 | f_e f, f_e f'                 => beq_f f f'
 | amp e, amp e'                 => beq_e e e'
 | star e, star e'               => beq_e e e'
 | cpair e0 e1, cpair e0' e1'    => andb (beq_e e0 e0') (beq_e e1 e1')
 | dot e ipe, dot e' ipe'        => andb (beq_e e e') (beq_ipe ipe ipe')
 | assign e1 e2, assign e1' e2'  => andb (beq_e e1 e1') (beq_e e2 e2')
 | appl e1 e2, appl e1' e2'      => andb (beq_e e1 e1') (beq_e e2 e2')
 | call s, call s'               => beq_st s s'
 | inst e t, inst e' t'          => andb (beq_e e e') (beq_tau t t')
 | pack t0 e t1, pack t0' e' t1' => andb (andb (beq_tau t0 t0') (beq_e e e'))
                                         (beq_tau t1 t1')
 | _, _ => false
end
with beq_f (f f' : F) : bool :=
 match  f, f with 
 | dfun t0 x t1 s, dfun t0' x' t1' s' => 
   (andb (andb (beq_tau t0 t0') (beq_evar x x'))
         (andb (beq_tau t1 t1') (beq_st s s')))
 | ufun a k f, ufun a' k' f'     => (andb (andb (beq_tvar a a') (beq_kappa k k'))
                                          (beq_f f f'))
 | _, _ => false
end.
