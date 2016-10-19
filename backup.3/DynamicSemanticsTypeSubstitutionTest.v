(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

 This defines the formal syntax, pg. 61.

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.

Require Import FormalSyntax.
Require Import DynamicSemanticsTypeSubstitution.
Require Import TestUtilities. 

(* Test substitution in types. *)
Example subst_Tau_alpha: (subst_Tau (tv_t alpha) tau alpha) = tau.
Proof.
  reflexivity.
Qed.

Example subst_Tau_beta: (subst_Tau (tv_t beta) tau alpha) = (tv_t beta).
Proof.
  reflexivity.
Qed.

Example subst_Tau_cint: (subst_Tau cint tau alpha) = cint.
Proof.
  reflexivity.
Qed.

Example subst_Tau_cross_none : 
  (subst_Tau (cross t0 t1) tau alpha) = cross t0 t1.
Proof.

  reflexivity.
Qed.

Example subst_Tau_cross_l : 
  (subst_Tau (cross (tv_t alpha) t1) tau alpha) = cross tau t1.
Proof.
  reflexivity.
Qed.

Example subst_Tau_cross_r : 
  (subst_Tau (cross t0 (tv_t alpha)) tau alpha) = cross t0 tau.
Proof.
  reflexivity.
Qed.

Example subst_Tau_arrow_l: 
  (subst_Tau (arrow (tv_t alpha) t1) tau alpha) = arrow tau t1.
Proof.
  reflexivity.
Qed.

Example subst_Tau_arrow_l_beta: 
  (subst_Tau (arrow (tv_t beta) t1) tau alpha) = arrow (tv_t beta) t1.
Proof.
  reflexivity.
Qed.

Example subst_Tau_arrow_r: 
  (subst_Tau (arrow t0 (tv_t alpha)) tau alpha) = arrow t0 tau.
Proof.
  reflexivity.
Qed.

Example subst_Tau_arrow_r_beta: 
  (subst_Tau (arrow t0 (tv_t beta)) tau alpha) = arrow t0 (tv_t beta).
Proof.
  reflexivity.
Qed.

Example subst_Tau_ptype_beta: 
  subst_Tau (ptype (tv_t beta)) tau alpha = (ptype (tv_t beta)).
Proof.
  reflexivity.
Qed.

Example subst_Tau_ptype_alpha: 
  subst_Tau (ptype (tv_t alpha)) tau alpha = (ptype tau).
Proof.
  reflexivity.
Qed.

Example subst_Tau_utype: 
  (subst_Tau (utype beta k t0) tau alpha) = (utype beta k t0).
Proof.
  reflexivity.
Qed.

Example subst_Tau_utype_alpha: 
  (subst_Tau (utype beta k (tv_t alpha)) tau alpha) = (utype beta k tau).
Proof.
  reflexivity.
Qed.

Example subst_Tau_utype_beta: 
  (subst_Tau (utype beta k (tv_t beta)) tau alpha) = 
  (utype beta k (tv_t beta)).
Proof.
  reflexivity.
Qed.

Example subst_Tau_etype: 
  (subst_Tau (etype aliases beta k t0) tau alpha) = 
  (etype aliases beta k t0).
Proof.
  reflexivity.
Qed.

Example subst_Tau_etype_alpha: 
  (subst_Tau (etype aliases beta k (tv_t alpha)) tau alpha) = 
  (etype aliases beta k tau).
Proof.
  reflexivity.
Qed.

Example subst_Tau_etype_beta:
  (subst_Tau (etype aliases beta k (tv_t beta)) tau alpha) = 
  (etype aliases beta k (tv_t beta)).
Proof.
  reflexivity.
Qed.

(* Test substitution in expressions. *)
Example subst_E_i_e_i : (subst_E (i_e i) tau alpha) = (i_e i).
Proof.
 reflexivity.
Qed.

Example subst_E_p_e : (subst_E (p_e x pdot) tau alpha) = p_e x pdot.
Proof.
 reflexivity.
Qed.

(* TODO Need to be actually recursing into the F here.
   So I need an f with an alpha in it. *)
Example subst_E_f_e  : 
  (subst_E (f_e f) tau alpha) = f_e f.
Proof.
  reflexivity.
Qed.

Example subst_E_f_e_alpha  : 
  (subst_E (f_e faa) tau alpha) = f_e f.
Proof.
  compute.
  reflexivity.
Qed.

Example subst_E_f_e_beta  : 
  (subst_E (f_e fbb) tau alpha) = f_e fbb.
Proof.
  reflexivity.
Qed.

(* Bug 5, not recursing through function wrapper. *)
Example subst_E_dfun : 
  (subst_E (f_e (dfun tau x tau (retn (p_e x pdot)))) tau alpha) =
  (f_e (dfun tau x tau (retn (p_e x pdot)))).
Proof.
 reflexivity.
Qed.

Example subst_E_amp_no_alpha : (subst_E (amp e') tau alpha) = amp e'.
Proof.
 reflexivity.
Qed.

Example subst_E_star : (subst_E (star e') tau alpha) = star e'.
Proof.
 reflexivity.
Qed.

Example subst_E_cpair : 
  (subst_E (cpair e1 e2) tau alpha) = cpair e1 e2.
Proof.
 reflexivity.
Qed.

Example subst_E_dot : (subst_E (dot e' i) tau alpha) = dot e' i.
Proof.
 reflexivity.
Qed.

Example subst_E_assign : 
  (subst_E (assign e1 e2) tau alpha) = assign e1 e2.
Proof.
 reflexivity.
Qed.

Example subst_E_appl : (subst_E (appl  e1 e2) tau alpha) = appl  e1 e2.
Proof.
 reflexivity.
Qed.

Example subst_E_call : (subst_E (call s) tau alpha) = call s.
Proof.
 reflexivity.
Qed.

Example subst_E_inst : (subst_E (inst e' t0) tau alpha) = inst e' t0.
Proof.
 reflexivity.
Qed.

Example subst_E_pack : 
  (subst_E (pack t e' t1) tau alpha) = pack t e' t1.
Proof.
 reflexivity.
Qed.

(* Test substitution in statements. *)

Example subst_St_e_s_none: 
  (subst_St (e_s e) tau alpha) = (e_s e).
Proof.
 reflexivity.
Qed.

Example subst_St_e_s_alpha: 
  (subst_St (e_s (f_e faa)) tau alpha) = (e_s (f_e f)).
Proof.
 reflexivity.
Qed.

Example subst_St_e_s_beta: 
  (subst_St (e_s (f_e fbb)) tau alpha) = (e_s (f_e fbb)).
Proof.
  reflexivity.
Qed.

Example subst_St_retn_none: 
  (subst_St (retn (f_e f)) tau alpha) = retn (f_e f).
Proof.
 reflexivity.
Qed.

Example subst_St_retn_alpha: 
  (subst_St (retn (f_e faa)) tau alpha) = 
                       retn (f_e f).
Proof.
 reflexivity.
Qed.

Example subst_St_retn_beta: 
  (subst_St (retn (f_e fbb)) tau alpha) = 
                       retn (f_e fbb).
Proof.
 reflexivity.
Qed.

Example subst_St_seq_none: 
  (subst_St (seq applff applff) tau alpha) = (seq applff applff).
Proof.
 reflexivity.
Qed.

Example subst_St_seq_alpha: 
  (subst_St (seq applfaa applfaa) tau alpha) = (seq applff applff).
Proof.
 reflexivity.
Qed.

Example subst_St_seq_beta: 
  (subst_St (seq applfbb applfbb) tau alpha) = (seq applfbb applfbb).
Proof.
 reflexivity.
Qed.

Example subst_St_if_s_none: 
  (subst_St (if_s e s1 s2) tau alpha) = (if_s e s1 s2).
Proof.
 reflexivity.
Qed.

Example subst_St_if_s_alpha: 
  (subst_St (if_s (f_e faa) applfaa applfaa) tau alpha) = 
            (if_s (f_e f)   applff   applff).
Proof.
 reflexivity.
Qed.

Example subst_St_if_s_beta:
  (subst_St (if_s (f_e fbb) applfbb applfbb) tau alpha) = 
            (if_s (f_e fbb)  applfbb applfbb).
Proof.
 reflexivity.
Qed.

Example subst_St_while_none: 
  (subst_St (while e s) tau alpha) = (while e s).
Proof.
 reflexivity.
Qed.

Example subst_St_while_alpha: 
  (subst_St (while (f_e faa) applfaa) tau alpha) = 
            (while (f_e f) applff).
Proof.
 reflexivity.
Qed.

Example subst_St_while_beta:
  (subst_St (while (f_e fbb) applfbb) tau alpha) = 
            (while (f_e fbb) applfbb).
Proof.
 reflexivity.
Qed.

Example subst_St_letx_none: 
  (subst_St (letx x e s) tau alpha) = (letx x e s).
Proof.
 reflexivity.
Qed.

Example subst_St_letx_alpha:
  (subst_St (letx x (f_e faa) applfaa) tau alpha) = 
            (letx x (f_e f) applff).
Proof.
 reflexivity.
Qed.

Example subst_St_letx_beta:
  (subst_St (letx x (f_e fbb) applfbb) tau alpha) = 
            (letx x (f_e fbb) applfbb).
Proof.
 reflexivity.
Qed.

Example subst_St_open_none: 
  (subst_St (open e gamma x s) tau alpha) = 
            (open e gamma x s).
Proof.
 reflexivity.
Qed.

Example subst_St_open_alpha: 
  (subst_St (open (f_e faa) gamma x applfaa) tau alpha) = 
            (open (f_e f  ) gamma x applff).
Proof.
 reflexivity.
Qed.

Example subst_St_open_beta:
  (subst_St (open (f_e fbb) gamma x applfbb) tau alpha) = 
            (open (f_e fbb) gamma x applfbb).
Proof.
 reflexivity.
Qed.

Example subst_St_openstar_none: 
  (subst_St (openstar e gamma x s) tau alpha) = 
            (openstar e gamma x s).
Proof.
 reflexivity.
Qed.

Example subst_St_openstar_alpha: 
  (subst_St (openstar (f_e faa) gamma x applfaa) tau alpha) = 
            (openstar (f_e f  ) gamma x applff).
Proof.
 reflexivity.
Qed.

Example subst_St_openstar_beta:
  (subst_St (openstar (f_e fbb) gamma x applfbb) tau alpha) = 
            (openstar (f_e fbb) gamma x applfbb).
Proof.
 reflexivity.
Qed.

Example subst_F_dfun_none: 
  (subst_F f tau alpha) = f.
Proof.
  reflexivity.
Qed.

Example subst_F_dfun_alpha: 
  (subst_F faa tau alpha) = f.
Proof.
  reflexivity.
Qed.

Example subst_F_dfun_beta:
  (subst_F fbb tau alpha) = fbb.
Proof.
  reflexivity.
Qed.

Example subst_F_ufun_non:
  (subst_F (ufun gamma k f) tau alpha) =
           (ufun gamma k f).
Proof.
 reflexivity.
Qed.

Example subst_F_ufun_alpha:
  (subst_F (ufun gamma k faa) tau alpha) =
           (ufun gamma k f).
Proof.
 reflexivity.
Qed.

Example subst_F_ufun_beta:
  (subst_F (ufun gamma k fbb) tau alpha) =
           (ufun gamma k fbb).
Proof.
 reflexivity.
Qed.

(* Bug 7 found here, did not get alpha binding in subst_F right. *)
Example subst_F_ufun_alpha_bound:
  (subst_F (ufun alpha k faa) tau alpha) =
           (ufun alpha k faa).
Proof.
 reflexivity.
Qed.

Example NotFreeInTau_int :
  NotFreeInTau beta cint = true.
Proof.
  reflexivity.
Qed.

Example NotFreeInTau_intcrossint :
  NotFreeInTau beta (cross cint cint) = true.
Proof.
  reflexivity.
Qed.

Example NotFreeInTau_intcrossint_1 :
  NotFreeInTau beta (cross (tv_t beta) cint) = false.
Proof.
  reflexivity.
Qed.

Example NotFreeInTau_intcrossint_2 :
  NotFreeInTau beta (cross cint (tv_t beta)) = false.
Proof.
  reflexivity.
Qed.

Example NotFreeInTau_intarrow :
  NotFreeInTau beta (arrow cint cint) = true.
Proof.
  reflexivity.
Qed.

Example NotFreeInTau_intarrow_1:
  NotFreeInTau beta (arrow (tv_t beta) cint) = false.
Proof.
  reflexivity.
Qed.

Example NotFreeInTau_intarrow_2:
  NotFreeInTau beta (arrow cint (tv_t beta)) = false.
Proof.
  reflexivity.
Qed.

Example NotFreeInTau_ptype: 
  NotFreeInTau beta (ptype cint) = true.
Proof.
  reflexivity.
Qed.

Example NotFreeInTau_ptype_false:
  NotFreeInTau beta (ptype (tv_t beta)) = false.
Proof.
  reflexivity.
Qed.

Example NotFreeInTau_utype_bound:
  NotFreeInTau beta (utype beta A cint) = true.
Proof.
  reflexivity.
Qed.

Example NotFreeInTau_utype_bound_2:
  NotFreeInTau beta (utype beta A (tv_t beta)) = true.
Proof.
  reflexivity.
Qed.

Example NotFreeInTau_utype_bound_3:
  NotFreeInTau beta (utype alpha A (tv_t beta)) = false.
Proof.
  reflexivity.
Qed.

Example NotFreeInTau_etype_bound:
  NotFreeInTau beta (etype aliases beta A cint) = true.
Proof.
  reflexivity.
Qed.

Example NotFreeInTau_etype_bound_2:
  NotFreeInTau beta (etype aliases beta A (tv_t beta)) = true.
Proof.
  reflexivity.
Qed.

Example NotFreeInTau_etype_bound_3:
  NotFreeInTau beta (etype aliases alpha A (tv_t beta)) = false.
Proof.
  reflexivity.
Qed.




