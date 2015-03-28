(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

 This defines the formal syntax, pg. 61.

*)
Set Implicit Arguments.
Require Export LanguageModuleDef.
Require Import TestUtilities. 
Require Import DynamicSemanticsTypeSubstitution.

(* TODO what about substitution over bound type variables? 
  Not Needed I think. *)
(* Test substitution in types. *)
Example subst_Tau_alpha: (subst_Tau (ftvar alpha) tau alpha) = tau.
Proof.
  reflexivity.
Qed.

Example subst_Tau_beta: (subst_Tau (ftvar beta) tau alpha) = (ftvar beta).
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

Example subst_Tau_partial:
  (subst_Tau (cross cint cint)  t1 alpha) = cross cint cint.
Proof.
  reflexivity.
Qed.

Example subst_Tau_cross_0 : 
  (subst_Tau (cross (ftvar alpha) (ftvar alpha)) cint alpha) = 
   cross cint cint.
Proof.
  reflexivity.
Qed.

Example subst_Tau_cross_l : 
  (subst_Tau (cross (ftvar alpha) t1) tau alpha) = cross tau t1.
Proof.
  reflexivity.
Qed.

Example subst_Tau_cross_r : 
  (subst_Tau (cross t0 (ftvar alpha)) tau alpha) = cross t0 tau.
Proof.
  reflexivity.
Qed.

Example subst_Tau_arrow_l: 
  (subst_Tau (arrow (ftvar alpha) t1) tau alpha) = arrow tau t1.
Proof.
  reflexivity.
Qed.

Example subst_Tau_arrow_l_beta: 
  (subst_Tau (arrow (ftvar beta) t1) tau alpha) = arrow (ftvar beta) t1.
Proof.
  reflexivity.
Qed.

Example subst_Tau_arrow_r: 
  (subst_Tau (arrow t0 (ftvar alpha)) tau alpha) = arrow t0 tau.
Proof.
  reflexivity.
Qed.

Example subst_Tau_arrow_r_beta: 
  (subst_Tau (arrow t0 (ftvar beta)) tau alpha) = arrow t0 (ftvar beta).
Proof.
  reflexivity.
Qed.

Example subst_Tau_ptype_beta: 
  subst_Tau (ptype (ftvar beta)) tau alpha = (ptype (ftvar beta)).
Proof.
  reflexivity.
Qed.

Example subst_Tau_ptype_alpha: 
  subst_Tau (ptype (ftvar alpha)) tau alpha = (ptype tau).
Proof.
  reflexivity.
Qed.

Example subst_Tau_utype: 
  (subst_Tau (utype k cint) tau alpha) = (utype k cint).
Proof.
  reflexivity.
Qed.

Example subst_Tau_utype_alpha: 
  (subst_Tau (utype k (ftvar alpha)) tau alpha) = (utype k tau).
Proof.
  reflexivity.
Qed.

Example subst_Tau_utype_beta: 
  (subst_Tau (utype k (ftvar beta)) tau alpha) = 
  (utype k (ftvar beta)).
Proof.
  reflexivity.
Qed.

Example subst_Tau_etype: 
  (subst_Tau (etype aliases k t0) tau alpha) = 
  (etype aliases k t0).
Proof.
  reflexivity.
Qed.

Example subst_Tau_etype_alpha: 
  (subst_Tau (etype aliases k (ftvar alpha)) tau alpha) = 
  (etype aliases k tau).
Proof.
  reflexivity.
Qed.

Example subst_Tau_etype_beta:
  (subst_Tau (etype aliases k (ftvar beta)) tau alpha) = 
  (etype aliases k (ftvar beta)).
Proof.
  reflexivity.
Qed.

(* Test substitution in expressions. *)
Example subst_E_i_e_i : (subst_E (i_e i) tau alpha) = (i_e i).
Proof.
 reflexivity.
Qed.

Example subst_E_p_e : (subst_E (p_e (fevar x) pdot) tau alpha) = p_e (fevar x) pdot.
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
  (subst_E (f_e (dfun tau tau (retn (p_e (fevar x) pdot)))) tau alpha) =
  (f_e (dfun tau tau (retn (p_e (fevar x) pdot)))).
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

Example subst_E_dot : (subst_E (dot e' zero_pe) tau alpha) = dot e' zero_pe.
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
  (subst_St (letx e s) tau alpha) = (letx e s).
Proof.
 reflexivity.
Qed.

Example subst_St_letx_alpha:
  (subst_St (letx (f_e faa) applfaa) tau alpha) = 
            (letx (f_e f) applff).
Proof.
 reflexivity.
Qed.

Example subst_St_letx_beta:
  (subst_St (letx (f_e fbb) applfbb) tau alpha) = 
            (letx (f_e fbb) applfbb).
Proof.
 reflexivity.
Qed.

Example subst_St_open_none: 
  (subst_St (open e s) tau alpha) = 
            (open e s).
Proof.
 reflexivity.
Qed.

Example subst_St_open_alpha: 
  (subst_St (open (f_e faa) applfaa) tau alpha) = 
            (open (f_e f  ) applff).
Proof.
 reflexivity.
Qed.

Example subst_St_open_beta:
  (subst_St (open (f_e fbb)  applfbb) tau alpha) = 
            (open (f_e fbb)  applfbb).
Proof.
 reflexivity.
Qed.

Example subst_St_openstar_none: 
  (subst_St (openstar e  s) tau alpha) = 
            (openstar e  s).
Proof.
 reflexivity.
Qed.

Example subst_St_openstar_alpha: 
  (subst_St (openstar (f_e faa)  applfaa) tau alpha) = 
            (openstar (f_e f  )  applff).
Proof.
 reflexivity.
Qed.

Example subst_St_openstar_beta:
  (subst_St (openstar (f_e fbb)  applfbb) tau alpha) = 
            (openstar (f_e fbb)  applfbb).
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
  (subst_F (ufun k f) tau alpha) =
           (ufun k f).
Proof.
 reflexivity.
Qed.

Example subst_F_ufun_alpha:
  (subst_F (ufun k faa) tau alpha) =
           (ufun k f).
Proof.
 reflexivity.
Qed.

Example subst_F_ufun_beta:
  (subst_F (ufun k fbb) tau alpha) =
           (ufun k fbb).
Proof.
 reflexivity.
Qed.

(* Bug 7 found here, did not get alpha binding in subst_F right. *)
Example subst_F_ufun_alpha_bound:
  (subst_F (ufun k (dfun tau (ftvar alpha) 
                         (retn (inst (p_e fx pdot) (ftvar alpha)))))
                 tau 
                 alpha) =
           (ufun k 
                 (dfun tau tau
                       (retn (inst (p_e fx pdot) tau)))).
Proof.
  reflexivity.
Qed.

Example fv_cint :
  fv_tau cint = \{}_t.
Proof.
  reflexivity.
Qed.

Example fv_intcrossint :
  fv_tau (cross cint cint) = \{}_t.
Proof.
  reflexivity.
Qed.

Example fv_intcrossint_1 :
  fv_tau (cross (ftvar beta) cint) = \{ beta }_t.
Proof.
  tauto.
Qed.

Example NotFreeInTau_intcrossint_2 :
  fv_tau (cross cint (ftvar beta)) = \{ beta }_t.
Proof.
  tauto.
Qed.

Example fv_intarrow :
  fv_tau (arrow cint cint) = \{}_t.
Proof.
  tauto.
Qed.

Example fv_intarrow_1:
  fv_tau (arrow (ftvar beta) cint) =  \{beta}_t.
Proof.
  tauto.
Qed.

Example fv_intarrow_2:
  fv_tau (arrow cint (ftvar beta)) = \{beta}_t.
Proof.
  tauto.
Qed.

Example NotFreeInTau_ptype: 
  fv_tau (ptype cint) = \{}_t.
Proof.
  reflexivity.
Qed.

Example fv_ptype_false:
 fv_tau (ptype (ftvar beta)) = \{ beta }_t.
Proof.
  tauto.
Qed.

Example fv_utype_bound:
  fv_tau (utype A cint) = \{}_t.
Proof.
  reflexivity.
Qed.

Example fv_utype_bound_2:
  fv_tau (utype A (btvar 0)) = \{}_t.
Proof.
  reflexivity.
Qed.

Example fv_utype_bound_3:
  fv_tau (utype A (ftvar beta)) = \{ beta }_t.
Proof.
  tauto.
Qed.

Example fv_etype_bound:
  fv_tau (etype aliases A cint) = \{}_t.
Proof.
  reflexivity.
Qed.

Example fv_etype_bound_2:
  fv_tau (etype aliases A (btvar 0)) = \{}_t.
Proof.
  reflexivity.
Qed.

Example NotFreeInTau_etype_bound_3:
 fv_tau (etype aliases A (ftvar beta)) = \{ beta }_t.
Proof.
  tauto.
Qed.




