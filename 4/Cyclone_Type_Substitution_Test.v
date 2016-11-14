(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION".   Daniel Grossman, August 2003 *)
(* Definitions from Section 3.5.2 *)
(* Brian Milnes 2016 *)

Set Implicit Arguments.
Require Export Cyclone_Type_Substitution.

Module CycloneTypeSubstitutionTest.

(* Questions:
  1) Do I need the FV stuff yet?
  2) I'll have to remake test utilities and perhaps bring some more 
      definitions over.
*)

Definition tau  := cint.
Definition tau' := cross cint cint.
Definition t    := cint.
Definition t'   := cross cint cint.
Definition t0   := cint.
Definition t1   := cross cint cint.

Definition alpha := var_gen \{}.
Definition beta  := var_gen \{ alpha }.
Definition gamma := var_gen (\{ alpha} \u \{ beta }).

Lemma alpha_not_beta:
  alpha = beta -> False.
Admitted.

Lemma alpha_not_gamma:
  alpha <> gamma.
Admitted.

Lemma beta_not_gamma:
  beta <> gamma.
Admitted.

Definition k  := A.
Definition ka := A.
Definition kb := B.

Definition i     := (i_i 0).
Definition i1    := (i_i 1).
Definition i2    := (i_i 2).
Definition i3    := (i_i 3).

(* Learn how to do this with freshies. *)
Definition x     := var_gen \{}.
Definition x'    := var_gen \{x}.
Definition y     := var_gen (\{x} \u \{x'}).
Definition y'    := var_gen (\{x} \u \{x'} \u \{y}).
Definition z     := var_gen (\{x} \u \{x'} \u \{y} \u \{y'}).
Definition z'    := var_gen (\{x} \u \{x'} \u \{y} \u \{y'} \u \{z}).

Definition fx   := (fevar x).
Definition b0   := (bevar 0).

Definition f   :=
  (dfun cint   cint (retn (inst (p_e fx nil) tau))).
Definition faa := 
  (dfun tau   (ftvar alpha) (retn (inst (p_e fx nil) (ftvar alpha)))).
Definition fbb  := 
  (dfun tau  (ftvar beta) (retn (inst (p_e fx nil) (ftvar beta)))).

Definition applff  := (e_s (appl (f_e f)   (f_e f))).
Definition applfaa := (e_s (appl (f_e faa) (f_e faa))).
Definition applfbb := (e_s (appl (f_e fbb) (f_e fbb))).

Definition ufg  := (ufun A faa).
Definition ufaa := (ufun A faa).
Definition ufbb := (ufun A faa).

Definition e    := (i_e (i_i 0)).
Definition e'   := (i_e (i_i 1)).
Definition e0   := (i_e (i_i 0)).
Definition e1   := (i_e (i_i 1)).
Definition e2   := (i_e (i_i 1)).

Definition s  := (retn (i_e (i_i 0))).
Definition s' := (retn (i_e (i_i 0))).
Definition s1 := (retn (i_e (i_i 1))).
Definition s2 := (retn (i_e (i_i 2))).

(* Wow this is freaky due to the abstract nature of variables.
  I have to know that alpha <> beta <> gamma.
*)

Ltac case_subst :=
  match goal with
     | [  |- subst_Tau _ _ _ = _ ] =>
       simpl
     | [  |- subst_E _ _ _ = _ ] =>
       simpl
     | [  |- subst_St _ _ _ = _ ] =>
       simpl         
     | [  |- subst_F _ _ _ = _ ] =>
       simpl         
     | [  |- (If ?x = ?y then _ else _) = _ ] =>
      destruct~ (classicT (x = y))
     | [ H: ?n <> ?n |- _ ] =>
       false
     | [ H: alpha = beta |- _ ] =>
       apply alpha_not_beta in H;
         contradiction
     | [ |- _ _ = _ _ ] =>
       fequals
     | [ |- _ = ?x] =>
       try unfold x
  end.

Example subst_Tau_alpha: (subst_Tau (ftvar alpha) tau alpha) = tau.
Proof.
  repeat case_subst.
Qed.

Example subst_Tau_beta: (subst_Tau (ftvar beta) tau alpha) = (ftvar beta).
Proof.
  repeat case_subst.
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
  repeat case_subst.
Qed.

Example subst_Tau_cross_l : 
  (subst_Tau (cross (ftvar alpha) t1) tau alpha) = cross tau t1.
Proof.
  repeat case_subst.
Qed.

Example subst_Tau_cross_r : 
  (subst_Tau (cross t0 (ftvar alpha)) tau alpha) = cross t0 tau.
Proof.
  repeat case_subst.
Qed.

Example subst_Tau_arrow_l: 
  (subst_Tau (arrow (ftvar alpha) t1) tau alpha) = arrow tau t1.
Proof.
  repeat case_subst.
Qed.

Example subst_Tau_arrow_l_beta: 
  (subst_Tau (arrow (ftvar beta) t1) tau alpha) = arrow (ftvar beta) t1.
Proof.
  repeat case_subst.
Qed.

Example subst_Tau_arrow_r: 
  (subst_Tau (arrow t0 (ftvar alpha)) tau alpha) = arrow t0 tau.
Proof.
  repeat case_subst.
Qed.

Example subst_Tau_arrow_r_beta: 
  (subst_Tau (arrow t0 (ftvar beta)) tau alpha) = arrow t0 (ftvar beta).
Proof.
  repeat case_subst.
Qed.

Example subst_Tau_ptype_beta: 
  subst_Tau (ptype (ftvar beta)) tau alpha = (ptype (ftvar beta)).
Proof.
  repeat case_subst.
Qed.

Example subst_Tau_ptype_alpha: 
  subst_Tau (ptype (ftvar alpha)) tau alpha = (ptype tau).
Proof.
  repeat case_subst.
Qed.

Example subst_Tau_utype: 
  (subst_Tau (utype k cint) tau alpha) = (utype k cint).
Proof.
  repeat case_subst.
Qed.

Example subst_Tau_utype_alpha: 
  (subst_Tau (utype k (ftvar alpha)) tau alpha) = (utype k tau).
Proof.
  repeat case_subst.
Qed.

Example subst_Tau_utype_beta: 
  (subst_Tau (utype k (ftvar beta)) tau alpha) = 
  (utype k (ftvar beta)).
Proof.
  repeat case_subst.
Qed.

Example subst_Tau_etype: 
  (subst_Tau (etype aliases k t0) tau alpha) = 
  (etype aliases k t0).
Proof.
  repeat case_subst.
Qed.

Example subst_Tau_etype_alpha: 
  (subst_Tau (etype aliases k (ftvar alpha)) tau alpha) = 
  (etype aliases k tau).
Proof.
  repeat case_subst.
Qed.

Example subst_Tau_etype_beta:
  (subst_Tau (etype aliases k (ftvar beta)) tau alpha) = 
  (etype aliases k (ftvar beta)).
Proof.
  repeat case_subst.
Qed.

(* Test substitution in expressions. *)
Example subst_E_i_e_i : (subst_E (i_e i) tau alpha) = (i_e i).
Proof.
 repeat case_subst.
Qed.

Example subst_E_p_e : (subst_E (p_e (fevar x) nil) tau alpha) = p_e (fevar x) nil.
Proof.
 repeat case_subst.
Qed.

(* TODO Need to be actually recursing into the F here.
   So I need an f with an alpha in it. *)
Example subst_E_f_e  : 
  (subst_E (f_e f) tau alpha) = f_e f.
Proof.
  repeat case_subst.
Qed.

Example subst_E_f_e_alpha  : 
  (subst_E (f_e faa) tau alpha) = f_e f.
Proof.
  compute.
  repeat case_subst.
Qed.

Example subst_E_f_e_beta  : 
  (subst_E (f_e fbb) tau alpha) = f_e fbb.
Proof.
  repeat case_subst.
Qed.

(* Bug 5, not recursing through function wrapper. *)
Example subst_E_dfun : 
  (subst_E (f_e (dfun tau tau (retn (p_e (fevar x) nil)))) tau alpha) =
  (f_e (dfun tau tau (retn (p_e (fevar x) nil)))).
Proof.
 repeat case_subst.
Qed.

Example subst_E_amp_no_alpha : (subst_E (amp e') tau alpha) = amp e'.
Proof.
 repeat case_subst.
Qed.

Example subst_E_star : (subst_E (star e') tau alpha) = star e'.
Proof.
 repeat case_subst.
Qed.

Example subst_E_cpair : 
  (subst_E (cpair e1 e2) tau alpha) = cpair e1 e2.
Proof.
 repeat case_subst.
Qed.

Example subst_E_dot : (subst_E (dot e' zero_pe) tau alpha) = dot e' zero_pe.
Proof.
 repeat case_subst.
Qed.

Example subst_E_assign : 
  (subst_E (assign e1 e2) tau alpha) = assign e1 e2.
Proof.
 repeat case_subst.
Qed.

Example subst_E_appl : (subst_E (appl  e1 e2) tau alpha) = appl  e1 e2.
Proof.
 repeat case_subst.
Qed.

Example subst_E_call : (subst_E (call s) tau alpha) = call s.
Proof.
 repeat case_subst.
Qed.

Example subst_E_inst : (subst_E (inst e' t0) tau alpha) = inst e' t0.
Proof.
 repeat case_subst.
Qed.

Example subst_E_pack : 
  (subst_E (pack t e' t1) tau alpha) = pack t e' t1.
Proof.
 repeat case_subst.
Qed.

(* Test substitution in statements. *)

Example subst_St_e_s_none: 
  (subst_St (e_s e) tau alpha) = (e_s e).
Proof.
 repeat case_subst.
Qed.

Example subst_St_e_s_alpha: 
  (subst_St (e_s (f_e faa)) tau alpha) = (e_s (f_e f)).
Proof.
 repeat case_subst.
Qed.

Example subst_St_e_s_beta: 
  (subst_St (e_s (f_e fbb)) tau alpha) = (e_s (f_e fbb)).
Proof.
  repeat case_subst.
Qed.

Example subst_St_retn_none: 
  (subst_St (retn (f_e f)) tau alpha) = retn (f_e f).
Proof.
 repeat case_subst.
Qed.

Example subst_St_retn_alpha: 
  (subst_St (retn (f_e faa)) tau alpha) = 
                       retn (f_e f).
Proof.
 repeat case_subst.
Qed.

Example subst_St_retn_beta: 
  (subst_St (retn (f_e fbb)) tau alpha) = 
                       retn (f_e fbb).
Proof.
 repeat case_subst.
Qed.

Example subst_St_seq_none: 
  (subst_St (seq applff applff) tau alpha) = (seq applff applff).
Proof.
 repeat case_subst.
Qed.

Example subst_St_seq_alpha: 
  (subst_St (seq applfaa applfaa) tau alpha) = (seq applff applff).
Proof.
 repeat case_subst.
Qed.

Example subst_St_seq_beta: 
  (subst_St (seq applfbb applfbb) tau alpha) = (seq applfbb applfbb).
Proof.
 repeat case_subst.
Qed.

Example subst_St_if_s_none: 
  (subst_St (if_s e s1 s2) tau alpha) = (if_s e s1 s2).
Proof.
 repeat case_subst.
Qed.

Example subst_St_if_s_alpha: 
  (subst_St (if_s (f_e faa) applfaa applfaa) tau alpha) = 
            (if_s (f_e f)   applff   applff).
Proof.
 repeat case_subst.
Qed.

Example subst_St_if_s_beta:
  (subst_St (if_s (f_e fbb) applfbb applfbb) tau alpha) = 
            (if_s (f_e fbb)  applfbb applfbb).
Proof.
 repeat case_subst.
Qed.

Example subst_St_while_none: 
  (subst_St (while e s) tau alpha) = (while e s).
Proof.
 repeat case_subst.
Qed.

Example subst_St_while_alpha: 
  (subst_St (while (f_e faa) applfaa) tau alpha) = 
            (while (f_e f) applff).
Proof.
 repeat case_subst.
Qed.

Example subst_St_while_beta:
  (subst_St (while (f_e fbb) applfbb) tau alpha) = 
            (while (f_e fbb) applfbb).
Proof.
 repeat case_subst.
Qed.

Example subst_St_letx_none: 
  (subst_St (letx e s) tau alpha) = (letx e s).
Proof.
 repeat case_subst.
Qed.

Example subst_St_letx_alpha:
  (subst_St (letx (f_e faa) applfaa) tau alpha) = 
            (letx (f_e f) applff).
Proof.
 repeat case_subst.
Qed.

Example subst_St_letx_beta:
  (subst_St (letx (f_e fbb) applfbb) tau alpha) = 
            (letx (f_e fbb) applfbb).
Proof.
 repeat case_subst.
Qed.

Example subst_St_open_none: 
  (subst_St (open e s) tau alpha) = 
            (open e s).
Proof.
 repeat case_subst.
Qed.

Example subst_St_open_alpha: 
  (subst_St (open (f_e faa) applfaa) tau alpha) = 
            (open (f_e f  ) applff).
Proof.
 repeat case_subst.
Qed.

Example subst_St_open_beta:
  (subst_St (open (f_e fbb)  applfbb) tau alpha) = 
            (open (f_e fbb)  applfbb).
Proof.
 repeat case_subst.
Qed.

Example subst_St_openstar_none: 
  (subst_St (openstar e  s) tau alpha) = 
            (openstar e  s).
Proof.
 repeat case_subst.
Qed.

Example subst_St_openstar_alpha: 
  (subst_St (openstar (f_e faa)  applfaa) tau alpha) = 
            (openstar (f_e f  )  applff).
Proof.
 repeat case_subst.
Qed.

Example subst_St_openstar_beta:
  (subst_St (openstar (f_e fbb)  applfbb) tau alpha) = 
            (openstar (f_e fbb)  applfbb).
Proof.
 repeat case_subst.
Qed.

Example subst_F_dfun_none: 
  (subst_F f tau alpha) = f.
Proof.
  repeat case_subst.
Qed.

Example subst_F_dfun_alpha: 
  (subst_F faa tau alpha) = f.
Proof.
  repeat case_subst.
Qed.

Example subst_F_dfun_beta:
  (subst_F fbb tau alpha) = fbb.
Proof.
  repeat case_subst.
Qed.

Example subst_F_ufun_non:
  (subst_F (ufun k f) tau alpha) =
           (ufun k f).
Proof.
 repeat case_subst.
Qed.

Example subst_F_ufun_alpha:
  (subst_F (ufun k faa) tau alpha) =
           (ufun k f).
Proof.
 repeat case_subst.
Qed.

Example subst_F_ufun_beta:
  (subst_F (ufun k fbb) tau alpha) =
           (ufun k fbb).
Proof.
 repeat case_subst.
Qed.

(* Bug 7 found here, did not get alpha binding in subst_F right. *)
Example subst_F_ufun_alpha_bound:
  (subst_F (ufun k (dfun tau (ftvar alpha) 
                         (retn (inst (p_e fx nil) (ftvar alpha)))))
                 tau 
                 alpha) =
           (ufun k 
                 (dfun tau tau
                       (retn (inst (p_e fx nil) tau)))).
Proof.
  repeat case_subst.
Qed.

(*
Example fv_cint :
  fv_tau cint = \{}_t.
Proof.
  repeat case_subst.
Qed.

Example fv_intcrossint :
  fv_tau (cross cint cint) = \{}_t.
Proof.
  repeat case_subst.
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
  repeat case_subst.
Qed.

Example fv_ptype_false:
 fv_tau (ptype (ftvar beta)) = \{ beta }_t.
Proof.
  tauto.
Qed.

Example fv_utype_bound:
  fv_tau (utype A cint) = \{}_t.
Proof.
  repeat case_subst.
Qed.

Example fv_utype_bound_2:
  fv_tau (utype A (btvar 0)) = \{}_t.
Proof.
  repeat case_subst.
Qed.

Example fv_utype_bound_3:
  fv_tau (utype A (ftvar beta)) = \{ beta }_t.
Proof.
  tauto.
Qed.

Example fv_etype_bound:
  fv_tau (etype aliases A cint) = \{}_t.
Proof.
  repeat case_subst.
Qed.

Example fv_etype_bound_2:
  fv_tau (etype aliases A (btvar 0)) = \{}_t.
Proof.
  repeat case_subst.
Qed.

Example NotFreeInTau_etype_bound_3:
 fv_tau (etype aliases A (ftvar beta)) = \{ beta }_t.
Proof.
  tauto.
Qed.
*)

End CycloneTypeSubstitutionTest.