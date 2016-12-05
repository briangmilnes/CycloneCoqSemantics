(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

 This tests the dynamic semantics of statements and expressions, pg. 58, 59.

*)
 
Set Implicit Arguments.
Require Export Cyclone_Dynamic_Semantics Cyclone_LN_Env Cyclone_LN_Types Cyclone_LN_Types_In_Terms Cyclone_LN_Terms.
Require Export Cyclone_Test_Utilities.
Close Scope list_scope.
Import LibEnvNotations.
Import LVPE.LibVarPathEnvNotations.

(* Test the S judgement. *)

(* Test induction on S. *)

(* A bad induction as it is not set up mutualy but it gives us a 
 feel by looking at the goals that the induction is set up OK. *)

Lemma bad_s_induction:
  forall h s h' s',
    S h s h' s' ->
    True.
Proof.
  introv shshs.
  induction shshs. 
Admitted.

Function f (h : Heap) (s : St) (h' : Heap) (s' : St) : Prop :=
  True.

Lemma simple_srl_induction:
  forall h s h' s',
    S h s h' s' ->
    f h s h' s'.
Proof.
  apply(SRL_ind_mutual
          (fun (h : Heap) (s : St) (h' : Heap) (s' : St) (_ : S h s h' s') =>
             f h s h' s')
          (fun (h : Heap) (s : St) (h' : Heap) (s' : St) (_ : R h s h' s') =>
             f h s h' s')
          (fun (h : Heap) (s : St) (h' : Heap) (s' : St) (_ : L h s h' s') =>
             f h s h' s')); intros.

Admitted.

(* Let's make some e->e' transitions that actually evaluate something to test this stuff. *)

Definition s  := (if_s (i_e (i_i 0)) 
                       (e_s (i_e (i_i 0))) 
                       (e_s (i_e (i_i 1)))).
Definition s' := (e_s (i_e (i_i 0))).

Definition e  := (dot (cpair (i_e (i_i 0)) (i_e (i_i 1))) zero_pe).
Definition e' := (i_e (i_i 0)).

Definition hxv := (varx ~ v) & hdot.

Ltac unfold_defs :=
  unfold_test_utilities;
  unfold s, s', e, e'.

Example S_Let_3_1_test :
  S hdot (letx v s) ((varx ~ v) & hdot) s.
Proof.
  unfold_defs.
  apply~ S_let_3_1.
Qed.

Example S_seq_3_2_test :
  S hdot (seqx (e_s v) s) hdot s.
Proof.
  unfold_defs.
  (* apply S_seq_3_2. *)
  auto.
Qed.

Example S_return_3_3_test :
 S hdot (seqx (retn v) s) hdot (retn v).
Proof.
  unfold_defs.
  (* apply S_return_3_3. *)
  auto.
Qed.

Example S_if0_3_4_test :
 S hdot (if_s (i_e (i_i 0)) s1 s2)
   hdot s1.
Proof.
  unfold_defs.
  auto. (* apply S_if0_3_4.*)
Qed.

Example S_if_ne_0_3_5_test :
  S hdot (if_s vi1 s1 s2) hdot s2.
Proof.
  unfold_defs.
  auto. (* apply S_if_ne_0_3_5.*)
Qed.

Example S_while_3_6_test :
 S hdot (while e s) 
   hdot (if_s e (seqx s (while e s)) (e_s (i_e (i_i 0)))).
Proof.
  unfold_defs.
  auto. (* apply S_while_3_6.*)
Qed.

Example S_open_3_7_test :
  S hdot (openx (pack tau' v (etype aliases k tau)) s)
    hdot (letx v s).
Proof.
  unfold_defs.
  auto. (* apply S_open_3_7.*)
Qed.

Definition etau := (etype aliases A tau).
Definition H38 := ((varx ~ (pack etau v etau)) & hdot).

Example pack_value:
  get varx H38 = Some v' ->
  Value v'.
Proof.
  unfold etau, H38.
  unfold_defs.
  auto.
Qed.

Example open_st_test:
  (TTM.open_rec_st 0 tau s) = s.
Proof.
  unfold_defs.
  auto.
Qed.

(* TODO Ltac. *)
Definition H39 := (varx ~ (pack tau' v (etype aliases k tau))) & hdot.
Example S_openstar_3_8_test :
  S H39 (openstar (p_e x nil) s)
    H39 (letx (amp (p_e x (app nil (cons u_pe nil)))) s).
Proof.
  unfold H39.
  unfold_defs.
  apply S_openstar_3_8
  with 
  (v:= v)
  (v':= (pack (cross cint cint) v (etype aliases k cint)))
  (h:= (varx ~ (pack (cross cint cint) v (etype aliases k cint))) & hdot)
  (s:= s)
  (tau:= cint)
  (tau':= (cross cint cint))
  (q:= aliases)
  (k:= k);
  auto.
Qed.

Example S_exp_3_9_1_test :
  S hdot (e_s e) hdot (e_s e').
Proof.
  unfold_defs.
  auto. (* apply S_exp_3_9_1.*)
Qed.

Example S_ret_3_9_2_test :
  S hdot (retn e) hdot (retn e').
Proof.
  unfold_defs.
  auto. (* apply S_ret_3_9_2.*)
Qed.

Example S_if_3_9_3_test :
  S hdot (if_s e s1 s2) hdot (if_s e' s1 s2).
Proof.
  unfold_defs.
  auto. (* apply S_if_3_9_3.*)
Qed.

Example S_letx_3_9_4_test :
  S hdot (letx e s) hdot (letx e' s).
Proof.
  unfold_defs.
  auto. (* apply S_letx_3_9_4.*)
Qed.

(* ? TODO e not a value.*)
Example S_open_3_9_5_test :
  S hdot (openx e s) hdot (openx e' s).
Proof.
  unfold_defs.
  auto. (* apply S_open_3_9_5.*)
Qed.

Example S_seq_3_10_test :
  S hdot (seqx s s2) hdot (seqx s' s2).
Proof.
  unfold_defs.
  auto. (* apply S_seq_3_10.*)
Qed.

Example S_openstar_3_11_test :
 S hdot (openstar (dot (p_e x nil) zero_pe) s) 
   hdot (openstar      (p_e x (cons (i_pe zero_pe) nil)) s).
Proof.
  unfold_defs.
  auto. (* apply S_openstar_3_11.*)
  (* apply L_xpi_3_1.*)
Qed.

(* Test R. *)

Definition h703 := ((varx ~ v) & hdot).
Example R_get_3_1_test:
  R h703  (e_s (p_e x nil)) 
    h703  (e_s v).
Proof.
  unfold h703.
  unfold_defs.
  auto.
  (* apply R_get_3_1 with (v':=v); *)
Qed.

Example R_assign_3_2_test:
  R  hdot                           (e_s (assign (p_e (fevar varx) nil) (i_e (i_i 3))))
    ((varx ~ (i_e (i_i 3))) & hdot) (e_s (i_e (i_i 3))).
Proof.
  unfold_defs.
  auto.
  (* eapply R_assign_3_2 *)
Qed.

Example R_initial_assign_3_2_test:
  R hdot (e_s (assign (p_e (fevar varx) nil) (i_e (i_i 3))))
    ((varx ~ (i_e (i_i 3))) & hdot) (e_s (i_e (i_i 3))).
Proof.
  unfold_defs.
  auto. (* apply R_initial_assign_3_2.*)
Qed.

Example R_star_3_3_test:
  R ((varx ~ v) & hdot) (e_s (star (amp (p_e x nil))))
    ((varx ~ v) & hdot) (e_s (p_e x nil)).
Proof.
  unfold_defs.
  auto. (* apply R_star_amp_3_3.*)
Qed.

Example R_dot_3_4_0_test:
  R hdot (e_s (dot (cpair v0 v1) zero_pe))
    hdot (e_s v0).
Proof.
  unfold_defs.
  auto. (* apply R_dot_3_4_0.*)
Qed.

Example R_dot_3_4_1_test:
  R hdot (e_s (dot (cpair v0 v1) one_pe))
    hdot (e_s v1).
Proof.
  unfold_defs.
  auto. (* apply R_dot_3_4_1.*)
Qed.

Example R_appl_3_5_test:
  R hdot (e_s (appl (f_e (dfun tau tau' s)) v))
    hdot (e_s (call (letx v s))).
Proof.
  unfold_defs.
  auto. (* apply R_appl_3_5.*)
Qed.

Example R_call_3_6_test:
  R hdot (e_s (call (retn v)))
    hdot (e_s v).
Proof.
  unfold_defs.
  auto. (* apply R_call_3_6.*)
Qed.

(*
Example R_inst_3_7_test:
  R hdot (e_s (inst (f_e (ufun alpha k f)) tau))
    hdot (e_s (f_e (subst_F f tau alpha))).
Proof.
  unfold_defs.
  apply R_inst_3_7.
Qed.
*)

Example R_call_3_8_test:
  R hdot (e_s (call s)) hdot (e_s (call s')).
Proof.
  unfold_defs.
  auto. (* apply R_call_3_8.*)
Qed.

(* Originally I had an invalid left expression here. *)

Example R_amp_3_9_1_test:
  R ((varx ~ v) & hdot) (e_s (amp (dot (p_e x nil) zero_pe)))
    ((varx ~ v) & hdot) (e_s (amp (p_e x (cons (i_pe zero_pe) nil)))).
Proof.
  unfold_defs.
  auto. (* apply R_amp_3_9_1.*)
  (* apply L_xpi_3_1. *)
Qed.

Example R_assign_3_9_2_test:
  R hdot (e_s (assign (star (amp (p_e x nil))) v0)) 
    hdot (e_s (assign (p_e x nil) v0)).
Proof.
  unfold_defs.
  auto. (* apply R_assign_3_9_2.*)
Qed.

Example R_star_3_10_1_test:
  R hdot (e_s (star (star (amp (p_e x nil)))))
    hdot (e_s (star (p_e x nil))).
Proof.
  unfold_defs.
  auto. (* apply R_star_3_10_1.*)
Qed.

Example R_dot_3_10_2_test:
  R hdot (e_s (dot (star (amp (p_e x nil)))  zero_pe))
    hdot (e_s (dot (p_e x nil)               zero_pe)).
Proof.
  unfold_defs.
  auto. (* apply R_dot_3_10_2.*)
Qed.

Example Bug14_e_e': 
 ~ R hdot (e_s (i_e (i_i 0)))
     hdot (e_s (i_e (i_i 1))).
Proof.
  unfold_defs.
  compute.
  intros H.
  inversion H.
Qed.

Example R_assign_3_10_3_test:
  R h (e_s (assign (p_e x pdot) e))
    h (e_s (assign (p_e x pdot) e')).
Proof.
  unfold_defs.
  auto. (* apply R_assign_3_10_3.*)
Qed.

Example R_inst_3_10_4_test:
  R h (e_s (inst e tau))
    h (e_s (inst e' tau)).
Proof.
  unfold_defs.
  auto. (* apply R_inst_3_10_4.*)
Qed.

Example R_pack_3_10_5_test:
  R h  (e_s (pack tau' e  (etype witnesschanges k tau)))
    h  (e_s (pack tau' e' (etype witnesschanges k tau))).
Proof.
  unfold_defs.
  apply R_pack_3_10_5.
  auto.
Qed.

Example R_cpair_3_10_6_test:
  R h (e_s (cpair e e2))
    h (e_s (cpair e' e2)).
Proof.
  unfold_defs.
  apply R_cpair_3_10_6.
  auto.
Qed.

Example R_cpair_3_10_7_test:
  R h (e_s (cpair v e))
    h (e_s (cpair v e')).
Proof.
  unfold_defs.
  apply R_cpair_3_10_7;
  auto.
Qed.

Example R_cpair_3_10_8_test:
  R h (e_s (cpair e e2))
    h (e_s (cpair e' e2)).
Proof.
  unfold_defs.
  apply R_cpair_3_10_8.
  auto.
Qed.

Example R_appl_3_10_9_test:
  R h (e_s (appl e e2))
    h (e_s (appl e' e2)).
Proof.
  unfold_defs.
  apply R_appl_3_10_9.
  auto.
Qed.

Example R_appl_3_10_10_test:
  R h (e_s (appl v e))
    h (e_s (appl v e')).
Proof.
  unfold_defs.
  apply R_appl_3_10_10;
  auto.
Qed.

(* Test L *)

Example L_xpi_3_1_test:
  L h (e_s (dot (p_e x nil) zero_pe))
    h (e_s (p_e x (cons (i_pe zero_pe) nil))).
Proof.
  unfold_defs.
  auto. (* apply L_xpi_3_1.*)
Qed.

Example L_staramp_3_2_test:
  L h (e_s (star (amp (p_e x nil)))) h (e_s (p_e x nil)).
Proof.
  unfold_defs.
  auto. (* apply L_staramp_3_2.*)
Qed.

Example L_star_3_3_test:
  L h (e_s (star e)) h (e_s (star e')) .
Proof.
  unfold_defs.
  auto.
  (* eapply L_star_3_3. *)
Qed.

Example L_ei_3_4_test:
  L hdot (e_s (dot (dot (p_e x nil) zero_pe) zero_pe))
    hdot (e_s (dot (p_e x (cons (i_pe zero_pe) nil)) zero_pe)).
Proof.
 unfold_defs.
 auto. (* apply L_ei_3_4.*)
Qed.

