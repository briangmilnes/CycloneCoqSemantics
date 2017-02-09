(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

 This tests the dynamic semantics of statements and expressions, pg. 58, 59.

*)
 
Set Implicit Arguments.
Require Export Cyclone_Dynamic_Semantics Cyclone_LN_Env Cyclone_LN_Types Cyclone_LN_Types_In_Terms Cyclone_LN_Terms Cyclone_LN_Tactics.
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

Function fs (h : Heap) (s : St) (h' : Heap) (s' : St) : Prop :=
  True.

Function fe (h : Heap) (e : E) (h' : Heap) (e' : E) : Prop :=
  True.

Lemma simple_srl_induction:
  forall h s h' s',
    S h s h' s' ->
    fs h s h' s'.
Proof.
  apply(SRL_ind_mutual
          (fun (h : Heap) (s : St) (h' : Heap) (s' : St) (_ : S h s h' s') =>
             fs h s h' s')
          (fun (h : Heap) (e : E) (h' : Heap) (e' : E) (_ : R h e h' e') =>
             fe h e h' e')
          (fun (h : Heap) (e : E) (h' : Heap) (e' : E) (_ : L h e h' e') =>
             fe h e h' e')); intros.
Admitted.

(* Let's make some e->e' transitions that actually evaluate something to test this stuff. *)

Definition s  := (if_s (i_e (i_i 0)) 
                       (e_s (i_e (i_i 0))) 
                       (e_s (i_e (i_i 1)))).
Definition s' := (e_s (i_e (i_i 0))).

Definition e  := (dot (cpair (i_e (i_i 0)) (i_e (i_i 1))) zero_pe).
Definition e' := (i_e (i_i 0)).

Definition hxv := (varx ~ v) & empty.

Ltac unfold_defs :=
  unfold_test_utilities;
  unfold s, s', e, e'.

Example S_Let_3_1_test :
  S empty (letx v s) (empty & (varx ~ v)) s.
Proof.
  unfold_defs.
  apply~ S_let_3_1.
Qed.

Example S_seq_3_2_test :
  S empty (seqx (e_s v) s) empty s.
Proof.
  unfold_defs.
  (* apply S_seq_3_2. *)
  auto.
Qed.

Example S_return_3_3_test :
 S empty (seqx (retn v) s) empty (retn v).
Proof.
  unfold_defs.
  (* apply S_return_3_3. *)
  auto.
Qed.

Example S_if0_3_4_test :
 S empty (if_s (i_e (i_i 0)) s1 s2)
   empty s1.
Proof.
  unfold_defs.
  auto. (* apply S_if0_3_4.*)
Qed.

Example S_if_ne_0_3_5_test :
  S empty (if_s vi1 s1 s2) empty s2.
Proof.
  unfold_defs.
  auto. (* apply S_if_ne_0_3_5.*)
Qed.

Example S_while_3_6_test :
 S empty (while e s) 
   empty (if_s e (seqx s (while e s)) (e_s (i_e (i_i 0)))).
Proof.
  unfold_defs.
  auto. (* apply S_while_3_6.*)
Qed.

Example S_open_3_7_test :
  S empty (openx (pack tau' v (etype aliases k tau)) s)
    empty (letx v s).
Proof.
  unfold_defs.
  auto. (* apply S_open_3_7.*)
Qed.

Definition etau := (etype aliases A tau).
Definition H38 := ((varx ~ (pack etau v etau)) & empty).

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
Definition H39 := empty & (varx ~ (pack tau' v (etype aliases k tau))).
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
  (h:= (empty & varx ~ (pack (cross cint cint) v (etype aliases k cint))))
  (s:= s)
  (tau:= cint)
  (tau':= (cross cint cint))
  (q:= aliases)
  (k:= k);
  auto.
Qed.

Example S_exp_3_9_1_test :
  S empty (e_s e) empty (e_s e').
Proof.
  unfold_defs.
  auto. (* apply S_exp_3_9_1.*)
Qed.

Example S_ret_3_9_2_test :
  S empty (retn e) empty (retn e').
Proof.
  unfold_defs.
  auto. (* apply S_ret_3_9_2.*)
Qed.

Example S_if_3_9_3_test :
  S empty (if_s e s1 s2) empty (if_s e' s1 s2).
Proof.
  unfold_defs.
  auto. (* apply S_if_3_9_3.*)
Qed.

Example S_letx_3_9_4_test :
  S empty (letx e s) empty (letx e' s).
Proof.
  unfold_defs.
  auto. (* apply S_letx_3_9_4.*)
Qed.

(* ? TODO e not a value.*)
Example S_open_3_9_5_test :
  S empty (openx e s) empty (openx e' s).
Proof.
  unfold_defs.
  auto. (* apply S_open_3_9_5.*)
Qed.

Example S_seq_3_10_test :
  S empty (seqx s s2) empty (seqx s' s2).
Proof.
  unfold_defs.
  auto. (* apply S_seq_3_10.*)
Qed.

Example S_openstar_3_11_test :
 S empty (openstar (dot (p_e x nil) zero_pe) s) 
   empty (openstar      (p_e x (cons (i_pe zero_pe) nil)) s).
Proof.
  unfold_defs.
  auto. (* apply S_openstar_3_11.*)
  (* apply L_xpi_3_1.*)
Qed.

(* Test R. *)

Definition h703 := (empty & (varx ~ v)).
Example R_get_3_1_test:
  R h703  (p_e x nil)
    h703   v.
Proof.
  unfold h703.
  unfold_defs.
  auto.
  (* apply R_get_3_1 with (v':=v); *)
Qed.

Example R_assign_3_2_test:
  R  empty                            (assign (p_e (fevar varx) nil) (i_e (i_i 3)))
    (empty & (varx ~ (i_e (i_i 3))))  (i_e (i_i 3)).
Proof.
  unfold_defs.
  auto.
  (* eapply R_assign_3_2 *)
Qed.

Example R_initial_assign_3_2_test:
  R empty  (assign (p_e (fevar varx) nil) (i_e (i_i 3)))
    (empty & (varx ~ (i_e (i_i 3))))  (i_e (i_i 3)).
Proof.
  unfold_defs.
  auto. (* apply R_initial_assign_3_2.*)
Qed.

Example R_star_3_3_test:
  R (empty & (varx ~ v))  (star (amp (p_e x nil)))
    (empty & (varx ~ v))  (p_e x nil).
Proof.
  unfold_defs.
  auto. (* apply R_star_amp_3_3.*)
Qed.

Example R_dot_3_4_0_test:
  R empty  (dot (cpair v0 v1) zero_pe)
    empty  v0.
Proof.
  unfold_defs.
  auto. (* apply R_dot_3_4_0.*)
Qed.

Example R_dot_3_4_1_test:
  R empty  (dot (cpair v0 v1) one_pe)
    empty  v1.
Proof.
  unfold_defs.
  auto. (* apply R_dot_3_4_1.*)
Qed.

Example R_appl_3_5_test:
  R empty  (appl (f_e (dfun tau tau' s)) v)
    empty  (call (letx v s)).
Proof.
  unfold_defs.
  auto. (* apply R_appl_3_5.*)
Qed.

Example R_call_3_6_test:
  R empty  (call (retn v))
    empty  v.
Proof.
  unfold_defs.
  auto. (* apply R_call_3_6.*)
Qed.

(*
Example R_inst_3_7_test:
  R empty (e_s (inst (f_e (ufun alpha k f)) tau))
    empty (e_s (f_e (subst_F f tau alpha))).
Proof.
  unfold_defs.
  apply R_inst_3_7.
Qed.
*)

Example R_call_3_8_test:
  R empty  (call s) empty  (call s').
Proof.
  unfold_defs.
  auto. (* apply R_call_3_8.*)
Qed.

(* Originally I had an invalid left expression here. *)

Example R_amp_3_9_1_test:
  R ((varx ~ v) & empty)  (amp (dot (p_e x nil) zero_pe))
    ((varx ~ v) & empty)  (amp (p_e x (cons (i_pe zero_pe) nil))).
Proof.
  unfold_defs.
  auto. (* apply R_amp_3_9_1.*)
  (* apply L_xpi_3_1. *)
Qed.

Example R_assign_3_9_2_test:
  R empty  (assign (star (amp (p_e x nil))) v0) 
    empty  (assign (p_e x nil) v0).
Proof.
  unfold_defs.
  auto. (* apply R_assign_3_9_2.*)
Qed.

Example R_star_3_10_1_test:
  R empty  (star (star (amp (p_e x nil))))
    empty  (star (p_e x nil)).
Proof.
  unfold_defs.
  auto. (* apply R_star_3_10_1.*)
Qed.

Example R_dot_3_10_2_test:
  R empty  (dot (star (amp (p_e x nil)))  zero_pe)
    empty  (dot (p_e x nil)               zero_pe).
Proof.
  unfold_defs.
  auto. (* apply R_dot_3_10_2.*)
Qed.

Example Bug14_e_e': 
 ~ R empty  (i_e (i_i 0))
     empty  (i_e (i_i 1)).
Proof.
  unfold_defs.
  compute.
  intros H.
  inversion H.
Qed.

Example R_assign_3_10_3_test:
  R h  (assign (p_e x pdot) e)
    h  (assign (p_e x pdot) e').
Proof.
  unfold_defs.
  auto. (* apply R_assign_3_10_3.*)
Qed.

Example R_inst_3_10_4_test:
  R h  (inst e tau)
    h  (inst e' tau).
Proof.
  unfold_defs.
  auto. (* apply R_inst_3_10_4.*)
Qed.

Example R_pack_3_10_5_test:
  R h   (pack tau' e  (etype witnesschanges k tau))
    h   (pack tau' e' (etype witnesschanges k tau)).
Proof.
  unfold_defs.
  apply R_pack_3_10_5.
  auto.
Qed.

Example R_cpair_3_10_6_test:
  R h  (cpair e e2)
    h  (cpair e' e2).
Proof.
  unfold_defs.
  apply R_cpair_3_10_6.
  auto.
Qed.

Example R_cpair_3_10_7_test:
  R h  (cpair v e)
    h  (cpair v e').
Proof.
  unfold_defs.
  apply R_cpair_3_10_7;
  auto.
Qed.

Example R_cpair_3_10_8_test:
  R h  (cpair e e2)
    h  (cpair e' e2).
Proof.
  unfold_defs.
  apply R_cpair_3_10_8.
  auto.
Qed.

Example R_appl_3_10_9_test:
  R h  (appl e e2)
    h  (appl e' e2).
Proof.
  unfold_defs.
  apply R_appl_3_10_9.
  auto.
Qed.

Example R_appl_3_10_10_test:
  R h  (appl v e)
    h  (appl v e').
Proof.
  unfold_defs.
  apply R_appl_3_10_10;
  auto.
Qed.

(* Test L *)

Example L_xpi_3_1_test:
  L h  (dot (p_e x nil) zero_pe)
    h  (p_e x (cons (i_pe zero_pe) nil)).
Proof.
  unfold_defs.
  auto. (* apply L_xpi_3_1.*)
Qed.

Example L_staramp_3_2_test:
  L h  (star (amp (p_e x nil))) h  (p_e x nil).
Proof.
  unfold_defs.
  auto. (* apply L_staramp_3_2.*)
Qed.

Example L_star_3_3_test:
  L h  (star e) h  (star e') .
Proof.
  unfold_defs.
  auto.
  (* eapply L_star_3_3. *)
Qed.

Example L_ei_3_4_test:
  L empty  (dot (dot (p_e x nil) zero_pe) zero_pe)
    empty  (dot (p_e x (cons (i_pe zero_pe) nil)) zero_pe).
Proof.
 unfold_defs.
 auto. (* apply L_ei_3_4.*)
Qed.

