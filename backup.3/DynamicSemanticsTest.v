(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

 This tests the dynamic semantics of statements and expressions, pg. 58, 59.

*)
 
Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.

Require Export FormalSyntax.
Require Export DynamicSemanticsTypeSubstitution.
Require Export DynamicSemanticsHeapObjects.
Require Export DynamicSemantics.
Require Export Tacticals.

Require Export TestUtilities.

(* Test the S judgement. *)

(* ?TODO Let's make these tests more meaninful. *)

(* Let's make some e->e' transitions that actually evaluate something to test this stuff. *)

Definition s  := (if_s (i_e (i_i 0)) 
                       (e_s (i_e (i_i 0))) 
                       (e_s (i_e (i_i 1)))).
Definition s' := (e_s (i_e (i_i 0))).

Definition e  := (dot (cpair (i_e (i_i 0)) (i_e (i_i 1))) (i_i 0)).
Definition e' := (i_e (i_i 0)).

Definition hxv := [(x,v)].

Example S_Let_3_1_test :
  S [] (letx x v s) [(x,v)] s.
Proof.
  apply S_let_3_1;
  eauto 10 with Chapter3.
Qed.

Example S_seq_3_2_test :
  S [] (seq (e_s v) s) [] s.
Proof.
  apply S_seq_3_2.
  eauto 10 with Chapter3.
Qed.

Example S_return_3_3_test :
 S [] (seq (retn v) s) [] (retn v).
Proof.
  apply S_return_3_3.
  eauto 10 with Chapter3.
Qed.

Example S_if0_3_4_test :
 S [] (if_s (i_e (i_i 0)) s1 s2)
   [] s1.
Proof.
  apply S_if0_3_4.
Qed.

Example S_if_ne_0_3_5_test :
  S [] (if_s vi1 s1 s2) [] s2.
Proof.
  apply S_if_ne_0_3_5.
  eauto 10 with Chapter3.
Qed.

Example S_while_3_6_test :
 S [] (while e s) 
   [] (if_s e (seq s (while e s)) (e_s (i_e (i_i 0)))).
Proof.
  apply S_while_3_6.
Qed.

(* Bug 8, just naming in two constructors. *)

(* TODO Questionable test? *)
Example S_open_3_7_test :
  S [] (open (pack tau' v (etype aliases alpha k tau)) alpha x s)
    [] (letx x' v (subst_St s tau alpha)).
Proof.
  apply S_open_3_7.
  eauto 10 with Chapter3.
Qed.

(* TODO Questionable test? *)
Definition etau := (etype aliases alpha A tau).
Definition H38 := [(x,(pack etau v etau))].
Example pack_value:
  (getH H38 x) = Some v' ->
  Value v'.
Proof.
  intros H.
  compute in H.
  compute.
  eauto 10 with Chapter3.
Qed.

(* Okay so H evaluates right and is a value. *)
(* Bug 20, State unbound. *)
(* Bug 21, Pack not in Values! *)
(* Is this a bug with get or is this just not syntax directed without
  some Tacticals. At least need Tactical for adding nil. *)
(* Bug 22, why is this not syntax directed ? Automation bug really. *)
Example S_openstar_3_8_test :
  S H38 (openstar (p_e x []) alpha x' s)
    H38 (letx x'  (amp (p_e x ([] ++ [u_pe])))
                          (subst_St s tau alpha)).
Proof.
  apply S_openstar_3_8 with 
  (tau':= etau) (v:= v) (q:= aliases) (k:=A)
  (v':= (pack etau v etau));
  eauto 10 with Chapter3.
Qed.

Example S_exp_3_9_1_test :
  S [] (e_s e) [] (e_s e').
Proof.
  apply S_exp_3_9_1.
  eauto 10 with Chapter3.
Qed.

Example S_ret_3_9_2_test :
  S [] (retn e) [] (retn e').
Proof.
  apply S_ret_3_9_2.
  eauto 10 with Chapter3.
Qed.

Example S_if_3_9_3_test :
  S [] (if_s e s1 s2) [] (if_s e' s1 s2).
Proof.
  apply S_if_3_9_3.
  eauto 10 with Chapter3.
Qed.

Example S_letx_3_9_4_test :
  S [] (letx x e s) [] (letx x e' s).
Proof.
  apply S_letx_3_9_4.
  eauto 10 with Chapter3.
Qed.

(* ? TODO e not a value.*)
Example S_open_3_9_5_test :
  S [] (open e alpha x s) [] (open e' alpha x s).
Proof.
  apply S_open_3_9_5.
  eauto 10 with Chapter3.
Qed.

(* Bug 9 - extra tvar. *)
(* Bug 10. If returning the wrong clause. *)
Example S_seq_3_10_test :
  S [] (seq s s2) [] (seq s' s2).
Proof.
  apply S_seq_3_10.
  eauto 10 with Chapter3.
Qed.

Example S_openstar_3_11_test :
 S [] (openstar (dot (p_e x []) (i_i 0))    alpha x s) 
   [] (openstar      (p_e x [i_pe (i_i 0)]) alpha x s).
Proof.
  apply S_openstar_3_11.
  eauto 10 with Chapter3.
  apply L_xpi_3_1.
Qed.

(* Test R. *)

Example R_get_3_1_test:
  R [(x,v)]  (e_s (p_e x nil)) 
    [(x,v)]  (e_s v).
Proof.
  (* I don't care because eauto can find this v'. *)
  apply R_get_3_1 with (v':=v); 
  eauto 10 with Chapter3.
Qed.

(* Dan Bug,  Set rule 1 should be set(v',[],v,v'') ? *)
Definition h32xv   := ([] ++ [(x,v')]  ++ []).
Definition h32xv'' := ([] ++ [(x,v'')] ++ []).
(* Definition h32xv'' := [(x,v'')]. *)
Example R_read_heap_3_2_test:
  R h32xv   (e_s (assign (p_e x []) (i_e (i_i 3))))
    h32xv'' (e_s (i_e (i_i 3))).
Proof.
  apply R_assign_3_2;
  eauto 10 with Chapter3.
Qed.

Example R_star_3_3_test:
  R hxv (e_s (star (amp (p_e x nil))))
    hxv (e_s (p_e x nil)).
Proof.
  apply R_star_3_3.
Qed.

Example R_dot_3_4_0_test:
  R [] (e_s (dot (cpair v0 v1) (i_i 0)))
    [] (e_s v0).
Proof.
  apply R_dot_3_4_0.
Qed.

Example R_dot_3_4_1_test:
  R [] (e_s (dot (cpair v0 v1) (i_i 1)))
    [] (e_s v1).
Proof.
  apply R_dot_3_4_1.
Qed.

Example R_appl_3_5_test:
  R [] (e_s (appl (f_e (dfun tau x tau' s)) v))
    [] (e_s (call (letx x v s))).
Proof.
  apply R_appl_3_5.
  eauto 10 with Chapter3.
Qed.

Example R_call_3_6_test:
  R [] (e_s (call (retn v)))
    [] (e_s v).
Proof.
  apply R_call_3_6.
  eauto 10 with Chapter3.
Qed.

Example R_inst_3_7_test:
  R [] (e_s (inst (f_e (ufun alpha k f)) tau))
    [] (e_s (f_e (subst_F f tau alpha))).
Proof.
  apply R_inst_3_7.
Qed.

(* Bug 12, R instead of S in the precondition. *)

Example R_call_3_8_test:
  R [] (e_s (call s)) [] (e_s (call s')).
Proof.
  apply R_call_3_8.
  eauto 10 with Chapter3.
Qed.

(* Originally I had an invalid left expression here. *)

Example R_amp_3_9_1_test:
  R hxv (e_s (amp (dot (p_e x nil) (i_i 0))))
    hxv (e_s (amp (p_e x [i_pe (i_i 0)]))).
Proof.
  apply R_amp_3_9_1.
  apply L_xpi_3_1.
Qed.

Example R_assign_3_9_2_test:
  R [] (e_s (assign (star (amp (p_e x nil))) v0)) 
    [] (e_s (assign (p_e x nil) v0)).
Proof.
  apply R_assign_3_9_2.
  eauto 10 with Chapter3.
Qed.

(* These would be nice for test but I can't make a statement into an expression. Even an If. *)

(* TODO It would be better if I went from h to h' here. *)
Example R_star_3_10_1_test:
  R [] (e_s (star (star (amp (p_e x [])))))
    [] (e_s (star (p_e x []))).
Proof.
  apply R_star_3_10_1.
  eauto 10 with Chapter3.
Qed.

Example R_dot_3_10_2_test:
  R [] (e_s (dot (star (amp (p_e x [])))  (i_i 0)))
    [] (e_s (dot (p_e x [])               (i_i 0))).
Proof.
  apply R_dot_3_10_2.
  eauto 10 with Chapter3.
Qed.

(* TODO I should really make these change h to h' under e's evaluation. *)

Example Bug14_e_e': 
 ~ R [] (e_s (i_e (i_i 0)))
     [] (e_s (i_e (i_i 1))).
Proof.
  compute.
  intros H.
  inversion H.
Qed.

(* Bug 17, L's instead of R's on precondition to 3.10 rules. *)
Example R_assign_3_10_3_test:
  R h (e_s (assign (p_e x pdot) e))
    h (e_s (assign (p_e x pdot) e')).
Proof.
  apply R_assign_3_10_3.
  eauto 10 with Chapter3.
Qed.

Example R_inst_3_10_4_test:
  R h  (e_s (inst e tau))
    h (e_s (inst e' tau)).
Proof.
  apply R_inst_3_10_4.
  eauto 10 with Chapter3.
Qed.

Example R_pack_3_10_5_test:
  R h  (e_s (pack tau' e  (etype nowitnesschange alpha k tau)))
    h  (e_s (pack tau' e' (etype nowitnesschange alpha k tau))).
Proof.
  apply R_pack_3_10_5.
  eauto 10 with Chapter3.
Qed.

(* Bug 18, Tau unquantified in three rules. *)
Example R_cpair_3_10_6_test:
  R h (e_s (cpair e e2))
    h (e_s (cpair e' e2)).
Proof.
  apply R_cpair_3_10_6.
  eauto 10 with Chapter3.
Qed.

Example R_cpair_3_10_7_test:
  R h (e_s (cpair v e))
    h (e_s (cpair v e')).
Proof.
  apply R_cpair_3_10_7;
  eauto 10 with Chapter3.
Qed.

Example R_cpair_3_10_8_test:
  R h (e_s (cpair e e2))
    h (e_s (cpair e' e2)).
Proof.
  apply R_cpair_3_10_8.
  eauto 10 with Chapter3.
Qed.

Example R_appl_3_10_9_test:
  R h (e_s (appl e e2))
    h (e_s (appl e' e2)).
Proof.
  apply R_appl_3_10_9.
  eauto 10 with Chapter3.
Qed.

Example R_appl_3_10_10_test:
  R h (e_s (appl v e))
    h (e_s (appl v e')).
Proof.
  apply R_appl_3_10_10;
  eauto 10 with Chapter3.
Qed.

(* Test L *)

Example L_xpi_3_1_test:
  L h (e_s (dot (p_e x nil) (i_i Z0))) 
    h (e_s (p_e x [(i_pe (i_i Z0))])).
Proof.
 apply L_xpi_3_1.
Qed.

Example L_staramp_3_2_test:
  L h (e_s (star (amp (p_e x nil)))) h (e_s (p_e x nil)).
Proof.
 apply L_staramp_3_2.
Qed.

(* Bug 11, h should have been h'. *)
(* Bug 14, extra e in quantification. *)
Example L_star_3_3_test:
  L h (e_s (star e)) h (e_s (star e')) .
Proof.
 eapply L_star_3_3.
 eauto 10 with Chapter3.
Qed.

(* Bug 19, extra quantified variable. *)
Example L_ei_3_4_test:
  L [] (e_s (dot (dot (p_e x []) (i_i 0)) (i_i 0)))
    [] (e_s (dot (p_e x ([] ++ [i_pe (i_i 0)])) (i_i 0))).
Proof.
 apply L_ei_3_4.
 eauto 10 with Chapter3. 
Qed.

