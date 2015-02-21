(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

 This tests the static semantics of statements and expressions, pg. 63. 

*)
Set Implicit Arguments.
Require Export LanguageModuleDef.
Require Export DynamicSemanticsHeapObjects.
Require Export StaticSemanticsTypingHeapObjects.
Require Export StaticSemanticsKindingAndContextWellFormedness.
Require Export StaticSemantics.

Require Import TestUtilities.
Require Import Tacticals.

(* Test ret, the return checker. *)

Example ret_ret_test:
  ret (retn e).
Proof.
 apply ret_ret.
Qed.

Example ret_if_test_not:
  ~ret (if_s e (e_s (i_e (i_i 0))) (e_s (i_e (i_i 0)))).
Proof.
  compute.
  intros H.
  inversion H.
  inversion H2.
Qed.

Example ret_if_test:
  ret (if_s e (retn (i_e (i_i 0))) (retn (i_e (i_i 0)))).
Proof.
  apply ret_if;
  eauto 20 with Chapter3.
Qed.

Example ret_seq_1_test:
 ret (seq (retn (i_e (i_i 0))) (e_s (i_e (i_i 0)))).
Proof.
  apply ret_seq_1;
  eauto 20 with Chapter3.
Qed.

Example ret_seq_2_test:
  ret (seq (e_s (i_e (i_i 0))) (retn (i_e (i_i 0)))).
Proof.
  apply ret_seq_2;
  eauto 20 with Chapter3.
Qed.

Example ret_let_test:
  ret (letx x e (retn (i_e (i_i 0)))).
Proof.
  apply ret_let;
  eauto 20 with Chapter3.
Qed.

Example ret_open_test:
  ret (open e alpha x (retn (i_e (i_i 0)))).
Proof.
  apply ret_open.
  eauto 20 with Chapter3.
Qed.

Example ret_openstar_test:
  ret (openstar e alpha x (retn (i_e (i_i 0)))).
Proof.
  apply ret_openstar.
  eauto 20 with Chapter3.
Qed.

(* Test ltyp. *)

(* Bug 22, misnamed contructors in WFDG. *)
Example SL_3_1_test:
  ltyp ddot udot (G.ctxt x cint gdot) (p_e x []) cint.
Proof.
  apply SL_3_1 with (tau':=cint);
  eauto 20 with Chapter3.
Qed.

(* Bug 23, just got SL_3_2 wrong. *)
(* Bug 24, contexts were messed up due to trying to follow Dan's type overloading of WF. *)
Example SL_3_2_test:
  ltyp ddot udot (G.ctxt x (ptype cint) gdot) (star (p_e x [])) cint.
Proof.
  apply SL_3_2;
  eauto 20 with Chapter3.
Qed.

Example SL_3_3_test:
  ltyp ddot udot (G.ctxt x (cross cint cint) gdot) (dot (p_e x []) zero_pe) cint.
Proof.
  apply SL_3_3 with (t1:=cint). 
  apply SL_3_1 with (tau':= (cross cint cint)); 
  eauto 20 with Chapter3.
Qed.

Example SL_3_4_test:
  ltyp ddot udot (G.ctxt x (cross cint cint) gdot) (dot (p_e x []) one_pe) cint.
Proof.
(* Again syntax direction. *)
  apply SL_3_4 with (t0:=cint);   eauto 20 with Chapter3.
Qed.

(* Test styp *)
(* Return at the end of a program, any old type will do. *)
Example styp_e_test:
  styp ddot udot gdot tau (e_s e).
Proof.
  apply styp_e_3_1 with (tau':= cint);
  eauto 20 with Chapter3.
Qed.

(* Bug 25 bad constructor naming in SL. *)
Example styp_return_test:
  styp ddot udot gdot tau (retn e).
Proof.
  apply styp_return_3_2;
  eauto 20 with Chapter3.
Qed.

Example styp_seq_test:
  styp ddot udot gdot tau (seq s1 s2).
Proof.
  apply styp_seq_3_3;
  eauto 20 with Chapter3.
Qed.

Example styp_while_test:
  styp ddot udot gdot tau (while e s).
Proof.
  apply styp_while_3_4;
  eauto 20 with Chapter3.
Qed.

Example styp_if_test:
  styp ddot udot gdot tau (if_s e s1 s2).
Proof.
  apply styp_if_3_5; 
  eauto 20 with Chapter3.
Qed.
   
Example styp_let_test:
  styp ddot udot gdot tau  (letx x e s).
Proof.
  apply styp_let_3_6 with (tau':= cint);
  eauto 20 with Chapter3.
Qed.

Example K_B_test:
  K (D.ctxt alpha B ddot) (tv_t alpha) B.
Proof.
  apply K_B; eauto 20 with Chapter3.
Qed.

(* Let's make some polymorphic pairs. *)
Definition axaa  := etype aliases alpha A (cross (tv_t alpha) (tv_t alpha)).
Definition paxaa := pack cint (cpair (i_e (i_i 0)) (i_e (i_i 1))) axaa.
(* alpha is bound here to the witness type so we can pass it on inside. *)
Definition oaxaa := open paxaa alpha x (e_s (p_e x [i_pe zero_pe])).

(* Bug 31, aliases where phi is wanted in styp_open_3_7. *)
(* Bug 32, phi  where alieases is wanted in styp_open_3_8. *)
Example styp_open_test:
  styp ddot udot gdot 
       cint 
       (open (pack cint 
                   (cpair (i_e (i_i 0)) (i_e (i_i 1)))
                   (etype aliases alpha B 
                          (cross (tv_t alpha) (tv_t alpha))))
             alpha x (e_s (p_e x [i_pe zero_pe]))).
Proof.
  apply styp_open_3_7
        with (p    := aliases)
             (k    := B)
             (tau  := cint)
             (tau' := (cross (tv_t alpha) (tv_t alpha)));
   eauto 20 with Chapter3.
Qed.

Example styp_openstar_test:
  styp ddot udot gdot 
       cint 
       (openstar (pack cint 
                   (cpair (i_e (i_i 0)) (i_e (i_i 1)))
                   (etype aliases alpha B 
                          (cross (tv_t alpha) (tv_t alpha))))
             alpha x (e_s (p_e x [i_pe zero_pe]))).
Proof.
  apply styp_openstar_3_8
        with (k    := B)
             (tau  := cint)
             (tau' := (cross (tv_t alpha) (tv_t alpha)));
  eauto 20 with Chapter3.
Qed.

(* Test rtyp. *)

(* Bug 26, bad contexting in SR_3_2. *)
Example SR_3_1_test:
  rtyp ddot udot (G.ctxt x tau gdot) (p_e x []) tau.
Proof.
  apply SR_3_1 with (tau':= tau); 
  eauto 20 with Chapter3.
Qed.

Example SR_3_2_test:
  rtyp ddot udot (G.ctxt x (ptype cint) gdot) (star (p_e x [])) cint.
Proof.
  apply SR_3_2;
  eauto 20 with Chapter3.
Qed.
      
Example SR_3_3_test:
  rtyp ddot udot gdot (dot (cpair (i_e (i_i 0)) (i_e (i_i 1))) zero_pe) cint.
Proof.
  apply SR_3_3 with (t1:=cint);
  eauto 20 with Chapter3.
Qed.

Example SR_3_4_test:
  rtyp ddot udot (G.ctxt x (cross cint cint) gdot)
       (dot (p_e x []) one_pe) cint.
Proof.
  apply SR_3_4 with (t0:= cint).
  eauto 20 with Chapter3.
Qed.

Example SR_3_5_test:
  rtyp ddot udot gdot (i_e (i_i 0)) cint.
Proof.
  apply SR_3_5.
  eauto 20 with Chapter3.
Qed.

(* Bug 27, star instead of amp. *)
Example SR_3_6_test:
  rtyp ddot udot (G.ctxt x (cross cint cint) gdot)
       (amp (p_e x [])) (ptype (cross cint cint)).
Proof.
  apply SR_3_6.
  eauto 20 with Chapter3.
Qed.

Example SR_3_7_test:
  rtyp ddot udot gdot (cpair (i_e (i_i 0)) (i_e (i_i 1))) (cross cint cint).
Proof.
  apply SR_3_7;
  eauto 20 with Chapter3.
Qed.

Example SR_3_8_test:
  rtyp ddot udot (G.ctxt x cint gdot)
       (assign (p_e x []) (i_e (i_i 0))) cint.
Proof.
  apply SR_3_8;
  eauto 20 with Chapter3.
Qed.

(* Bug 29, again can't type (ret (e_s (p_e ...))) *)
(* Bug 34, overly general typing, in SR_3_5 must make it specific to integer. *)

Example SR_3_9_test:
  rtyp ddot udot gdot 
       (appl (f_e (dfun cint x cint (retn (p_e x []))))
             (i_e (i_i 0)))
       cint.
Proof.
  apply SR_3_9 with (tau':= cint);   eauto 20 with Chapter3.
Qed.

Example SR_3_10_test:
  rtyp ddot udot gdot 
       (call (retn (i_e (i_i 0))))
       cint.
Proof.
  apply SR_3_10;
  eauto 20 with Chapter3.
Qed.

(* TODO totally bogus e in here. *)
Example SR_3_11_test:
  rtyp 
    ddot udot gdot
    (inst (f_e (ufun alpha B
                     (dfun (tv_t alpha) x (tv_t alpha) (retn (p_e x [])))))
          cint)
    (subst_Tau (arrow (tv_t alpha) (tv_t alpha)) cint alpha).
Proof.
  apply SR_3_11 with (k:= B);
  eauto 20 with Chapter3.
Qed.

(* TODO why wont' this kind at A? *)
Example SR_3_12_test:
  rtyp ddot udot gdot
       (pack cint (cpair (i_e (i_i 0)) (i_e (i_i 1))) 
             (etype aliases alpha B (cross (tv_t alpha) (tv_t alpha))))
       (etype aliases alpha B (cross (tv_t alpha) (tv_t alpha))).
Proof.
  apply SR_3_12;
  eauto 20 with Chapter3.
Qed.

Example SR_3_13_test:
  rtyp ddot udot gdot 
       (f_e (dfun cint x cint (retn (i_e (i_i 0)))))
       (arrow cint cint).
Proof.
  apply SR_3_13;
  eauto 20 with Chapter3.
Qed.

Definition pid := (dfun (tv_t alpha) x (tv_t alpha) (retn (p_e x []))).

(* Bug 35, extra E quantified, extra Tau. *)

Example SR_3_14_test:
  rtyp ddot udot gdot 
       (f_e (ufun alpha B (dfun (tv_t alpha) x (tv_t alpha) (retn (p_e x [])))))
       (utype alpha B (arrow (tv_t alpha) (tv_t alpha))).
Proof.
  apply SR_3_14; eauto 20 with Chapter3.
Qed.

(* Test htyp. *)

(* Bug 12, unused Gamma in quantifier. *)
(* Bug 13, unused H in quantifier. *)
(* Bug 16, H x->v H' not H x->v. *)

Example htyp_empty_test:
  htyp udot gdot hdot gdot.
Proof.
  apply htyp_empty;
  eauto 20 with Chapter3.
Qed.

Example htyp_xv_test:
  htyp udot gdot (H.ctxt x v hdot) (G.ctxt x tau gdot).
Proof.
  (* loss of syntax direction here but we don't mind really as eauto is working. *)
  (* eauto 20 with Chapter3. *)
  eapply htyp_xv with (g':= gdot);
  eauto 20 with Chapter3.
Qed.

(* Test refp. *)

Example refp_empty_test:
  refp h udot.
Proof.
 apply refp_empty.
Qed.

(* TODO why ? H totally wrong for this. Closer, no cigar. *)
(* Bug 36, forgot PairIsAValue. *)
(* Bug 37, forgot PackIsAValue has a wrongly constrained tau. *)
(* TODO loop bug. *)
(*
Example refp_pack_test:
  refp [(x,
         pack (cross cint cint) 
              (cpair (i_e (i_i 0)) (i_e (i_i 0))) 
              (etype aliases alpha A (cross cint cint)))]
       ([((x, [u_pe]), (cross cint cint))] ++ []).
Proof.
  constructor.
  eauto 20 with Chapter3.
  apply refp_pack with 
  (k     := A) 
  (v     := (cpair (i_e (i_i 0)) (i_e (i_i 0))))
  (v'    := pack (cross cint cint) 
                 (cpair (i_e (i_i 0)) (i_e (i_i 0))) 
                 (etype aliases alpha A (cross cint cint)))
  (tau   := (cross cint cint))
  (alpha := alpha);
  eauto 20 with Chapter3.
  constructor.
  constructor.
  constructor.
  constructor.
  constructor.
   (* Bug, after get(v,[],v) fix. *)
Admitted.
*)

(* Test prog. *)

Example program_test:
  prog hdot (retn (i_e (i_i 0))).
Proof.
  apply program with (u:= udot) (g:= gdot) (tau:=cint);
  eauto 20 with Chapter3.
Qed.
