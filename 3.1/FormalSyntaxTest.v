(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

 This tests the formal syntax, pg. 57. 
 But it also tests the contexts for historical reasons.

*)

Set Implicit Argument.
Require Export LanguageModuleDef.
Require Import TestUtilities.


Check A : K.T.
Check B : K.T.

Check (TV.var 0) : TV.T.

Check witnesschanges : Phi.
Check aliases         : Phi.

Check (tv_t (TV.var 0)) : Tau.
Check cint : Tau.
Check cross cint cint : Tau.
Check arrow cint cint : Tau.
Check ptype cint : Tau.
Check utype (TV.var 0) A cint : Tau.
Check etype aliases (TV.var 0) B cint : Tau.

Check evar 0 : EVar.

Check e_s  (i_e (i_i Z0)) : St.
Check retn (i_e (i_i Z0)) : St.
Check seq (e_s  (i_e (i_i Z0))) (retn (i_e (i_i Z0))) : St.
Check if_s (i_e (i_i Z0)) (e_s  (i_e (i_i Z0))) (retn (i_e (i_i Z0))) : St.
Check while (i_e (i_i Z0)) (retn (i_e (i_i Z0))) : St.
Check letx  (evar 0) (i_e (i_i Z0)) (retn (p_e (evar 0) [])) : St.
Check open (i_e (i_i Z0)) (TV.var 0) (evar 0) (retn (p_e (evar 0) [])) : St.
Check openstar (i_e (i_i Z0)) (TV.var 0) (evar 0) (retn (p_e (evar 0) [])) : St.

Example NumValue : Value (i_e (i_i Z0)).
Proof.
  apply IIsAValue.
Qed.

(* Bug 1, no amp in source. *)
Example AmpValue : 
  Value (amp (p_e (evar 0) [(i_pe one_pe)])).
Proof.
  apply AmpIsAValue.
Qed.

(* 2 bugs found, extra variable in quantification. *)
Example FunctionValue : 
  Value (f_e (dfun cint (evar 0) cint (retn (p_e (evar 0) [])))). 
Proof.
  apply DfunIsAValue.
Qed.

Example PolymorphicFunctionValue : 
  Value (f_e (ufun (TV.var 0) A
                   (dfun cint (evar 0) cint (retn (p_e (evar 0) []))))).
Proof.
  apply UfunIsAValue.
Qed.

Example NotInDomHnil :
  HM.map hdot (evar 0)  = None.
Proof.
  reflexivity.
Qed.

Example NotInDomHsingle :
  HM.map hdot (evar 0)  = None.
Proof.
  reflexivity.
Qed.

Example NotInDomHdifferent :
  HM.map (hctxt x v0 hdot) y = None. 
Proof.
  reflexivity.
Qed.

Example NotInDomHsecond :
  HM.map (hctxt x v0 (hctxt z v0 hdot)) y = None.
Proof.
  reflexivity.
Qed.

Example NotInDomDnil :
  DM.map ddot (TV.var 0) = None.
Proof.
  reflexivity.
Qed.

Example NotInDomDsingle :
  DM.map (dctxt alpha A ddot) alpha = Some A.
Proof.
  reflexivity.
Qed.

Example NotInDomDdifferent :
   DM.map (dctxt alpha B ddot) beta = None.
Proof.
  reflexivity.
Qed.

Example NotInDomDsecond :
   DM.map (dctxt alpha A (dctxt gamma B ddot)) beta = None.
Proof.
  reflexivity.
Qed.

(* TODO test setH. *)

Example deleteH_test_nil : 
  HM.delete hdot x = hdot.
Proof.
  reflexivity.
Qed.

Example deleteH_test_x :
  HM.delete (hctxt x (i_e (i_i 0)) hdot) x = hdot.
Proof.
  reflexivity.
Qed.

Example delete_test_xy :
  HM.delete (hctxt y (i_e (i_i 0)) (hctxt x (i_e (i_i 0)) hdot)) x = 
            (hctxt y (i_e (i_i 0)) hdot).
Proof.
  reflexivity.
Qed.

Example delete_test_yx :
  HM.delete (hctxt y (i_e (i_i 0)) (hctxt x (i_e (i_i 0)) hdot)) y = 
            (hctxt x (i_e (i_i 0)) hdot).
Proof.
 reflexivity.
Qed.

Example delete_test_z :
  HM.delete (hctxt y (i_e (i_i 0)) (hctxt x (i_e (i_i 0)) hdot)) z = 
            (hctxt y (i_e (i_i 0)) (hctxt x (i_e (i_i 0)) hdot)).
Proof.
 reflexivity.
Qed.

Example DMadd_nil :
  DM.add ddot alpha A = (dctxt alpha A ddot).
Proof.
  reflexivity.
Qed.

Example DMadd_exists :
  DM.add (dctxt alpha B ddot) alpha A = (dctxt alpha A ddot).
Proof.
  reflexivity.
Qed.

Example DMadd_add_to_end :
  DM.add (dctxt alpha B ddot) beta A = (dctxt alpha B (dctxt beta A ddot)).
Proof.
  reflexivity.
Qed.

Example DMadd_overwrite_at_end :
  DM.add (dctxt alpha B (dctxt beta B ddot)) beta A = 
  (dctxt alpha B (dctxt beta A ddot)).
Proof.
  reflexivity.
Qed.

Example DMadd_overwrite_at_start :
  DM.add (dctxt alpha B (dctxt beta B ddot)) alpha A = 
         (dctxt alpha A (dctxt beta B ddot)).
Proof.
  reflexivity.
Qed.

Example GMmapx : 
  GM.map (gctxt x tau gdot) x = Some tau.
Proof.
  reflexivity.
Qed.

Example GMmapyx : 
  GM.map (gctxt y tau (gctxt x tau' gdot)) x = Some tau'.
Proof.
  reflexivity.
Qed.

Example NotInDomGnil :
  GM.map gdot (evar 0) = None.
Proof.
  reflexivity.
Qed.

Example NotInDomGsingle :
  GM.map (gctxt x tau gdot) x = Some tau.
Proof.
  reflexivity.
Qed.

Example NotInDomGdifferent :
   GM.map  (gctxt x tau gdot) y = None.
Proof.
  reflexivity.
Qed.

Example NotInDomGsecond :
  GM.map (gctxt x tau (gctxt z tau' gdot)) y = None.
Proof.
  reflexivity.
Qed.

Example getUnil :
  forall (tau : Tau),
    ~GM.map gdot x = Some tau.
Proof.
  intros.
  compute.
  intros.
  inversion H0.
Qed.

Example path_eq:
  beq_path [] [] = true.
Proof.
  reflexivity.
Qed.

Example getUx : 
  UM.map (uctxt (x, p0) tau udot) (x,p0) = Some tau.
Proof.
  compute.
  constructor.
Qed.

(* Bug 6 in defintion x <>y \/ [] = nil. *)
Example UMmapyx : 
  UM.map (uctxt (y,nil) tau (uctxt (x, nil) tau' udot)) (x,[]) = Some tau'.
Proof.
  reflexivity.
Qed.

