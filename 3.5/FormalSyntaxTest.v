(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

 This tests the formal syntax, pg. 57. 
 But it also tests the contexts for historical reasons.

*)

Set Implicit Arguments.
Require Export LanguageModuleDef.
Require Import TestUtilities.


Check A : Kappa.
Check B : Kappa.

Check (TV.var 0) : TVar.

Check witnesschanges : Phi.
Check aliases         : Phi.

Check (ftvar (TV.var 0)) : Tau.
Check (btvar 0) : Tau.
Check cint : Tau.
Check cross cint cint : Tau.
Check arrow cint cint : Tau.
Check ptype cint : Tau.
Check utype A cint : Tau.
Check etype aliases B cint : Tau.

Check EV.var 0 : EVar.

Check e_s  (i_e (i_i 0)) : St.
Check retn (i_e (i_i 0)) : St.
Check seq (e_s  (i_e (i_i 0))) (retn (i_e (i_i 0))) : St.
Check if_s (i_e (i_i 0)) (e_s  (i_e (i_i 0))) (retn (i_e (i_i 0))) : St.
Check while (i_e (i_i 0)) (retn (i_e (i_i 0))) : St.
Check letx  (i_e (i_i 0)) (retn (p_e (bevar 0) [])) : St.
Check open (i_e (i_i 0)) (retn (p_e fx [])) : St.
Check openstar (i_e (i_i 0)) (retn (p_e fx [])) : St.

Example NumValue : Value (i_e (i_i 0)).
Proof.
  apply IIsAValue.
Qed.

(* Bug 1, no amp in source. *)
Example AmpValue : 
  Value (amp (p_e fx [(i_pe one_pe)])).
Proof.
  apply AmpIsAValue.
Qed.

(* 2 bugs found, extra variable in quantification. *)
Example FunctionValue : 
  Value (f_e (dfun cint cint (retn (p_e b0 [])))). 
Proof.
  apply DfunIsAValue.
Qed.

Example PolymorphicFunctionValue : 
  Value (f_e (ufun A
                   (dfun cint cint (retn (p_e b0 []))))).
Proof.
  apply UfunIsAValue.
Qed.

Example NotInDomHnil :
  H.map H.dot (EV.var 0)  = None.
Proof.
  reflexivity.
Qed.

Example NotInDomHsingle :
  H.map H.dot (EV.var 0)  = None.
Proof.
  reflexivity.
Qed.

Example NotInDomHdifferent :
  H.map (H.ctxt x v0 H.dot) y = None. 
Proof.
  reflexivity.
Qed.

Example NotInDomHsecond :
  H.map (H.ctxt x v0 (H.ctxt z v0 H.dot)) y = None.
Proof.
  reflexivity.
Qed.

Example NotInDomDnil :
  D.map D.dot (TV.var 0) = None.
Proof.
  reflexivity.
Qed.

Example NotInDomDsingle :
  D.map (D.ctxt alpha A D.dot) alpha = Some A.
Proof.
  reflexivity.
Qed.

Example NotInDomDdifferent :
   D.map (D.ctxt alpha B D.dot) beta = None.
Proof.
  reflexivity.
Qed.

Example NotInDomDsecond :
   D.map (D.ctxt alpha A (D.ctxt gamma B D.dot)) beta = None.
Proof.
  reflexivity.
Qed.

(* TODO test setH. *)

Example deleteH_test_nil : 
  H.delete H.dot x = H.dot.
Proof.
  reflexivity.
Qed.

Example deleteH_test_x :
  H.delete (H.ctxt x (i_e (i_i 0)) H.dot) x = H.dot.
Proof.
  reflexivity.
Qed.

Example delete_test_xy :
  H.delete (H.ctxt y (i_e (i_i 0)) (H.ctxt x (i_e (i_i 0)) H.dot)) x = 
            (H.ctxt y (i_e (i_i 0)) H.dot).
Proof.
  reflexivity.
Qed.

Example delete_test_yx :
  H.delete (H.ctxt y (i_e (i_i 0)) (H.ctxt x (i_e (i_i 0)) H.dot)) y = 
            (H.ctxt x (i_e (i_i 0)) H.dot).
Proof.
 reflexivity.
Qed.

Example delete_test_z :
  H.delete (H.ctxt y (i_e (i_i 0)) (H.ctxt x (i_e (i_i 0)) H.dot)) z = 
            (H.ctxt y (i_e (i_i 0)) (H.ctxt x (i_e (i_i 0)) H.dot)).
Proof.
 reflexivity.
Qed.

Example DMadd_nil :
  D.add D.dot alpha A = (D.ctxt alpha A D.dot).
Proof.
  reflexivity.
Qed.

Example DMadd_exists :
  D.add (D.ctxt alpha B D.dot) alpha A = (D.ctxt alpha A D.dot).
Proof.
  reflexivity.
Qed.

Example DMadd_add_to_end :
  D.add (D.ctxt alpha B D.dot) beta A = (D.ctxt alpha B (D.ctxt beta A D.dot)).
Proof.
  reflexivity.
Qed.

Example DMadd_overwrite_at_end :
  D.add (D.ctxt alpha B (D.ctxt beta B D.dot)) beta A = 
  (D.ctxt alpha B (D.ctxt beta A D.dot)).
Proof.
  reflexivity.
Qed.

Example DMadd_overwrite_at_start :
  D.add (D.ctxt alpha B (D.ctxt beta B D.dot)) alpha A = 
         (D.ctxt alpha A (D.ctxt beta B D.dot)).
Proof.
  reflexivity.
Qed.

Example GMmapx : 
  G.map (G.ctxt x tau G.dot) x = Some tau.
Proof.
  reflexivity.
Qed.

Example GMmapyx : 
  G.map (G.ctxt y tau (G.ctxt x tau' G.dot)) x = Some tau'.
Proof.
  reflexivity.
Qed.

Example NotInDomGnil :
  G.map G.dot (EV.var 0) = None.
Proof.
  reflexivity.
Qed.

Example NotInDomGsingle :
  G.map (G.ctxt x tau G.dot) x = Some tau.
Proof.
  reflexivity.
Qed.

Example NotInDomGdifferent :
   G.map  (G.ctxt x tau G.dot) y = None.
Proof.
  reflexivity.
Qed.

Example NotInDomGsecond :
  G.map (G.ctxt x tau (G.ctxt z tau' G.dot)) y = None.
Proof.
  reflexivity.
Qed.

Example getUnil :
  forall (tau : Tau),
    ~G.map G.dot x = Some tau.
Proof.
  intros.
  compute.
  intros.
  inversion H.
Qed.

Example path_eq:
  Path.eqb [] [] = true.
Proof.
  reflexivity.
Qed.

Example getUx : 
  U.map (U.ctxt (x, p0) tau U.dot) (x,p0) = Some tau.
Proof.
  compute.
  constructor.
Qed.

(* Bug 6 in defintion x <>y \/ [] = nil. *)
Example UMmapyx : 
  U.map (U.ctxt (y,nil) tau (U.ctxt (x, nil) tau' U.dot)) (x,[]) = Some tau'.
Proof.
  reflexivity.
Qed.

