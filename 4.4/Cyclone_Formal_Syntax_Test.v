(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

 This tests the formal syntax, pg. 57. 
 But it also tests the contexts for historical reasons.

*)


Set Implicit Arguments.
Require Import Cyclone_Formal_Syntax Cyclone_Test_Utilities Cyclone_LN_Tactics.
Close Scope list_scope.
Import LibEnvNotations.



Check A : Kappa.
Check B : Kappa.

Check (ftvar alpha_) : Tau.

Check witnesschanges : Phi.
Check aliases         : Phi.

Check (ftvar alpha_) : Tau.
Check cint : Tau.
Check cross cint cint : Tau.
Check arrow cint cint : Tau.
Check ptype cint : Tau.
Check utype A cint : Tau.
Check etype aliases B cint : Tau.

Check (fevar varx) : V.

Check e_s  (i_e (i_i 0)) : St.
Check retn (i_e (i_i 0)) : St.
Check seqx (e_s (i_e (i_i 0))) (retn (i_e (i_i 0))) : St.
Check if_s (i_e (i_i 0)) (e_s  (i_e (i_i 0))) (retn (i_e (i_i 0))) : St.
Check while (i_e (i_i 0)) (retn (i_e (i_i 0))) : St.
Check letx  (i_e (i_i 0)) (retn (p_e x nil)) : St.
Check openx (i_e (i_i 0)) (retn (p_e x nil)) : St.
Check openstar (i_e (i_i 0)) (retn (p_e x nil)) : St.

Example NumValue : Value (i_e (i_i 0)).
Proof.
  apply IIsAValue.
Qed.

Example AmpValue : 
  Value (amp (p_e x (cons (i_pe one_pe) nil))).
Proof.
  auto.
Qed.

Example FunctionValue : 
  Value (f_e (dfun cint cint (retn (p_e x nil)))). 
Proof.
  auto.
Qed.

Example PolymorphicFunctionValue : 
  Value (f_e (ufun  A
                   (dfun cint cint (retn (p_e x nil))))).
Proof.
  auto.
Qed.

Ltac auto_env :=
  try solve[ autounfold;
             autorewrite with env_defs;
             intros;
             auto;
             try unfold get_impl;
             try unfold LVPE.V.get_impl;
             simpl;
             try case_var~;
             try case_var~].

Hint Extern 1 (get _ _ = _) => auto_env.

Example NotInDomHnil :
  get varx hdot  = None.
Proof.
  auto.
Qed.

Example NotInDomHsingle :
  get varx hdot = None.
Proof.
  auto.
Qed.

Example NotInDomHdifferent :
  varx <> vary ->
  get vary ((single varx v0) & hdot) = None. 
Proof.
  auto.
Qed.

Example NotInDomHsecond :
  vary <> varx ->
  vary <> varz ->
  get vary ((single varx v0) & ((varz ~ v0) & hdot)) = None.
Proof.
  auto.
Qed.

Example NotInDomDnil :
  get vary ddot = None.
Proof.
  auto.
Qed.

Example NotInDomDsingle :
  get alpha_ ((single alpha_ A) & ddot) = Some A.
Proof.
  auto.
Qed.

Example NotInDomDdifferent :
  alpha_ <> beta_ ->
  get beta_ ((single alpha_ B) & ddot) = None.
Proof.
  auto.
Qed.

Example NotInDomDsecond :
  alpha_ <> beta_ ->
  beta_ <> gamma_ ->
   get beta_ ((single alpha_ A) & (single gamma_ B) & ddot) = None.
Proof.
  auto.
Qed.

(* Just to allow me to see how case_var handles things. *)
Example case_var_abstract_unknown:
  forall (v v' : var),
  (If (v = v') then True else False).
Proof.
  intros.
  try case_var.
  admit.
  admit.
Qed.



Example case_var_abstract_eq:
  forall (v v' : var),
    v = v' ->
    (If (v = v') then True else False).
Proof.
  intros.
  case_var~.
Qed.

Example case_var_abstract_neq:
  forall (v v' : var),
    v <> v' ->
    (If (v = v') then True else False).
Proof.
  intros.
  case_var~.
  admit.
Qed.


(*
 case 
  1) abstract pair q q'
     1a) q = q'  - resolve
     1b) q <> q' - resolve
     1c) unknown - two goals
     1d) q twice

  2) concrete pair (x,y) (x',y')
     2a) unknown - two goals - resolved with If_r/l
     2b) x <> x' - resolve
     2c) y <> y' - resolve
     2d) x twice 
     2e) y twice

 Do I need the lemmas?
 When and how do I apply If_l/r?
 *)

Example get_Upsilon_abstract_unknown:
  forall vp vp',
  LVPE.V.get vp (LVPE.V.concat udot (LVPE.V.single vp' tau))  = Some tau.
Proof.
  intros.
  simpl_env.
  try case_varpath.
  auto.
Admitted.

Example get_Upsilon_abstract_identical:
  forall vp,
    (If vp = vp then Some tau else LVPE.V.get vp udot) = Some tau.
Proof.
  intros.
  simpl_env.
Qed.

Example get_Upsilon_abstract_eq:
  forall vp vp',
    vp = vp' ->
    LVPE.V.get vp (LVPE.V.concat udot (LVPE.V.single vp' tau))  = Some tau.
Proof.
  intros.
  simpl_env.
Qed.

Example get_Upsilon_abstract_neq:
  forall vp vp',
    vp <> vp' ->
    LVPE.V.get vp (LVPE.V.concat udot (LVPE.V.single vp' tau))  = None.
Proof.
  intros.
  simpl_env.
  auto.
Qed.

Example get_Upsilon_pair_abstract:
  forall x x' p p',
    LVPE.V.get (x,p) (LVPE.V.concat udot (LVPE.V.single (x',p') tau) )  = Some tau.
Proof.
  intros.
  try simpl_env.
  admit.
Qed.

Example get_Upsilon_pair_known_eq:
  forall x p,
    LVPE.V.get (x,p) (LVPE.V.concat udot (LVPE.V.single (x,p) tau))  = Some tau.
Proof.
  intros; simpl_env.
Qed.

(* Bug in coqc ?  It runs interactively but not on compile.
Ltac case_if_eq_base_resolve_if E F H :=
  destruct (classicT (E = F)) as [H|H];
  [tryfalse; try subst E; try apply~ If_l | tryfalse; try apply~ If_r].

Example getUx_abstract_neq_l:
  forall x p x',
    x <> x' ->
    LVPE.V.get (x,p) (LVPE.V.concat udot (LVPE.V.single (x',p) tau)) = None.
Proof.
  intros.
  simpl_env.
Qed.


Example getUx_abstract_unknown_r:
  forall x p x' p',
    x = x' ->
    LVPE.V.get (x,p) (LVPE.V.concat udot (LVPE.V.single (x',p') tau)) = Some tau.
Proof.
  intros.
  try simpl_env.
  admit.
Qed.
Check getUx_abstract_unknown_r.

Example getUx_abstract_unknown_l:
  forall x p x' p',
    p = p' ->
    LVPE.V.get (x,p) (LVPE.V.concat udot (LVPE.V.single (x',p') tau)) = Some tau.
Proof.
  intros.
  try simpl_env.
  admit.
Qed.
Check getUx_abstract_unknown_l.
*)
