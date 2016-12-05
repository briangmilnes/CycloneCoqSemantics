(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

 This tests the static semantics of statements and expressions, pg. 63. 

*)
Set Implicit Arguments.
Require Import Cyclone_Static_Semantics.
Require Import Cyclone_Test_Utilities.
Require Import Cyclone_LN_Tactics.
Close Scope list_scope.
Import LibEnvNotations.
Import LVPE.LibVarPathEnvNotations.

Ltac fv_of_static_goal :=
  match goal with
    | |- styp ?d ?u ?g ?t ?s =>
      constr:((fv_delta d) \u (fv_upsilon u) \u (fv_gamma g) \u (TTM.fv_st s)
                           \u (TM.fv_st s) \u (T.fv t)) 
    | |- ltyp ?d ?u ?g ?e ?t => 
      constr:((fv_delta d) \u (fv_upsilon u) \u (fv_gamma g) \u (TTM.fv_e e)
                           \u (TM.fv_e e) \u (T.fv t))
    | |- rtyp ?d ?u ?g ?e ?t => 
      constr:((fv_delta d) \u (fv_upsilon u) \u (fv_gamma g) \u (TTM.fv_e e)
                           \u (TM.fv_e e) \u (T.fv t))
  end.

Hint Extern 6 (styp _ _ _ _ (letx _ _))          
	=> idtac "1"; apply_fresh_from* styp_let_3_6 with fv_of_static_goal.
Hint Extern 6 (styp _ _ _ _ (openx _ _))         
	=> idtac "2"; apply_fresh_from* styp_open_3_7 with fv_of_static_goal.
Hint Extern 6 (styp _ _ _ _ (openstar _ _))      
	=> idtac "3"; apply_fresh_from* styp_openstar_3_8 with fv_of_static_goal.
Hint Extern 6 (rtyp _ _ _ (pack _ _ _) _)       
	=> idtac "4"; apply_fresh_from* SR_3_12 with fv_of_static_goal.
Hint Extern 6 (rtyp _ _ _ (f_e (ufun _ _)) _)    
	=> idtac "5"; apply_fresh_from* SR_3_14 with fv_of_static_goal.
Hint Extern 6 (rtyp _ _ _ (f_e (dfun _ _ _ )) _) 
	=> idtac "6"; apply_fresh_from* SR_3_13 with fv_of_static_goal.


Hint Extern 6 (styp _ _ _ _ (TM.open_rec_st _ _ _)) =>
 idtac "7"; simpls~; try case_nat~;try case_nat~.
(* Bug This can cause stack overflow. *)
Hint Extern 6 (rtyp _ _ _ _ (T.open_rec _ _ _))     =>
 idtac "8"; simpls~; try case_nat~; try case_nat~.
Hint Extern 6 (rtyp _ _ _ (TTM.open_rec_f _ _ _) _) =>
 idtac "9"; simpls~; try case_nat~; try case_nat~.
Hint Extern 6 (rtyp _ _ _ (f_e (TTM.open_rec_f _ _ _)) _) =>
 idtac "10";  simpl; try case_nat~; try case_nat~.
Hint Extern 6 (styp _ _ _ _ (TM.open_rec_st _ _ _)) =>
 idtac "11"; simpls~; try case_nat~; try case_nat~.

Hint Extern 4 (ltyp _ _ _ (p_e _ _) _) =>
 idtac "12"; applys~ SL_3_1.
Hint Extern 4 (rtyp ?a ?b ?c (p_e ?d ?e) ?f) =>
 idtac "13" a b c d e f; applys~ SR_3_1.
Hint Extern 4 (ltyp _ _ _  (dot (p_e _ _) zero_pe) _) =>
 idtac "14"; applys~ SL_3_3.
Hint Extern 4 (ltyp _ _ _ (dot (p_e _ _) one_pe)  _)  =>
 idtac "15"; applys~ SL_3_4.
Hint Extern 4 (rtyp _ _ _ (dot _ zero_pe) _)          =>
 idtac "16"; applys~ SR_3_3.
Hint Extern 4 (rtyp _ _ _ (dot _ one_pe)  _)          =>
 idtac "17"; applys~ SR_3_4.
Hint Extern 4 (styp _ _ _ _ (e_s _))                  =>
 idtac "18"; applys~ styp_e_3_1.
Hint Extern 6 (rtyp _ _ _ (appl _ _) _)               =>
 idtac "19"; applys~ SR_3_9.

(* Test ret, the return checker. *)

Example ret_ret_test:
  ret (retn e).
Proof.
  auto. (* apply ret_ret.*)
Qed.

Example ret_if_test_not:
  ~ret (if_s e (e_s (i_e (i_i 0))) (e_s (i_e (i_i 0)))).
Proof.
  intros H.
  inversion H.
  inversion H2.
Qed.

Example ret_if_test:
  ret (if_s e (retn (i_e (i_i 0))) (retn (i_e (i_i 0)))).
Proof.
  auto. (* apply ret_if;*)
Qed.

Example ret_seq_1_test:
 ret (seqx (retn (i_e (i_i 0))) (e_s (i_e (i_i 0)))).
Proof.
  auto. (* apply ret_seq_1;*)
Qed.

Example ret_seq_2_test:
  ret (seqx (e_s (i_e (i_i 0))) (retn (i_e (i_i 0)))).
Proof.
  auto.
  (* apply ret_seq_2;*)
Qed.

Example ret_let_test:
  ret (letx e (retn (i_e (i_i 0)))).
Proof.
  auto. (* apply ret_let.*)
Qed.

Example ret_open_test:
  ret (openx e (retn (i_e (i_i 0)))).
Proof.
  auto. (* apply ret_open.*)
Qed.

Example ret_openstar_test:
  ret (openstar e (retn (i_e (i_i 0)))).
Proof.
  auto. (* apply ret_openstar.*)
Qed.

(* Test ltyp. *)

Example SL_3_1_test:
  ltyp ddot udot (gdot & (varx ~ cint))  (p_e (fevar varx) nil) cint.
Proof.
  auto.
Qed.

Example SL_3_2_test:
  ltyp ddot udot (gdot & (varx ~ (ptype cint))) (star (p_e (fevar varx) nil)) cint.
Proof.
  auto.
  (* apply SL_3_2. *)
Qed.

Example SL_3_3_test:
  ltyp ddot udot (gdot & (varx ~ (cross cint cint)))
       (dot (p_e (fevar varx) nil) zero_pe) cint.
Proof.
  auto.
(*
  apply SL_3_3 with (t1:=cint). 
  apply SL_3_1 with (tau':= (cross cint cint)); 
  auto.
*)
Qed.

Example SL_3_4_test:
  ltyp ddot udot (gdot & (varx ~ (cross cint cint))) (dot (p_e (fevar varx) nil) one_pe) cint.
Proof.
  auto. (* apply SL_3_4 with (t0:=cint);   auto.*)
Qed.

(* Test styp *)
(* Return at the end of a program, any old type will do. *)
Example styp_e_test:
  styp ddot udot gdot tau (e_s e).
Proof.
  unfold_test_utilities.
  auto.
(*
  applys~ styp_e_3_1.
  auto.
  apply styp_e_3_1 with (tau':= cint);
  auto.
*)
Qed.

Example styp_return_test:
  styp ddot udot gdot tau (retn e).
Proof.
  unfold_test_utilities.
  auto.
(*  apply styp_return_3_2; *)
Qed.

Example styp_seq_test:
  styp ddot udot gdot tau (seqx s1 s2).
Proof.
  unfold_test_utilities.
  auto.
  (* apply styp_seq_3_3; *)
Qed.

Example styp_while_test:
  styp ddot udot gdot tau (while e s).
Proof.
  unfold_test_utilities.
  auto.
  (* apply styp_while_3_4; *)
Qed.

Example styp_if_test:
  styp ddot udot gdot tau (if_s e s1 s2).
Proof.
  unfold_test_utilities.
  auto.
  (* apply styp_if_3_5; *)
Qed.
   

Example styp_let_test:
  styp ddot udot gdot tau (letx e s).
Proof.
  unfold_test_utilities.
  auto.
  (* apply_fresh_from* styp_let_3_6 with fv_of_static_goal. *)
  (* apply styp_let_3_6 with (L:= ltac(fv_of_static_goal)) (tau':= cint); auto. *)
Qed.

Example K_B_test:
  K ((alpha_ ~ B) & ddot) (ftvar alpha_) B.
Proof.
  auto.
  (* apply K_B; auto *)
Qed.

(* Let's make some polymorphic pairs. *)
Definition axaa  := etype aliases A (cross (btvar 0) (btvar 0)).
Definition paxaa := pack cint (cpair (i_e (i_i 0)) (i_e (i_i 1))) axaa.
(* alpha is bound here to the witness type so we can pass it on inside. *)
Definition oaxaa := openx paxaa (e_s (p_e (bevar 0) (cons (i_pe zero_pe) nil))).
(*
Example styp_open_test:
  styp ddot udot gdot 
       cint 
       oaxaa.
Proof.
  unfold_test_utilities.
  unfold oaxaa, paxaa, axaa.
  apply styp_open_3_7
        with (L := \{})
             (p    := aliases)
             (k    := B)
             (tau  := cint)
             (tau' := (cross (btvar 0) (btvar 0))).
  simpl.
  case_nat.
  intros.
  apply styp_e_3_1 with (tau':= cint).
  admit.

  apply_fresh_from styp_open_3_7 with fv_of_static_goal.
  simpl.
  intros.
  case_nat~.

  admit.
  auto.

   auto.
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
  auto.
Qed.

*)

(* Test rtyp. *)

(* Bug 26, bad contexting in SR_3_2. *)
Example SR_3_1_test:
  rtyp ddot udot (gdot & (varx ~ tau)) (p_e x nil) tau.
Proof.
  auto.
  (* apply SR_3_1 with (tau':= tau); 
  auto. *)
Qed.

Example SR_3_2_test:
  rtyp ddot udot (gdot & (varx ~ (ptype cint))) (star (p_e x nil)) cint.
Proof.
  auto.
  (* apply SR_3_2;
  auto. *)
Qed.
      
Example SR_3_3_test:
  rtyp ddot udot gdot (dot (cpair (i_e (i_i 0)) (i_e (i_i 1))) zero_pe) cint.
Proof.
  auto.
  (* apply SR_3_3 with (t1:=cint); *)
Qed.

Example SR_3_4_test:
  rtyp ddot udot (gdot & (varx ~ (cross cint cint)))
       (dot (p_e x nil) one_pe) cint.
Proof.
  auto.
  (* apply SR_3_4 with (t0:= cint). *)
Qed.

Example SR_3_5_test:
  rtyp ddot udot gdot (i_e (i_i 0)) cint.
Proof.
  auto.
  (* apply SR_3_5. *)
Qed.

(* Bug 27, star instead of amp. *)
Example SR_3_6_test:
  rtyp ddot udot (gdot & (varx ~ (cross cint cint)))
       (amp (p_e x nil)) (ptype (cross cint cint)).
Proof.
  auto.
  (* apply SR_3_6. *)
Qed.

Example SR_3_7_test:
  rtyp ddot udot gdot (cpair (i_e (i_i 0)) (i_e (i_i 1))) (cross cint cint).
Proof.
  auto.
  (* apply SR_3_7;*)
Qed.

Example SR_3_8_test:
  rtyp ddot udot (gdot & (varx ~ cint))
       (assign (p_e x nil) (i_e (i_i 0))) cint.
Proof.
  auto.
  (* apply SR_3_8. *)
Qed.



Example SR_3_9_test:
  rtyp ddot udot gdot 
       (appl (f_e (dfun cint cint (retn (p_e (bevar 0) nil))))
             (i_e (i_i 0)))
       cint.
Proof.
  (* apply SR_3_9 with (tau':= cint);   auto. *)
  auto.
(* 
  applys~ SR_3_9.
  apply_fresh_from* SR_3_13 with fv_of_static_goal.
  simpls~.
  case_nat~.
  destruct (classicT (0 = 0)).
  auto.
  tryfalse.
*)
Qed.

Example SR_3_10_test:
  rtyp ddot udot gdot 
       (call (retn (i_e (i_i 0))))
       cint.
Proof.
  auto.
  (* apply SR_3_10;
  auto.*)
Qed.

(* Bogus: can't instantiate anything but a universal type. 
Example SR_3_11_test_simpl:
  rtyp 
    ddot udot ((varx ~ cint) & gdot)
    (inst (p_e (fevar varx) nil)
          cint)
    cint.
Proof.
  apply SR_3_11 with (k:= B) (tau':= cint); auto. (* 20 runs way too many times. *)
  apply SR_3_1 with (tau':= cint).
  auto.
  admit.
  auto.
  auto.
Qed.
*)

Definition xzero := (i_e (i_i 0)).
Tactic Notation "pick_fresh" ident(x) "with" tactic(E) :=
  let L := gather_vars in pick_fresh_gen (L \u E) x.

Example p63_1:
  styp ddot udot gdot
       cint
       (letx (i_e (i_i 0)) (e_s (p_e (bevar 0) nil))).
Proof.
  apply_fresh_from styp_let_3_6 with fv_of_static_goal; auto.
  (* But I'm not really solving the undirected type issues. *)
Qed.

Ltac apply_fresh_base_simple_plus_tau' lemma gather plus tau'' :=
  let L0 := gather_vars_plus plus in
   let L := beautify_fset L0 in
     apply (@lemma L) with (tau':= tau'').
(*    first [apply (@lemma L) with (tau':= tau') | eapply (@lemma L)]. *)

Ltac apply_fresh_base_plus_tau' lemma gather plus var_name tau' :=
  apply_fresh_base_simple_plus_tau' lemma gather plus tau';
  try (match goal with
    | |- forall _:_, _ \notin _ -> _ => intros_fresh var_name
    | |- forall _:_, fresh _ _ _ -> _ => intros_fresh var_name
    end).

Tactic Notation "apply_fresh_from'" constr(T) "with" tactic3(X) "also" constr(tau') :=
 apply_fresh_base_plus_tau' T gather_vars_plus X ltac_no_arg tau'.

Example p63_2:
    styp ddot udot gdot
         (ptype cint)
         (letx (i_e (i_i 0))
               (letx (amp (p_e (bevar 1) nil)) (e_s (p_e (bevar 0) nil)))).
Proof.
  apply_fresh_from' styp_let_3_6 with (fv_of_static_goal) also cint;
    [simpl; case_nat; case_nat| auto | auto].
  apply_fresh_from' styp_let_3_6 with (fv_of_static_goal) also (ptype cint);
    [simpl; case_nat | auto | auto].
  auto.
Qed.

Example p63_3:
    styp ddot udot gdot
         (etype aliases B (cross (ptype (btvar 0)) (btvar 0)))
         (letx (i_e (i_i 0))
               (letx (amp (p_e (bevar 1) nil)) 
                     (letx (pack cint
                                 (cpair (amp (p_e (bevar 2) nil)) (p_e (bevar 2) nil))
                                 (etype aliases B (cross (ptype (btvar 0)) (btvar 0))))
                        (e_s (p_e (bevar 0) nil))))).
Proof.
  apply_fresh_from' styp_let_3_6 with (fv_of_static_goal) also cint;
    try simpl in Fry;
    [simpl; case_nat; case_nat; case_nat| auto | auto].
  apply_fresh_from' styp_let_3_6 with (fv_of_static_goal) also (ptype cint);
    [simpl; case_nat | auto | auto].
  apply_fresh_from' styp_let_3_6 with (fv_of_static_goal)
   also (etype aliases B (cross (ptype (btvar 0)) (btvar 0)));
   try simpl in Fry1;
   try simpl in Fry0;
   [simpl; case_nat| idtac | auto].
  constructor.
  apply SR_3_1 with (tau':= (etype aliases B (cross (ptype (btvar 0)) (btvar 0)))).
  simpl_env.
  constructor.
  auto.
  auto.
  simpl in Fry0.
  apply_fresh_from SR_3_12 with (fv_of_static_goal); auto.
Qed.
  
 (* How do I get this to repeat without looping. *)
 (* Or matching all of the structure in them. *)
(*
  | H: context[fv_heap(_)]    |- _ => simpl in H 
  | H: context[fv_state(_)]   |- _ => simpl in H
  | H: context[fv_delta(_)]   |- _ => simpl in H
  | H: context[fv_gamma(_)]   |- _ => simpl in H
  | H: context[fv_upsilon(_)] |- _ => simpl in H
*)



Ltac simpl_env :=
  match goal with 
  | |- context [get ?a ddot]           => rewrite~ get_empty
  | |- context [get ?a gdot]           => rewrite~ get_empty
  | |- context [get ?a hdot]           => rewrite~ get_empty
  | |- context [LVPE.V.get ?a udot]    => rewrite~ LVPE.get_empty

  | |- context [LVPE.V.get ?a (?a ~p _) ]      =>
    rewrite~ LVPE.get_single; try repeat case_var~; simpl_env
  | |- context [get ?a (?a ~ _) ]      =>
    rewrite~ get_single; try repeat case_var~; simpl_env

  | |- context [LVPE.V.get ?a (_ &p (?a ~p _)) ]      =>
    rewrite~ LVPE.get_push; try repeat case_var~; simpl_env
  | |- context [get ?a (_ & (?a ~ _)) ]      =>
    rewrite~ get_push; simpl_env; try repeat case_var~

  | |- context [LVPE.V.get ?a (_ &p (_ ~p _)) ]      =>
    rewrite~ LVPE.get_push; try repeat case_var~; simpl_env
  | |- context [get ?a (_ & (_ ~ _)) ]      =>
    rewrite~ get_push; try repeat case_var~; simpl_env

  | |- context [get ?a ((?b ~ _) & _)] =>
    rewrite~ get_concat; try repeat case_var~; simpl_env
  | |- context [LVPE.V.get ?a ((?b ~ _) & _)] =>
    rewrite~ LVPE.get_concat; try repeat case_var~; simpl_env

  | |- context [_ \u \{}] =>
    repeat rewrite union_empty_r; simpl_env
  | H: context [_ \u \{}] |- _ =>
    repeat rewrite union_empty_r in H; simpl_env

  | |- context [\{} \u _] =>
    repeat rewrite union_empty_l; simpl_env
  | H: context [\{} \u _] |- _ =>
    repeat rewrite union_empty_l in H; simpl_env

  | |- context [?a \u ?a] =>
    repeat rewrite union_same; simpl_env
  | H: context [?a \u ?a] |- _ =>
    repeat rewrite union_same in H; simpl_env

  | |- context [?a \u ?a] =>
    repeat rewrite union_same; simpl_env
  | H: context [?a \u ?a] |- _ =>
    repeat rewrite union_same in H; simpl_env

  | H: context[TM.fv_v(_)]  |- _ => simpl in H
  | H: context[TM.fv(_)]    |- _ => simpl in H
  | H: context[TM.fv_st(_)] |- _ => simpl in H
  | H: context[TM.fv_e(_)]  |- _ => simpl in H
  | H: context[TM.fv_f(_)]  |- _ => simpl in H

  | H: context[TTM.fv_v(_)]  |- _ => simpl in H
  | H: context[TTM.fv(_)]    |- _ => simpl in H
  | H: context[TTM.fv_st(_)] |- _ => simpl in H
  | H: context[TTM.fv_e(_)]  |- _ => simpl in H
  | H: context[TTM.fv_f(_)]  |- _ => simpl in H
                                             
  | H: context[T.fv(_)] |- _ => simpl in H
  end.


Example p63_4:
    styp ddot udot gdot
         (ptype (etype aliases B (cross (ptype (btvar 0)) (btvar 0))))
         (letx (i_e (i_i 0))
               (letx (amp (p_e (bevar 1) nil)) 
                     (letx (pack cint
                                 (cpair (amp (p_e (bevar 2) nil)) (p_e (bevar 2) nil))
                                 (etype aliases B (cross (ptype (btvar 0)) (btvar 0))))
                           (openstar (p_e (bevar 2) nil)
                                     (e_s (p_e (bevar 0) nil)))))).
Proof.
  apply_fresh_from' styp_let_3_6 with (fv_of_static_goal) also cint;
    try simpl_env;
    try simpl_env;
    [simpl; case_nat; case_nat; case_nat| auto | auto].
  apply_fresh_from' styp_let_3_6 with (fv_of_static_goal) also (ptype cint);
    try simpl_env;
    [simpl; case_nat | auto | auto].
  simpl_env.
  apply_fresh_from' styp_let_3_6 with (fv_of_static_goal)
   also (etype aliases B (cross (ptype (btvar 0)) (btvar 0)));
   try simpl in Fry1;
   try simpl in Fry0;
   [simpl; case_nat| idtac | auto].
  simpl.
  case_nat.
  simpl.
  case_nat.

  apply styp_openstar_3_8 with (L:=\{}) (k:=B) (tau':= (cross (ptype (btvar 0)) (btvar 0))).
  simpl.
  case_nat.
  intros.
  constructor.
  apply SR_3_1 with (tau':= (ptype (cross (ptype (ftvar alpha)) (ftvar alpha))));
  auto.
  admit.
  admit.
  admit.
  (* Way too hard, must automate. *)
  apply K_B_A.
  constructor.
  apply K_etype with (L:= \{}).
  simpl.
  case_nat.
  case_nat.
  intros.
  auto.
  apply SR_3_12 with (L:= \{}); auto.
Qed.

















Example SR_3_11_test:
  rtyp 
    ddot udot gdot
    (inst (f_e (ufun B (dfun (btvar 0) (btvar 0) (retn (p_e (bevar 0) nil)))))
          cint)
    (arrow cint cint).
Proof.
  apply SR_3_11 with
          (k := B)
            (tau':= (arrow (btvar 0) (btvar 0)));
    try solve[auto]; try solve[simpl; case_nat~].    
Qed.

Example simplest_pack:
  rtyp ddot udot ((varx ~ cint) & gdot)
        (pack cint (p_e (fevar varx) nil)
              (etype aliases B (btvar 0)))
        (etype aliases B (btvar 0)).
Proof.
 apply_fresh_from* SR_3_12 with fv_of_static_goal.
Qed.

Example pack_int:
  rtyp ddot udot ((varx ~ cint) & gdot)
        (pack cint (p_e (fevar varx) nil)
              (etype aliases B (btvar 0)))
        (etype aliases B (btvar 0)).
Proof.
 apply_fresh_from* SR_3_12 with fv_of_static_goal.
Qed.

Example pack_int_star:
  rtyp ddot udot ((varx ~ cint) & gdot)
        (pack (ptype cint) (amp (p_e (fevar varx) nil))
              (etype aliases B (ptype (btvar 0))))
        (etype aliases B (ptype (btvar 0))).
Proof.
 apply_fresh_from* SR_3_12 with fv_of_static_goal.
Qed.

Example pack_int_open:
  styp ddot udot ((varx ~ cint) & (vary ~ cint) & gdot)
        cint
        (openx (pack cint (p_e (fevar varx) nil) (etype aliases B (btvar 0)))
               (e_s (p_e (fevar vary) nil))).
Proof.
  apply styp_open_3_7
  with (L:=\{varx})
         (p:= aliases)
         (k:=B)
         (tau':= (btvar 0)).
  simpl.
  intros.
  case_nat.
  constructor.
  apply SR_3_1 with (tau':= cint).
  auto.
  auto.
  auto.
  admit.
  apply_fresh_from* SR_3_12 with fv_of_static_goal.
  simpl.
  auto.
  apply SR_3_1 with (tau':=cint).
  admit.
  constructor.
  auto.
  admit. (* WFC *)
  auto.
Qed.

Example let_pack_openstar:
  styp ddot udot ((varx ~ cint) & gdot) 
       cint 
  (letx (pack cint (p_e (fevar varx) nil) (etype aliases B (btvar 0)))
        (openstar (p_e (bevar 0) nil)
                  (e_s (assign (star (p_e (bevar 0) nil)) (i_e (i_i 7)))))).
Proof.
  apply styp_let_3_6 with
  (L:= (fv_delta ddot \u fv_upsilon udot) \u fv_gamma (varx ~ cint & gdot))
  (tau':= (etype aliases B (btvar 0))).
  (* apply_fresh_from styp_let_3_6 with fv_of_static_goal.*)
  intros.
  simpl.
  case_nat.
  case_nat.
  apply styp_openstar_3_8
  with (L:= \{varx} \u (fv_delta ddot \u fv_upsilon udot) \u fv_gamma (varx ~ cint & gdot))
         (k:= B)
         (tau':= cint).
  simpl.
  intros.
  case_nat.
  constructor.
  constructor.
  constructor.
  apply SR_3_1 with (tau':= (ptype cint)).
  simpl_env.
admit.
  admit.
  constructor.
  admit.
  constructor.
  constructor.
  constructor.
  admit.
  apply_fresh_from SR_3_12 with fv_of_static_goal.
  simpl.
  apply SR_3_1 with (tau':= cint).
  simpl_env.
  constructor.
  constructor.
  constructor.
  auto.
  auto.
  auto.
Qed.












































Example pack_int_openstar:
  styp ddot udot ((varx ~ cint) & gdot)
       (ptype cint)
       (openstar (pack cint (p_e (fevar varx) nil)
                       (etype aliases B (btvar 0)))
                 (e_s (p_e (fevar varx) nil))).
Proof.
  apply styp_openstar_3_8
  with (L:=\{varx})
         (k:=B)
         (tau':= (btvar 0)).
  simpl.
  intros.
  case_nat.
  constructor.
  apply SR_3_1 with (tau':= (ptype cint)).
  admit.
  auto.
  auto.
  admit. (* WFC won't solve but should be good. *)
  
  constructor.
  auto.
  admit.
  apply_fresh_from* SR_3_12 with fv_of_static_goal.  
  auto.
Qed.


(* Thesis example munged. Pg 62 line 3. 
Definition E_62_3 :=
           (pack (ptype cint) (cpair (amp (p_e (fevar varx) nil)) (p_e (fevar varx) nil))
                 (etype aliases B (cross (ptype (btvar 0)) (btvar 0)))).
Example SR_3_12_test:
  rtyp ddot udot ((varx ~ cint) & gdot)
    (pack (ptype (cross (ptype cint) cint))
          (cpair (amp (p_e (fevar varx) nil)) (p_e (fevar varx) nil))
          (etype aliases B (ptype (cross (ptype (btvar 0)) (btvar 0)))))
    (etype aliases B (ptype (cross (ptype (btvar 0)) (btvar 0)))).
Proof.
  apply_fresh_from* SR_3_12 with fv_of_static_goal.
  simpl.
  
Qed.


Example SR_3_12_test:
  rtyp ddot udot gdot
       (pack ((cross cint cint) (cpair (i_e (i_i 0)) (i_e (i_i 1))) 
             (etype aliases A (ptype (cross (btvar 0) (btvar 0)))))
       (etype aliases A (ptype (cross (btvar 0) (btvar 0)))).
Proof.
  apply_fresh_from SR_3_12 with fv_of_static_goal.
  simpl in Fry.
  simpl.
  auto.
  apply_fresh_from K_etype with fv_of_kinding_goal.
  intros.
  simpl.
  case_nat.
  apply K_B_A.
  apply K_ptype.
  apply K_cross.
  apply K_B_A.
  auto.
Qed.
*)


Example SR_3_13_test:
  rtyp ddot udot gdot 
       (f_e (dfun cint cint (retn (i_e (i_i 0)))))
       (arrow cint cint).
Proof.
  auto.
(*  apply SR_3_13; *)
Qed.

Example SR_3_14_test:
  rtyp ddot udot gdot 
       (f_e (ufun B (dfun (btvar 0) (btvar 0) (retn (p_e (bevar 0) nil)))))
       (utype B (arrow (btvar 0) (btvar 0))).
Proof.
  auto.
  (* apply_fresh_from* SR_3_14 with fv_of_static_goal. *)
Qed.

(* Test htyp. *)
Example htyp_empty_test:
  htyp udot gdot hdot gdot.
Proof.
  apply htyp_empty;
  auto.
Qed.

(* Question: we are at the H & (x~v) & H' match issue. *)
Example htyp_xv_test:
  htyp udot gdot (hdot & (varx ~ v) & hdot) (gdot & (varx ~ tau) & gdot).
Proof.
  unfold_test_utilities.
  (* loss of syntax direction here but we don't mind really as eauto is working. *)
  (* auto. *)
  eapply htyp_xv with (g':= gdot);
  auto.
  (* Bug needs hdot & hdot = hdot. *)
Admitted.

(* Test refp. *)

Example refp_empty_test:
  refp h udot.
Proof.
  auto.
  (* apply refp_empty. *)
Qed.

(* BUG
Example refp_pack_test:
  refp [(x,
         pack (cross cint cint) 
              (cpair (i_e (i_i 0)) (i_e (i_i 0))) 
              (etype aliases alpha A (cross cint cint)))]
       ([((x, [u_pe]), (cross cint cint))] ++ nil).
Proof.
  constructor.
  auto.
  apply refp_pack with 
  (k     := A) 
  (v     := (cpair (i_e (i_i 0)) (i_e (i_i 0))))
  (v'    := pack (cross cint cint) 
                 (cpair (i_e (i_i 0)) (i_e (i_i 0))) 
                 (etype aliases alpha A (cross cint cint)))
  (tau   := (cross cint cint))
  (alpha := alpha);
  auto.
  constructor.
  constructor.
  constructor.
  constructor.
  constructor.
   (* Bug, after get(v,nil,v) fix. *)
Admitted.
*)

(* Test prog. *)

Example program_test:
  prog hdot (retn (i_e (i_i 0))).
Proof.
  auto.
  apply program with (u:= udot) (g:= gdot) (tau:=cint);
  auto.
Qed.
