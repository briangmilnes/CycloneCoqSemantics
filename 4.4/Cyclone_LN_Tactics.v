(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION", Daniel Grossman, August 2003 *)
(* Tactics for LN *)
(* Brian Milnes 2016 *)

Set Implicit Arguments.
Require Export TLC.LibNat TLC.LibVar TLC.LibTactics.
Require Export Cyclone_LN_FSET Cyclone_LN_Terms Cyclone_LN_Types Cyclone_LN_Types_In_Terms Cyclone_LN_Env.
Require Export Cyclone_Static_Semantics.
Close Scope list_scope.
Import LibEnvNotations.
Import LVPE.LibVarPathEnvNotations.


(** Tactics for comparison of indices *)

Hint Extern 1 (_ < _) => nat_math.
Hint Extern 1 (_ <= _) => nat_math.


(* Modules seems to mess with Auto's definitions. *)
Hint Extern 1 (lt _ _) => nat_math.
Hint Extern 1 (le _ _ ) => nat_math.


(* Tactics for variables. *)

(* Tactics for building L, our finite set for cofinite induction. *)

Ltac gather_vars :=
  let A' := gather_vars_with (fun x : vars => x) in
  let B' := gather_vars_with (fun x : var  => \{x}) in
  let C' := gather_vars_with (fun x : Tau => T.fv x) in
  let D' := gather_vars_with (fun x : V => TM.fv_v x) in
  let E' := gather_vars_with (fun x : St => TM.fv_st x) in
  let F' := gather_vars_with (fun x : E => TM.fv_e x) in
  let G' := gather_vars_with (fun x : F => TM.fv_f x) in  
  let H' := gather_vars_with (fun x : Term => TM.fv x) in
  let I' := gather_vars_with (fun x : St => TTM.fv_st x) in
  let J' := gather_vars_with (fun x : E => TTM.fv_e x) in
  let K' := gather_vars_with (fun x : F => TTM.fv_f x) in
  let L' := gather_vars_with (fun x : Term => TTM.fv x) in
  let M' := gather_vars_with (fun x : Heap  => fv_heap x) in
  let N' := gather_vars_with (fun x : State => fv_state x) in
  let O' := gather_vars_with (fun x : Delta => fv_delta x) in
  let P' := gather_vars_with (fun x : Gamma => fv_gamma x) in 
  let Q' := gather_vars_with (fun x : Upsilon => fv_upsilon x) in 
  let R' := constr:((A' \u B' \u C' \u D' \u E' \u F' \u G' \u H' \u I' \u J'
                        \u K' \u L' \u M' \u N' \u O' \u P' \u Q'))
  in beautify_fset R'.


Ltac pick_fresh X :=
  let L := gather_vars in (pick_fresh_gen L X).

Tactic Notation "pick_fresh" ident(x) :=
  let L := gather_vars in pick_fresh_gen (L) x.

Tactic Notation "pick_fresh" ident(x) "from" constr(E) :=
  let L := gather_vars in pick_fresh_gen (L \u E) x.

Tactic Notation "apply_fresh" constr(T) :=
  apply_fresh_base T gather_vars ltac_no_arg.

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; auto_star.

Tactic Notation "apply_fresh" "*" constr(T) :=
  apply_fresh T; auto_star.

Tactic Notation "exists_fresh" :=
  let y := fresh "y" in let Fry := fresh "Fr" y in
  exists_fresh_gen gather_vars y Fry.

Tactic Notation "pick_fresh" ident(x) "with" tactic(E) :=
  let L := gather_vars in pick_fresh_gen (L \u E) x.

(* ********************************************************************** *)
(** Tactics *)

(** [inst_notin H y as H'] expects [H] to be of the form
  [forall x, x \notin L, P x] and creates an hypothesis [H']
  of type [P y]. It tries to prove the subgoal [y \notin L]
  by [auto]. This tactic is very useful to apply induction
  hypotheses given in the cases with binders. *)

Tactic Notation "inst_notin" constr(lemma) constr(var)
                "as" ident(hyp_name) :=
  let go L := let Fr := fresh in assert (Fr : var \notin L);
     [ notin_solve | lets hyp_name: (@lemma var Fr); clear Fr ] in
  match type of lemma with
    forall _, _ \notin ?L -> _ => go L end.

Tactic Notation "inst_notin" "~" constr(lemma) constr(var)
                "as" ident(hyp_name) :=
  inst_notin lemma var as hyp_name; auto_tilde.

Tactic Notation "inst_notin" "*" constr(lemma) constr(var)
                "as" ident(hyp_name) :=
  inst_notin lemma var as hyp_name; auto_star.

(* To reduce naming and make the proofs more robust, sometimes you want to
  invert on the constructor equalities or lc terms in the context. *)

Ltac inversion_on_equated_constructors :=
  match goal with
    | H: (?C _) = (?C _) |- _ => inversion H
    | H: (?C _ _) = (?C _ _) |- _ => inversion H
    | H: (?C _ _ _) = (?C _ _ _) |- _ => inversion H
  end.

Hint Resolve subset_union_weak_l subset_union_weak_r subset_refl
  subset_union_2 subset_union_2p subset_empty_l 
  subset_remove_2p subset_remove_11 : fset.

(* Too slow, bug in rewrite says Arthur.
Ltac simpl_get :=
  auto;
  autounfold;
  autorewrite with env_defs;
  intros;
  auto;
  try unfold get_impl;
  try unfold LVPE.V.get_impl;
  simpl.
*)

(* Again with variables collected from goals. *)

Ltac gather_vars_plus T :=
  let A' := gather_vars_with (fun x : vars => x) in
  let B' := gather_vars_with (fun x : var  => \{x}) in
  let C' := gather_vars_with (fun x : Tau => T.fv x) in
  let D' := gather_vars_with (fun x : V => TM.fv_v x) in
  let E' := gather_vars_with (fun x : St => TM.fv_st x) in
  let F' := gather_vars_with (fun x : E => TM.fv_e x) in
  let G' := gather_vars_with (fun x : F => TM.fv_f x) in  
  let H' := gather_vars_with (fun x : Term => TM.fv x) in
  let I' := gather_vars_with (fun x : St => TTM.fv_st x) in
  let J' := gather_vars_with (fun x : E => TTM.fv_e x) in
  let K' := gather_vars_with (fun x : F => TTM.fv_f x) in
  let L' := gather_vars_with (fun x : Term => TTM.fv x) in
  let M' := gather_vars_with (fun x : Heap  => fv_heap x) in
  let N' := gather_vars_with (fun x : State => fv_state x) in
  let O' := gather_vars_with (fun x : Delta => fv_delta x) in
  let P' := gather_vars_with (fun x : Gamma => fv_gamma x) in 
  let Q' := gather_vars_with (fun x : Upsilon => fv_upsilon x) in 
  let S' := T in
  let R' := constr:((A' \u B' \u C' \u D' \u E' \u F' \u G' \u H' \u I' \u J'
                        \u K' \u L' \u M' \u N' \u O' \u P' \u Q' \u S')) in
  beautify_fset R'.


Ltac apply_fresh_base_simple_plus lemma gather plus :=
  let L0 := gather_vars_plus plus in let L := beautify_fset L0 in
  first [apply (@lemma L) | eapply (@lemma L)].

Ltac apply_fresh_base_plus lemma gather plus var_name :=
  apply_fresh_base_simple_plus lemma gather plus;
  try (match goal with
    | |- forall _:_, _ \notin _ -> _ => intros_fresh var_name
    | |- forall _:_, fresh _ _ _ -> _ => intros_fresh var_name
    end).

Tactic Notation "apply_fresh_from" constr(T) "with" tactic3(X) :=
  apply_fresh_base_plus T gather_vars_plus X ltac_no_arg .

Tactic Notation "apply_fresh_from*" constr(T) "with" tactic3(X) :=
  apply_fresh_from T with X; auto.

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

(* Turn on and off tracing with these four Ltacs. *)

Ltac trace_goal :=
  idtac.
(*
  match goal with
  | |- ?g => idtac g
  end.
*)

Ltac simpl_open_rec :=
  timeout 2 
   repeat match goal with 
  | |- Some ?b = Some ?b       =>
    (*idtac "Some b = Some b";*) trace_goal; reflexivity
  | |- context [(TM.open_rec_st _ _ _)]      => trace_goal;
 try simpl
    | H: context [(TM.open_rec_st _ _ _)] |- _ => trace_goal;
 try simpl in H

    | |- context [(T.open_rec _ _ _)]      => trace_goal;
 try simpl
    | H: context [(T.open_rec _ _ _)] |- _ => trace_goal;
 try simpl in H
    | |- context [(TTM.open_rec_f _ _ _)]      => trace_goal;
 try simpl
    | H: context [(TTM.open_rec_f _ _ _)] |- _ => trace_goal;
 try simpl in H
    | |- context [(TTM.open_rec_st _ _ _)]      => trace_goal;
 try simpl
    | H: context [(TTM.open_rec_st _ _ _)] |- _ => trace_goal;
 try simpl in H
end.
  
Ltac simpl_get :=
  timeout 2
  repeat
    match goal with
  | |- context [get ?a ddot]           => trace_goal;
 rewrite~ get_empty
  | |- context [get ?a gdot]           => trace_goal;
 rewrite~ get_empty
  | |- context [get ?a hdot]           => trace_goal;
 rewrite~ get_empty
  | |- context [get ?a (_ & (_ ~ _)) ]      => trace_goal;
    rewrite~ get_push; try repeat case_var~

  | |- context [get ?a ((?b ~ _) & _)] => trace_goal;
    rewrite~ get_concat; try repeat case_var~

end.

Ltac simpl_lvpe_get :=
  timeout 2
  repeat
    match goal with 
    | |- context [LVPE.V.get ?a udot]    => trace_goal;
      rewrite~ LVPE.get_empty

  | |- context [LVPE.V.get ?a (?a ~p _) ]      => trace_goal;
    rewrite~ LVPE.get_single; try repeat case_var~
  | |- context [get ?a (?a ~ _) ]      => trace_goal;
    rewrite~ get_single; try repeat case_var~

  | |- context [LVPE.V.get ?a (_ &p (?a ~p _)) ]      => trace_goal;
    rewrite~ LVPE.get_push; try repeat case_var~
  | |- context [get ?a (_ & (?a ~ _)) ]      => trace_goal;
    rewrite~ get_push; try repeat case_var~

  | |- context [LVPE.V.get ?a (_ &p (_ ~p _)) ]      => trace_goal;
    rewrite~ LVPE.get_push; try repeat case_var~
  | |- context [LVPE.V.get ?a ((?b ~ _) & _)] => trace_goal;
    rewrite~ LVPE.get_concat; try repeat case_var~
end.

Ltac simpl_union :=
  timeout 2
  repeat
    match goal with 
    | |- context [_ \u \{}] => trace_goal;
    repeat rewrite union_empty_r

    | H: context [_ \u \{}] |- _ => trace_goal;
    repeat rewrite union_empty_r in H

    | |- context [\{} \u _] => trace_goal;
    repeat rewrite union_empty_l

    | H: context [\{} \u _] |- _ => trace_goal;
      repeat rewrite union_empty_l in H
    | |- context [?a \u ?a] => trace_goal;
    repeat rewrite union_same

  | H: context [?a \u ?a] |- _ => trace_goal;
    repeat rewrite union_same in H
  | |- context [?a \u ?a] => trace_goal;
    repeat rewrite union_same
end.

Ltac simpl_fv :=
  timeout 2
     repeat
     match goal with 
     (* Need better pattern matching. *)
     (* 1, 2 argument constructors for V.*)
     | H: context[TM.fv_v((_ _))]  |- _ => trace_goal;
                                           simpl in H
                                                      
     (* 1,2,3 argument constructors for terms.  *)
     | H: context[TM.fv((_ _))]    |- _ => trace_goal;
                                           simpl in H
     | H: context[TM.fv((_ _ _))]    |- _ => trace_goal;
                                             simpl in H
     | H: context[TM.fv((_ _ _ _))]    |- _ => trace_goal; simpl in H
                                                                      
     (* 1,2 argument constructors for st.  *)
     | H: context[TM.fv_st((_ _))] |- _ => trace_goal;
                                           simpl in H
     | H: context[TM.fv_st((_ _ _))] |- _ => trace_goal;
                                             simpl in H
                                                        
     (* 1, 2, 3 argument constructors for e. *)
     | H: context[TM.fv_e((_ _))]  |- _ => trace_goal;
                                           simpl in H
     | H: context[TM.fv_e((_ _ _))]  |- _ => trace_goal;
                                             simpl in H
     | H: context[TM.fv_e((_ _ _ _)_)]  |- _ => trace_goal;
                                                simpl in H
                                                           
     (* 1,2 argument constructors for F. *)                                                
     | H: context[TM.fv_f((_ _ _))]  |- _ => trace_goal;
                                             simpl in H
     | H: context[TM.fv_f((_ _))]  |- _ => trace_goal;
                                           simpl in H
                                                      
     (* 1, 2 argument constructors for V.*)
     | H: context[TTM.fv_v((_ _))]  |- _ => trace_goal;
                                            simpl in H
                                                       
     (* 1,2,3 argument constructors for terms.  *)
     | H: context[TTM.fv((_ _))]    |- _ => trace_goal;
                                            simpl in H
     | H: context[TTM.fv((_ _ _))]    |- _ => trace_goal;
                                              simpl in H
     | H: context[TTM.fv((_ _ _ _))]    |- _ => trace_goal;
                                                simpl in H
                                                           
     (* 1,2 argument constructors for st.  *)
     | H: context[TTM.fv_st((_ _))] |- _ => trace_goal;
                                            simpl in H
     | H: context[TTM.fv_st((_ _ _))] |- _ => trace_goal;
                                              simpl in H
                                                         
     (* 1, 2, 3 argument constructors for e. *)
     | H: context[TTM.fv_e((_ _))]  |- _ => trace_goal;
                                            simpl in H
     | H: context[TTM.fv_e((_ _ _))]  |- _ => trace_goal;
                                              simpl in H
     | H: context[TTM.fv_e((_ _ _ _))]  |- _ => trace_goal;
                                                simpl in H
                                                           
     (* 1,2 argument constructors for F. *)                                                
     | H: context[TTM.fv_f((_ _ _))]  |- _ => trace_goal;
                                              simpl in H
     | H: context[TTM.fv_f((_ _ ))]  |- _ => trace_goal;
                                             simpl in H
                                                        
     (* 1,2,3 argument constructors for types. *)
     | H: context[T.fv((_ _))] |- _ => trace_goal;
                                       simpl in H
     | H: context[T.fv((_ _ _))] |- _ => trace_goal;
                                         simpl in H
     | H: context[T.fv((_ _ _))] |- _ => trace_goal;
                                         simpl in H
end.
                                                    
Ltac simpl_contexts :=
  timeout 2
  repeat
    match goal with
    | H: context[(fv_heap hdot)] |- _ => trace_goal;
             rewrite fv_heap_empty in H
    | |- context[(fv_heap hdot)] => trace_goal;
                                    rewrite fv_heap_empty
                                            
    | H: context[(fv_delta ddot)] |- _ => trace_goal;
                                          rewrite fv_delta_empty in H
    | |- context[(fv_delta ddot)] => trace_goal;
                                     rewrite fv_delta_empty
                                             
    | H: context[(fv_gamma gdot)] |- _ => trace_goal;
                                          rewrite fv_gamma_empty in H
    | |- context[(fv_gamma gdot)] => trace_goal;
                                     rewrite fv_gamma_empty
                                             
    | H: context[(fv_upsilon udot)] |- _ => trace_goal;
                                            rewrite fv_upsilon_empty in H
    | |- context[(fv_upsilon udot)] => trace_goal;
                                       rewrite fv_upsilon_empty
                                               
    | H: context[(fv_gamma ((_ ~ _)))] |- _ => trace_goal;
     rewrite fv_gamma_single in H; try repeat case_var~
    | |- context[(fv_gamma ((_ ~ _))) ] => trace_goal;
     rewrite fv_gamma_single; try repeat case_var~

    | H: context[(fv_gamma (_ & (_ ~ _)))] |- _ => trace_goal;
     rewrite fv_gamma_push in H; try repeat case_var~
    | |- context[(fv_gamma (_ & (_ ~ _)))] => trace_goal;
     rewrite fv_gamma_push; try repeat case_var~

    | H: context[(fv_gamma (_ & _))] |- _ => trace_goal;
     rewrite fv_gamma_concat in H; try repeat case_var~
    | |- context[(fv_gamma (_ & _))] => trace_goal;
    rewrite fv_gamma_concat; try repeat case_var~

    | H: context[(fv_heap ((_ ~ _)))] |- _ => trace_goal;
     rewrite fv_heap_single in H; try repeat case_var~
    | |- context[(fv_heap ((_ ~ _))) ] => trace_goal;
     rewrite fv_heap_single; try repeat case_var~

    | H: context[(fv_heap (_ & (_ ~ _)))] |- _ => trace_goal;
     rewrite fv_heap_push in H; try repeat case_var~
    | |- context[(fv_heap (_ & (_ ~ _)))] => trace_goal;
     rewrite fv_heap_push; try repeat case_var~

    | H: context[(fv_heap (_ & _))] |- _ => trace_goal;
     rewrite fv_heap_concat in H; try repeat case_var~
    | |- context[(fv_heap (_ & _))] => trace_goal;
     rewrite fv_heap_concat; try repeat case_var~

    | H: context[(fv_delta ((_ ~ _)))] |- _ => trace_goal;
     rewrite fv_delta_single in H; try repeat case_var~
    | |- context[(fv_delta ((_ ~ _))) ] => trace_goal;
     rewrite fv_delta_single; try repeat case_var~

    | H: context[(fv_delta (_ & (_ ~ _)))] |- _ => trace_goal;
     rewrite fv_delta_push in H; try repeat case_var~
    | |- context[(fv_delta (_ & (_ ~ _)))] => trace_goal;
     rewrite fv_delta_push; try repeat case_var~

    | H: context[(fv_delta (_ & _))] |- _ => trace_goal;
     rewrite fv_delta_concat in H; try repeat case_var~
    | |- context[(fv_delta (_ & _))] => trace_goal;
     rewrite fv_delta_concat; try repeat case_var~                                                                     
    | H: context[(fv_upsilon ((_ ~ _)))] |- _ => trace_goal;
     rewrite fv_upsilon_single in H; try repeat case_var~
    | |- context[(fv_upsilon ((_ ~ _))) ] => trace_goal;
     rewrite fv_upsilon_single; try repeat case_var~

    | H: context[(fv_upsilon (_ & (_ ~ _)))] |- _ => trace_goal;
     rewrite fv_upsilon_push in H; try repeat case_var~
    | |- context[(fv_upsilon (_ & (_ ~ _)))] => trace_goal;
     rewrite fv_upsilon_push; try repeat case_var~

    | H: context[(fv_upsilon (_ & _))] |- _ => trace_goal;
     rewrite fv_upsilon_concat in H; try repeat case_varpath~; try repeat case_var~
    | |- context[(fv_upsilon (_ & _))] => trace_goal;
     rewrite fv_upsilon_concat; try repeat case_varpath~; try repeat case_var~
end.

Ltac simpl_if :=
  timeout 2
  repeat
    match goal with
    (* If last so I simplify all of its subterms. *)
    | |- context [If (_ = _) then _ else _]       => trace_goal;
         try repeat case_nat; try repeat case_var; try repeat case_varpath
    | H: context [If (_ = _) then _ else _] |- _  => trace_goal;
     try repeat case_nat; try repeat case_var; try repeat case_varpath
    end.

Ltac simpl_env := 
  timeout 2
  ((*idtac simpl_env;*)
    repeat 
      (try simpl_open_rec;
       try simpl_get; 
       try simpl_lvpe_get;
       try simpl_union;
       try simpl_fv;
       try simpl_contexts;
       try simpl_if)).
      
(*
      first [try simpl_get |
             try simpl_lvpe_get |
             try simpl_union |
             try simpl_fv |
             try simpl_contexts |
             try simpl_if]).
*)

Hint Extern 4 (get _ _ = _) => simpl_env.
Hint Extern 4 (LVPE.V.get _ _ = _) => simpl_env.

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

Ltac simpl_K :=
  timeout 2
  ((*idtac "simpl_K";*) 
   repeat match goal with
  | |- Some ?b = Some ?b       =>
    (*idtac "Some ?b Some ?b";*) trace_goal; reflexivity

  | |- K _ cint A              =>
    (*idtac "K _ cint A";*) trace_goal; apply K_B_A; apply K_cint

  | |- K _ cint B              =>
    (*idtac "K _ cint B";*) trace_goal; apply K_cint

  | |- K _ (ftvar _) B         =>
    (*idtac "K _ (ftvar _) B";*) trace_goal; apply K_B; try simpl_env

  | |- K _ (ftvar _) A         =>
    (*idtac "K _ (ftvar _) B";*) trace_goal; apply K_B_A; try simpl_env

  | |- K _ (ptype _) A         =>
    (*idtac "K _ (ptype _) A";*) trace_goal; apply K_B_A; apply K_ptype

  | |- K _ (ptype (ftvar _)) B =>
    (*idtac "K _ (ptype (ftvar _)) B";*) trace_goal; apply K_star_A; try simpl_env

  | |- K _ (ptype _) B         =>
    (*idtac "K _ (ptype _) B";*) trace_goal; apply K_ptype

  | |- K _ (cross _ _) A       =>
    (*idtac "K _ (cross _ _) A";*) trace_goal; apply K_cross

  | |- K _ (arrow _ _) A       =>
    (*idtac "K _ (arrow _ _) A";*) trace_goal; apply K_arrow

  | |- K _ (utype _ _) _ => 
     (*idtac "K _ (utype _ _) _";*) trace_goal;
     apply_fresh_from K_utype with fv_of_kinding_goal;
     simpl; intros; try case_nat

  | |- K _ (etype _ _ _) _  =>
     (*idtac "K _ (etype _ _ ?tau) _";*) trace_goal;
       apply_fresh_from K_etype with fv_of_kinding_goal;
     simpl; intros; try case_nat
end).
Hint Extern 5 (K _ _ _) => 
(*idtac "simpl_K_extern";*) trace_goal; try solve[simpl_K]. 


Hint Extern 6 (styp _ _ _ _ (letx _ _))          
	=> (*idtac "1";*) apply_fresh_from* styp_let_3_6 with fv_of_static_goal.
Hint Extern 6 (styp _ _ _ _ (openx _ _))         
	=> (*idtac "2";*) apply_fresh_from* styp_open_3_7 with fv_of_static_goal.
Hint Extern 6 (styp _ _ _ _ (openstar _ _))      
	=> (*idtac "3";*) apply_fresh_from* styp_openstar_3_8 with fv_of_static_goal.
Hint Extern 6 (rtyp _ _ _ (pack _ _ _) _)       
	=> (*idtac "4";*) apply_fresh_from* SR_3_12 with fv_of_static_goal.
Hint Extern 6 (rtyp _ _ _ (f_e (ufun _ _)) _)    
	=> (*idtac "5";*) apply_fresh_from* SR_3_14 with fv_of_static_goal.
Hint Extern 6 (rtyp _ _ _ (f_e (dfun _ _ _ )) _) 
	=> (*idtac "6";*) apply_fresh_from* SR_3_13 with fv_of_static_goal.

Hint Extern 6 (styp _ _ _ _ (TM.open_rec_st _ _ _)) =>
 (*idtac "7";*) simpls~; try case_nat~;try case_nat~.
Hint Extern 6 (rtyp _ _ _ _ (T.open_rec _ _ _))     =>
 (*idtac "8";*) simpls~; try case_nat~; try case_nat~.
Hint Extern 6 (rtyp _ _ _ (TTM.open_rec_f _ _ _) _) =>
 (*idtac "9";*) simpls~; try case_nat~; try case_nat~.
Hint Extern 6 (rtyp _ _ _ (f_e (TTM.open_rec_f _ _ _)) _) =>
 (*idtac "10";*)  simpl; try case_nat~; try case_nat~.
Hint Extern 6 (styp _ _ _ _ (TM.open_rec_st _ _ _)) =>
 (*idtac "11";*) simpls~; try case_nat~; try case_nat~.

Hint Extern 4 (ltyp _ _ _ (p_e _ _) _) =>
 (*idtac "12";*) applys~ SL_3_1.
Hint Extern 4 (rtyp ?a ?b ?c (p_e ?d ?e) ?f) =>
 (*idtac "13 a b c d e f";*) applys~ SR_3_1.
Hint Extern 4 (ltyp _ _ _  (dot (p_e _ _) zero_pe) _) =>
 (*idtac "14";*) applys~ SL_3_3.
Hint Extern 4 (ltyp _ _ _ (dot (p_e _ _) one_pe)  _)  =>
 (*idtac "15";*) applys~ SL_3_4.
Hint Extern 4 (rtyp _ _ _ (dot _ zero_pe) _)          =>
 (*idtac "16";*) applys~ SR_3_3.
Hint Extern 4 (rtyp _ _ _ (dot _ one_pe)  _)          =>
 (*idtac "17";*) applys~ SR_3_4.
Hint Extern 4 (styp _ _ _ _ (e_s _))                  =>
 (*idtac "18";*) applys~ styp_e_3_1.
Hint Extern 6 (rtyp _ _ _ (appl _ _) _)               =>
 (*idtac "19";*) applys~ SR_3_9.

Hint Extern 6 (ASGN ?d (utype _ ?tau))   =>
(*idtac "22";*) apply_fresh_from ASGN_utype with fv_of_kinding_goal;
  try simpl; try case_nat~.
Hint Extern 6 (ASGN ?d (etype _ _ ?tau)) =>
(*idtac "23";*) apply_fresh_from ASGN_etype with fv_of_kinding_goal;
  try simpl; try case_nat~.
Hint Extern 6 (WFU _) =>
 (*idtac "24";*) constructor~; simpl_env.

(* Some missing notations from LibTactics. *)
Tactic Notation "destruct" "*" constr(T) :=
  destruct T; auto_star.

Tactic Notation "apply" "*" constr(L) "with" simple_intropattern(P) :=
  apply L with P; auto_star.

(* To get our expansion without a lot of extra tactics. *)
Tactic Notation "intros" "*" :=
  auto_star; intros; auto_star.

(* Get rid of an annoying notin case. *)
Ltac invert_x_notin_x :=
  match goal with
    | H: ?x \notin \{ ?x } |- _ => 
      apply notin_singleton_r in H; tryfalse
  end.


