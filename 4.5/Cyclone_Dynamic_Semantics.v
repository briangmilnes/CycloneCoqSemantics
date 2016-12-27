(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION".   Daniel Grossman, August 2003 *)
(* Definitions from Section 3.5.1 *)
(* Brian Milnes 2016 *)

Set Implicit Arguments.
Require Export Cyclone_Formal_Syntax Cyclone_LN_Types_In_Terms Cyclone_Dynamic_Semantics_Heap_Objects.
Require List.
Close Scope list_scope.
Import LibEnvNotations.

(* Question: is abstract heap overloading OK? 
   Adding to the left as the get takes the first one, will it break induction? *)

Inductive S : Heap -> St -> Heap -> St -> Prop :=
 | S_let_3_1 : forall (x : var) (v : E) (h : Heap) (s: St),
                 Value v ->
                 get x h = None -> 
                 S h (letx v s) ((single x v) & h) (TM.open_rec_st 0 x s)

 | S_seq_3_2 : forall (v : E) (h : Heap) (s: St),
                  Value v ->
                  S h (seqx (e_s v) s) h s

 | S_return_3_3: forall (v : E) (h : Heap) (s: St),
                    Value v ->
                    S h (seqx (retn v) s) h (retn v)

 | S_if0_3_4: forall (h : Heap) (s1 s2: St),
                 S h (if_s (i_e (i_i 0)) s1 s2)
                   h s1

 | S_if_ne_0_3_5: forall (h : Heap) (z : nat) (s1 s2: St),
                     z <> 0 ->                                  
                     S h (if_s (i_e (i_i z)) s1 s2)
                       h s2

 | S_while_3_6: forall (h : Heap) (e : E) (s : St),
                     S h (while e s)
                       h (if_s e (seqx s (while e s)) (e_s (i_e (i_i 0))))

 | S_open_3_7:  forall (tau tau' : Tau) (v : E) (p : Phi) (k : Kappa)
                       (h : Heap) (s : St),
                  Value v ->
                  S h (openx (pack tau' v (etype p k tau)) s)
                    h (letx v (TTM.open_rec_st 0 tau' s))

 | S_openstar_3_8: forall (tau tau' : Tau) (v v' : E) (x : var) (q : Phi) (k : Kappa)
                          (h : Heap) (s : St) (p : Path),
                    Value v ->
                    get x h = Some v' -> 
                    get' v' p (pack tau' v (etype q k tau)) ->
                    (* S is part of the context not the heap, overloading ; in DS3.8 *)
                    (* x' is right, openstar uses *x' but I am eliding it in the syntax. *)
                    S h (openstar (p_e (fevar x) p) s)
                      h (letx  (amp (p_e (fevar x) (app p (cons u_pe nil)))) 
                                     (TTM.open_rec_st 0 tau s))

| S_exp_3_9_1: forall (h h' : Heap) (e e' : E),
                   R h (e_s e) h' (e_s e') ->
                   S h (e_s e) h' (e_s e')

| S_ret_3_9_2: forall (h h' : Heap) (e e' : E),
                   R h (e_s e) h' (e_s e') ->
                   S h (retn e) h' (retn e')

| S_if_3_9_3: forall (h h' : Heap) (e e' : E) (s1 s2 : St),
                   R h (e_s e) h' (e_s e') ->
                   S h (if_s e s1 s2) h' (if_s e' s1 s2)

| S_letx_3_9_4: forall (h h' : Heap) (e e' : E) (s : St),
                   R h (e_s e) h' (e_s e') ->
                   S h (letx e s) h' (letx e' s)

| S_open_3_9_5: forall (h h' : Heap) (e e' : E) (s : St),
                   R h (e_s e) h' (e_s e') ->
                   S h  (openx e  s)
                     h' (openx e' s)

| S_seq_3_10:  forall (h h' : Heap) (s s' s2: St),
                    S h s h' s' ->
                    S h (seqx s  s2) h' (seqx s' s2)

| S_openstar_3_11: forall (h h' : Heap) (e e' : E) (s : St),
                        L h  (e_s e) h' (e_s e') ->
                        S h  (openstar e  s)
                          h' (openstar e' s)
with R : Heap -> St -> Heap -> St -> Prop :=
 | R_get_3_1 : forall (h  : Heap) (x : var) (p : Path) (v v' : E),
                    get x h = Some v' ->
                    get' v' p v ->
                    Value v ->
                    Value v' ->
                    R h (e_s (p_e (fevar x) p))
                      h (e_s v)
 | R_assign_3_2:
     forall (h : Heap) (v v' v'' : E) (x : var) (p : Path),
       get x h = Some v' -> 
       set' v' p v v'' ->
       Value v   ->
       Value v'  ->
       Value v'' ->
       R h  (e_s (assign (p_e (fevar x) p) v))
         (h & (single x v'')) (e_s v)

 | R_initial_assign_3_2:
     forall (h : Heap) (v : E) (x : var),
       get x h = None ->
       Value v   ->
       R h  (e_s (assign (p_e (fevar x) nil) v))
         (h & (single x v)) (e_s v)

 | R_star_amp_3_3:  
                 forall (h : Heap) (v : var) (p : Path),
                   R h (e_s (star (amp (p_e (fevar v)  p))))
                     h (e_s (p_e (fevar v) p))

 (* Split on 0 or 1. *)
 | R_dot_3_4_0:  forall (h : Heap) (v0 v1 : E),
                    R h (e_s (dot (cpair v0 v1) zero_pe))
                      h (e_s v0)

 | R_dot_3_4_1:  forall (h : Heap) (v0 v1 : E),
                    R h (e_s (dot (cpair v0 v1) one_pe))
                      h (e_s v1)

 | R_appl_3_5:   forall (h : Heap) (tau tau' : Tau) (v : E) (s : St),
                    Value v ->
                    R h (e_s (appl (f_e (dfun tau tau' s)) v))
                      h (e_s (call (letx v s)))

 | R_call_3_6:    forall (h : Heap) (v : E),
                    Value v ->
                    R h (e_s (call (retn v)))
                      h (e_s v)

 | R_inst_3_7:  forall (h : Heap) (k : Kappa) (f : F) (tau : Tau),
                  R h (e_s (inst (f_e (ufun k f)) tau))
                    h (e_s (f_e (TTM.open_rec_f 0 tau f)))

 | R_call_3_8:  forall (h h': Heap) (s s': St), 
                  S h s h' s' ->
                  R h (e_s (call s)) h' (e_s (call s'))
 
 | R_amp_3_9_1: forall (h h' : Heap) (e e' : E),
                   L h (e_s e)       h' (e_s e') ->
                   R h (e_s (amp e)) h' (e_s (amp e'))

 | R_assign_3_9_2: forall (h h' : Heap) (e e' e2: E),
                   L h (e_s e)             h' (e_s e') ->
                   R h (e_s (assign e e2)) h' (e_s (assign e' e2))

 | R_star_3_10_1: forall (h h' : Heap) (e e' : E),
                    R h (e_s e)        h' (e_s e') ->
                    R h (e_s (star e)) h' (e_s (star e'))

 | R_dot_3_10_2: forall (h h' : Heap) (e e' : E) (ipe : IPE),
                    R h (e_s e) h' (e_s e') ->
                    R h  (e_s (dot e  ipe))
                      h' (e_s (dot e' ipe))

 | R_assign_3_10_3: forall (h h' : Heap) (e e' : E) (x : V) (p : Path),
                    R h (e_s e) h' (e_s e') ->
                    R h  (e_s (assign (p_e x p) e))
                      h' (e_s (assign (p_e x p) e'))

 | R_inst_3_10_4:  forall (h h' : Heap) (e e' : E) (tau : Tau),
                 R h (e_s e) h' (e_s e') ->
                 R h  (e_s (inst e tau)) 
                   h' (e_s (inst e' tau))

 | R_pack_3_10_5:  forall (h h' : Heap) (e e' : E) (tau tau' : Tau) (p : Phi) (k : Kappa),
                    R h (e_s e)        h' (e_s e') ->
                    R h  (e_s (pack tau' e  (etype p k tau)))
                      h' (e_s (pack tau' e' (etype p k tau)))

 | R_cpair_3_10_6:  forall (h h' : Heap) (e e' e2 : E),
                    R h (e_s e) h' (e_s e') ->
                    R h  (e_s (cpair e e2))
                      h' (e_s (cpair e' e2))

 | R_cpair_3_10_7:  forall (h h' : Heap) (e e' v : E),
                    Value v -> 
                    R h (e_s e) h' (e_s e') ->
                    R h  (e_s (cpair v e))
                      h' (e_s (cpair v e'))

 | R_cpair_3_10_8:  forall (h h' : Heap) (e e' e2 : E),
                    R h (e_s e) h' (e_s e') ->
                    R h  (e_s (cpair e e2))
                      h' (e_s (cpair e' e2))

 | R_appl_3_10_9:  forall (h h' : Heap) (e e' e2 : E),
                    R h  (e_s e) h' (e_s e') ->
                    R h  (e_s (appl e e2))
                      h' (e_s (appl e' e2))

 | R_appl_3_10_10: forall (h h' : Heap) (v e e': E),
                     Value v ->
                     R h  (e_s e) h' (e_s e') ->
                     R h  (e_s (appl v e))
                       h' (e_s (appl v e'))

with L : Heap -> St -> Heap -> St -> Prop :=
 | L_xpi_3_1: forall (h : Heap) (x : var) (p : Path) (ipe : IPE),
                L h (e_s (dot (p_e (fevar x) p) ipe))
                  h (e_s (p_e (fevar x) (app p (cons (i_pe ipe) nil))))

 | L_staramp_3_2: forall (h : Heap) (x : V) (p : Path),
                    L h (e_s (star (amp (p_e x p))))
                      h (e_s (p_e x p))

 | L_star_3_3: forall (h h' : Heap) (e e': E),
                 R h (e_s e)        h' (e_s e') ->
                 L h (e_s (star e)) h' (e_s (star e')) 

 | L_ei_3_4: forall (h h' : Heap) (e e': E) (ipe : IPE),
               L h (e_s e)                h' (e_s e') ->
               L h (e_s (dot e ipe))  h' (e_s (dot e' ipe)).


Scheme S_ind_mutual := Induction for S Sort Prop
with   R_ind_mutual := Induction for R Sort Prop
with   L_ind_mutual := Induction for L Sort Prop.

Combined Scheme SRL_ind_mutual 
         from S_ind_mutual, R_ind_mutual, L_ind_mutual.
(* Auto is not applying some of the rules. *)
Hint Constructors S.
Hint Constructors R.
Hint Constructors L.

Hint Extern 4 (S _ _ _ _) => idtac "(S _ _ _ _)"; trace_goal; constructors~.
Hint Extern 4 (R _ _ _ _) => idtac "(R _ _ _ _)"; trace_goal; constructors~.
Hint Extern 4 (L _ _ _ _) => idtac "(L _ _ _ _)"; trace_goal; constructors~.
Hint Extern 4 (R _ (e_s (p_e (fevar _) _)) _ (e_s _)) => idtac "(R _ (e_s (p_e (fevar _) _)) _ (e_s _))"; trace_goal; applys~ R_get_3_1.
