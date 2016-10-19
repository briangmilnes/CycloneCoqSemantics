(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

 This defines the dynamic semantics of statements and expressions, pg. 58, 59.

*)
 
Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.
Require Import Relation_Definitions.

Require Export FormalSyntax.
Require Export DynamicSemanticsTypeSubstitution.
Require Export DynamicSemanticsHeapObjects.

Inductive S : H -> St -> H -> St -> Prop :=

 | S_let_3_1 : forall (x : EVar) (v : E) (h : H) (s: St),
              Value v ->
              getH h x = None -> 
              S h (letx x v s) ((x,v) :: h) s

 | S_seq_3_2 : forall (v : E) (h : H) (s: St),
                  Value v ->
                  S h (seq (e_s v) s) h s

 | S_return_3_3: forall (v : E) (h : H) (s: St),
                    Value v ->
                    S h (seq (retn v) s) h (retn v)

 | S_if0_3_4: forall (h : H) (s1 s2: St),
                 S h (if_s (i_e (i_i 0)) s1 s2)
                   h s1

 | S_if_ne_0_3_5: forall (h : H) (z : Z) (s1 s2: St),
                     z <> Z0 ->                                  
                     S h (if_s (i_e (i_i z)) s1 s2)
                       h s2

 | S_while_3_6: forall (h : H) (e : E) (s : St),
                     S h (while e s)
                       h (if_s e (seq s (while e s)) (e_s (i_e (i_i 0))))

| S_open_3_7:  forall (tau tau' : Tau) (v : E) (p : Phi) (k : Kappa) (alpha : TVar) (x x': EVar) (h : H) (s : St),
                  Value v ->
                  S h (open (pack tau' v (etype p alpha k tau)) alpha x s)
                    h (letx x' v (subst_St s tau alpha))

| S_openstar_3_8: forall (tau tau' : Tau) (v v' : E) (q : Phi) (k : Kappa) (alpha : TVar) (x x': EVar) (h : H) (s : St) (p : P),
                    Value v ->
                    x <> x' ->
                    get v' p (pack tau' v (etype q alpha k tau)) ->
                    (* S is part of the context not the heap, overloading ; in DS3.8 *)
                    (* x' is right, openstar uses *x' but I am eliding it in the syntax. *)
                    getH h x = Some v' ->
                    S h (openstar (p_e x p) alpha x' s)
                      h (letx x'  (amp (p_e x (p ++ [u_pe]))) 
                                     (subst_St s tau alpha))

| S_exp_3_9_1: forall (h h' : H) (e e' : E),
                   R h (e_s e) h' (e_s e') ->
                   S h (e_s e) h' (e_s e')

| S_ret_3_9_2: forall (h h' : H) (e e' : E),
                   R h (e_s e) h' (e_s e') ->
                   S h (retn e) h' (retn e')

| S_if_3_9_3: forall (h h' : H) (e e' : E) (s1 s2 : St),
                   R h (e_s e) h' (e_s e') ->
                   S h (if_s e s1 s2) h' (if_s e' s1 s2)

| S_letx_3_9_4: forall (h h' : H) (e e' : E) (s : St) (x : EVar),
                   R h (e_s e) h' (e_s e') ->
                   S h (letx x e s) h' (letx x e' s)

| S_open_3_9_5: forall (h h' : H) (e e' : E) (x : EVar) (alpha : TVar) (s : St),
                   R h (e_s e) h' (e_s e') ->
                   S h  (open e  alpha x s)
                        h' (open e' alpha x s)

| S_seq_3_10:  forall (h h' : H) (s s' s2: St),
                    S h s h' s' ->
                    S h  (seq s  s2) h' (seq s' s2)

| S_openstar_3_11: forall (h h' : H) (e e' : E) (x : EVar) (alpha : TVar) (s : St),
                        L h  (e_s e) h' (e_s e') ->
                        S h  (openstar e  alpha x s)
                          h' (openstar e' alpha x s)

with R : H -> St -> H -> St -> Prop :=

 | R_get_3_1 : forall (h  : H) (x : EVar) (p : P) (v v' : E),
                    Value v ->
                    Value v' ->
                    get v' p v ->
                    getH h x = Some v' -> 
                    R h (e_s (p_e x p))
                      h (e_s v)

 | R_assign_3_2:
     forall (h' h : H) (v v' v'' : E) (x : EVar) (p : P),
       Value v   ->
       Value v'  ->
       Value v'' ->
       set v' p v v'' ->
       R (h ++ ([(x,v')] ++ h'))  (e_s (assign (p_e x p) v))
         (h ++ ([(x,v'')] ++ h')) (e_s v)

 | R_star_3_3:   forall (h : H) (x : EVar) (p : P),
                   R h (e_s (star (amp (p_e x p))))
                     h (e_s (p_e x p))

 (* Split on 0 or 1. *)
 | R_dot_3_4_0:  forall (h : H) (v0 v1 : E),
                    R h (e_s (dot (cpair v0 v1) (i_i 0)))
                      h (e_s v0)

 | R_dot_3_4_1:  forall (h : H) (v0 v1 : E),
                    R h (e_s (dot (cpair v0 v1) (i_i 1)))
                      h (e_s v1)

 | R_appl_3_5:   forall (h : H) (x : EVar) (tau tau' : Tau) (v : E) (s : St),
                    Value v ->
                    R h (e_s (appl (f_e (dfun tau x tau' s)) v))
                      h (e_s (call (letx x v s)))

 | R_call_3_6:    forall (h : H) (v : E),
                    Value v ->
                    R h (e_s (call (retn v)))
                      h (e_s v)

 | R_inst_3_7:  forall (h : H) (alpha : TVar) (k : Kappa) (f : F) (tau : Tau),
                  R h (e_s (inst (f_e (ufun alpha k f)) tau))
                    h (e_s (f_e (subst_F f tau alpha)))

 | R_call_3_8:  forall (h h': H) (s s': St), 
                  S h s h' s' ->
                  R h (e_s (call s)) h' (e_s (call s'))
 
 | R_amp_3_9_1: forall (h h' : H) (e e' : E),
                   L h (e_s e)       h' (e_s e') ->
                   R h (e_s (amp e)) h' (e_s (amp e'))

 | R_assign_3_9_2: forall (h h' : H) (e e' e2: E),
                   L h (e_s e)             h' (e_s e') ->
                   R h (e_s (assign e e2)) h' (e_s (assign e' e2))

 | R_star_3_10_1: forall (h h' : H) (e e' : E),
                    R h (e_s e)        h' (e_s e') ->
                    R h (e_s (star e)) h' (e_s (star e'))

 | R_dot_3_10_2: forall (h h' : H) (e e' : E) (z : Z),
                    R h (e_s e) h' (e_s e') ->
                    R h  (e_s (dot e  (i_i z)))  
                      h' (e_s (dot e' (i_i z)))

 | R_assign_3_10_3: forall (h h' : H) (e e' : E) (x : EVar) (p : P),
                    R h (e_s e) h' (e_s e') ->
                    R h  (e_s (assign (p_e x p) e))
                      h' (e_s (assign (p_e x p) e'))

 | R_inst_3_10_4:  forall (h h' : H) (e e' : E) (tau : Tau),
                 R h (e_s e) h' (e_s e') ->
                 R h  (e_s (inst e tau)) 
                   h' (e_s (inst e' tau))

 | R_pack_3_10_5:  forall (h h' : H) (e e' : E) (tau tau' : Tau) (p : Phi) (k : Kappa) (alpha : TVar),
                    R h (e_s e)        h' (e_s e') ->
                    R h  (e_s (pack tau' e  (etype p alpha k tau)))
                      h' (e_s (pack tau' e' (etype p alpha k tau)))

 | R_cpair_3_10_6:  forall (h h' : H) (e e' e2 : E),
                    R h (e_s e) h' (e_s e') ->
                    R h  (e_s (cpair e e2))
                      h' (e_s (cpair e' e2))

 | R_cpair_3_10_7:  forall (h h' : H) (e e' v : E),
                    Value v -> 
                    R h (e_s e) h' (e_s e') ->
                    R h  (e_s (cpair v e))
                      h' (e_s (cpair v e'))

 | R_cpair_3_10_8:  forall (h h' : H) (e e' e2 : E),
                    R h (e_s e) h' (e_s e') ->
                    R h  (e_s (cpair e e2))
                      h' (e_s (cpair e' e2))

 | R_appl_3_10_9:  forall (h h' : H) (e e' e2 : E),
                    R h  (e_s e) h' (e_s e') ->
                    R h  (e_s (appl e e2))
                      h' (e_s (appl e' e2))

 | R_appl_3_10_10: forall (h h' : H) (v e e': E),
                     Value v ->
                     R h  (e_s e) h' (e_s e') ->
                     R h  (e_s (appl v e))
                       h' (e_s (appl v e'))

with L : H -> St -> H -> St -> Prop :=

 | L_xpi_3_1: forall (h : H) (x : EVar) (p : P) (z : Z),
                L h (e_s (dot (p_e x p) (i_i z)))
                  h (e_s (p_e x (p ++ [(i_pe (i_i z))])))

 | L_staramp_3_2: forall (h : H) (x : EVar) (p : P),
                    L h (e_s (star (amp (p_e x p))))
                      h (e_s (p_e x p))

 | L_star_3_3: forall (h h' : H) (e e': E),
                 R h (e_s e)        h' (e_s e') ->
                 L h (e_s (star e)) h' (e_s (star e')) 

 | L_ei_3_4: forall (h h' : H) (e e': E) (z : Z),
               L h (e_s e)                h' (e_s e') ->
               L h (e_s (dot e (i_i z)))  h' (e_s (dot e' (i_i z))).

Scheme R_ind_mutual := Induction for R Sort Prop
with   S_ind_mutual := Induction for S Sort Prop
with   L_ind_mutual := Induction for L Sort Prop.
Combined Scheme SLR_ind_mutual 
         from S_ind_mutual, L_ind_mutual, R_ind_mutual.

(* Transitive, reflexive closure of S. *)

Inductive multi (R : H -> St -> H -> St -> Prop) 
              : H -> St -> H -> St -> Prop :=
  | multi_refl  : forall (h h' : H) (s s' : St), 
                    multi R h s h' s'
  | multi_step : forall (h h' h'': H) (s s' s'' : St),
                    R h s h' s' ->
                    multi R h' s' h'' s'' ->
                    multi R h s h'' s''.

Definition Sstar := (multi S).
