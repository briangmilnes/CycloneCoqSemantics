(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

 This defines the static semantics of statements and expressions, pg. 63. 

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.

Require Export FormalSyntax.
Require Export DynamicSemanticsHeapObjects.
Require Export StaticSemanticsTypingHeapObjects.
Require Export StaticSemanticsKindingAndContextWellFormedness.

Inductive ret : St -> Prop :=
| ret_ret       : forall (e : E),
                       ret (retn e)

| ret_if        : forall (e : E) (s1 s2 : St),
                       ret s1 ->
                       ret s2 ->
                       ret (if_s e s1 s2)

| ret_seq_1     : forall (s s' : St),
                       ret s ->
                       ret (seq s s')

| ret_seq_2     : forall (s s' : St),
                       ret s ->
                       ret (seq s' s)

| ret_let       : forall (x : EVar) (e : E) (s : St),
                       ret s ->
                       ret (letx x e s)

| ret_open      : forall (e : E) (alpha : TVar) (x : EVar) (s : St),
                       ret s ->
                       ret (open e alpha x s)

| ret_openstar  : forall (e : E) (alpha : TVar) (x : EVar) (s : St),
                       ret s ->
                       ret (openstar e alpha x s).

Inductive styp : Delta -> Upsilon -> Gamma -> Tau -> St   -> Prop :=
  | styp_e_3_1    : forall (d : Delta) (u : Upsilon) (g : Gamma) (tau tau' : Tau) (e : E),        (* This is correct, return at end of program. *)
                      rtyp d u g e   tau' ->
                      styp d u g tau (e_s e)

  | styp_return_3_2 : forall (d : Delta) (u : Upsilon) (g : Gamma) (tau : Tau) (e : E),
                         rtyp d u g e tau ->
                         styp d u g tau (retn e)

  | styp_seq_3_3    : forall (d : Delta) (u : Upsilon) (g : Gamma) (tau : Tau) (s1 s2 : St),
                         styp d u g tau s1 ->
                         styp d u g tau s2 ->
                         styp d u g tau (seq s1 s2)

  | styp_while_3_4  : forall (d : Delta) (u : Upsilon) (g : Gamma) (tau : Tau) (e: E) (s : St),
                         rtyp d u g e cint ->
                         styp d u g tau s ->
                         styp d u g tau (while e s)

  | styp_if_3_5     :  forall (d : Delta) (u : Upsilon) (g : Gamma) (tau : Tau) (e: E) (s1 s2 : St),
                          rtyp d u g e cint ->
                          styp d u g tau s1 ->
                          styp d u g tau s2 ->
                          styp d u g tau (if_s e s1 s2)
                               
  | styp_let_3_6    :  forall (d : Delta) (u : Upsilon) (g : Gamma)
                               (x : EVar)  (tau tau' : Tau) 
                               (s : St) (e : E),
                          styp d u (g ++ [(x,tau')])
                                            tau' s ->
                          rtyp d u g e    tau' ->
                          styp d u g tau  (letx x e s)

(* Bug 33, alpha conversion of alpha here ? *)

  | styp_open_3_7   :  forall (d : Delta) (u : Upsilon) (g : Gamma)
                               (x : EVar)  (p : Phi) (alpha : TVar)
                               (k : Kappa) (tau tau' : Tau)
                               (s : St) (e : E),
                          getD d alpha = None ->
                          getG g x = None ->
                          K d tau A      ->
                          rtyp d u g e (etype p alpha k tau') ->
                          styp (d ++ [(alpha,k)]) u (g ++ [(x,tau')])
                               tau s ->
                          styp d u g tau (open e alpha x s)

  | styp_openstar_3_8 :  forall (d : Delta) (u : Upsilon) (g : Gamma)
                               (x : EVar)  (alpha : TVar)
                               (k : Kappa) (tau tau' : Tau)
                               (s : St) (e : E),
                          rtyp d u g e (etype aliases alpha k tau') -> 
                          styp (d ++ [(alpha,k)])
                                  u 
                                  (g ++ [(x,tau')])
                                  tau s ->
                          getD d alpha = None ->
                          getG g x = None ->
                          K d tau A      ->
                          styp d u g tau (openstar e alpha x s)

with      ltyp :   Delta -> Upsilon -> Gamma -> E -> Tau -> Prop := 

  | SL_3_1     : forall (d : Delta) (g : Gamma) (u : Upsilon) 
                           (x : EVar) (p : P) (tau tau': Tau),
                      getG g x = Some tau' ->
                      gettype u x nil tau' p = Some tau ->
                      WFC d u g->
                      K d tau' A -> 
                      ltyp d u g (p_e x p) tau

  | SL_3_2     : forall (d : Delta) (u : Upsilon) (g : Gamma)
                        (e : E) (tau : Tau) ,
                      rtyp d u g e (ptype tau) ->
                      K d tau A ->
                      ltyp d u g (star e) tau

  | SL_3_3     : forall (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t0 t1 : Tau),
                      ltyp d u g e (cross t0 t1) ->
                      ltyp d u g (dot e (i_i Z0)) t0

  | SL_3_4     : forall (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t0 t1 : Tau),
                      ltyp d u g e (cross t0 t1) ->
                      ltyp d u g (dot e (i_i 1)) t1

with      rtyp :  Delta -> Upsilon -> Gamma -> E   -> Tau -> Prop := 
  | SR_3_1  : forall (d : Delta) (g : Gamma) (u : Upsilon) 
                        (x  : EVar) (p : P) (tau tau': Tau),
                   getG g x = Some tau' -> 
                   gettype u x nil tau' p = Some tau ->
                   K d tau' A ->
                   WFC d u g ->
                   rtyp d u g (p_e x p) tau

  | SR_3_2  :  forall (e : E) (tau : Tau) 
                      (d : Delta) (u : Upsilon) (g : Gamma),
                    rtyp d u g e (ptype tau) ->
                    K d tau A ->
                    rtyp d u g (star e) tau
                            
  | SR_3_3  :  forall (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t0 t1 : Tau),
                        rtyp d u g e (cross t0 t1) ->
                        rtyp d u g (dot e (i_i Z0)) t0

  | SR_3_4  : forall (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t0 t1 : Tau),
                      rtyp d u g e (cross t0 t1) ->
                      rtyp d u g (dot e (i_i 1)) t1

  | SR_3_5  : forall (d : Delta) (u : Upsilon) (g : Gamma) (z : Z),
                   WFC d u g ->
                   rtyp d u g (i_e (i_i z)) cint

  | SR_3_6  : forall (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau : Tau),
                   ltyp d u g e tau ->
                   rtyp d u g (amp e) (ptype tau)

  | SR_3_7  : forall (d : Delta) (u : Upsilon) (g : Gamma) (e0 e1: E) (t0 t1 : Tau),
                   rtyp d u g e0 t0 ->
                   rtyp d u g e1 t1 ->
                   rtyp d u g (cpair e0 e1) (cross t0 t1)

  | SR_3_8  : forall (d : Delta) (u : Upsilon) (g : Gamma) (e1 e2 : E) (tau : Tau),
                   ltyp d u g e1 tau ->
                   rtyp d u g e2 tau ->
                   ASGN d tau    ->
                   rtyp d u g (assign e1 e2) tau

  | SR_3_9  : forall (d : Delta) (u : Upsilon) (g : Gamma) (e1 e2 : E) (tau tau' : Tau),
                   rtyp d u g e1 (arrow tau' tau) ->
                   rtyp d u g e2 tau' ->
                   rtyp d u g (appl e1 e2) tau

  | SR_3_10 : forall (d : Delta) (u : Upsilon) (g : Gamma) (tau : Tau) (s : St),
                   styp d u g tau s ->
                   ret s ->
                   rtyp d u g (call s) tau

  | SR_3_11 : forall (d : Delta) (u : Upsilon) (g : Gamma) (e : E) 
                        (tau tau': Tau) (alpha : TVar) (k : Kappa),
                   rtyp d u g e (utype alpha k tau') ->
                   AK   d tau k ->
                   rtyp d u g (inst e tau) (subst_Tau tau' tau alpha)

  | SR_3_12 : forall (d : Delta) (u : Upsilon) (g : Gamma) (e : E) 
                        (tau tau': Tau) (alpha : TVar) (k : Kappa) (p : Phi),
                   rtyp d u g e (subst_Tau tau tau' alpha) ->
                   AK   d tau' k -> 
                   K    d (etype p alpha k tau) A ->
                   rtyp d u g (pack tau' e (etype p alpha k tau)) (etype p alpha k tau)

  | SR_3_13 : forall (d : Delta) (u : Upsilon) (g : Gamma) (tau tau': Tau) (s : St) (x : EVar),
                   getG g x = None ->
                   styp d u (g ++ [(x,tau)]) tau' s ->
                   ret s ->
                   rtyp d u g (f_e (dfun tau x tau' s)) (arrow tau tau')

  | SR_3_14 : forall (d : Delta) (u : Upsilon) (g : Gamma) (f : F)
                        (tau : Tau) (alpha : TVar) (k : Kappa),
                   getD d alpha = None ->
                   WFC  d u g ->
                   rtyp (d ++ [(alpha,k)]) u g (f_e f) tau ->
                   rtyp d u g (f_e (ufun alpha k f)) (utype alpha k tau).

Scheme styp_ind_mutual := Induction for styp Sort Prop
with   ltyp_ind_mutual := Induction for ltyp Sort Prop
with   rtyp_ind_mutual := Induction for rtyp Sort Prop.
Combined Scheme typ_ind_mutual from
          styp_ind_mutual, ltyp_ind_mutual, rtyp_ind_mutual.

Inductive htyp: Upsilon -> Gamma -> H -> Gamma -> Prop :=
  | htyp_empty : forall (u : Upsilon) (g: Gamma),
                      htyp u g nil nil
  | htyp_xv    : forall (u : Upsilon) (g g': Gamma) (h h': H) (x : EVar) (v : E) (tau : Tau),
                      Value v -> 
                      htyp u g (h ++ h') g' ->
                      rtyp nil u g v tau ->
                      htyp u g (h ++ [(x,v)] ++ h') (g' ++ [(x, tau)]).

Inductive refp  : H -> Upsilon -> Prop :=
  | refp_empty  : forall (h : H),
                       refp h nil
  | refp_pack  : forall (h : H) (u : Upsilon) (x : EVar) (p : P) (tau tau' : Tau) (alpha : TVar) (k : Kappa) (v v' : E),
                      getH h x = Some v' -> 
                      get v' p (pack tau' v (etype aliases alpha k tau)) ->
                      refp h u ->
                      refp h (u ++ [((p_e x p),tau')]).

Inductive prog  : H -> St -> Prop := 
  | program  : forall (h : H) (u : Upsilon) (g : Gamma) (tau : Tau) (s : St),
                    htyp u g h g ->
                    refp h u     ->
                    styp nil u g tau s ->
                    ret s -> 
                    prog h s.
