(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

 This defines the static semantics of statements and expressions, pg. 63. 

*)

Set Implicit Arguments.
Require Export Cyclone_Dynamic_Semantics_Heap_Objects.
Require Export Cyclone_Static_Semantics_Typing_Heap_Objects.
Require Export Cyclone_Static_Semantics_Kinding_And_Context_Well_Formedness.
Close Scope list_scope.
Import LibEnvNotations.
Import LVPE.LibVarPathEnvNotations.

Inductive ret : St -> Prop :=
| ret_ret       : forall (e : E),
                       ret (retn e)

| ret_if        : forall (e : E) (s1 s2 : St),
                       ret s1 ->
                       ret s2 ->
                       ret (if_s e s1 s2)

| ret_seq_1     : forall (s s' : St),
                       ret s ->
                       ret (seqx s s')

| ret_seq_2     : forall (s s' : St),
                       ret s' ->
                       ret (seqx s s')

| ret_let       : forall (e : E) (s : St),
                       ret s ->
                       ret (letx e s)

| ret_open      : forall (e : E) (s : St),
                       ret s ->
                       ret (openx e s)

| ret_openstar  : forall (e : E) (s : St),
                       ret s ->
                       ret (openstar e s).
Hint Constructors ret.

Inductive styp : Delta -> Upsilon -> Gamma -> St -> Tau -> Prop :=
  | styp_e_3_1    : forall (d : Delta) (u : Upsilon) (g : Gamma) 
                           (tau: Tau) (e : E),      
                      rtyp d u g e  tau -> 
                      styp d u g (e_s e) tau

(* This is correct, return at end of program. *)
  | styp_return_3_2 : forall (d : Delta) (u : Upsilon) (g : Gamma)
                             (tau : Tau) (e : E),
                         rtyp d u g e tau ->
                         styp d u g (retn e) tau

  | styp_seq_3_3    : forall (d : Delta) (u : Upsilon) (g : Gamma)
                             (tau : Tau) (s1 s2 : St),
                         styp d u g s1 tau ->
                         styp d u g s2 tau ->
                         styp d u g (seqx s1 s2) tau

  | styp_if_3_5     :  forall (d : Delta) (u : Upsilon) (g : Gamma) 
                              (tau : Tau) (e: E) (s1 s2 : St),
                          rtyp d u g e cint ->
                          styp d u g s1 tau ->
                          styp d u g s2 tau ->
                          styp d u g (if_s e s1 s2) tau

  | styp_while_3_4  : forall (d : Delta) (u : Upsilon) (g : Gamma) 
                             (tau : Tau) (e: E) (s : St),
                         rtyp d u g e cint ->
                         styp d u g s tau ->
                         styp d u g (while e s) tau

  | styp_let_3_6    :  forall (L : vars) (d : Delta) (u : Upsilon) (g : Gamma)
                               (tau tau' : Tau) 
                               (s : St) (e : E),
                          (forall (x : var),
                            x \notin L -> 
                            styp d u (g & (x ~ tau')) (TM.open_rec_st 0 x s) tau) ->
                            rtyp d u g e tau' ->
                            K d tau' A ->  (* Thesis change. *)
                            styp d u g (letx e s) tau

  | styp_open_3_7   :  forall (L : vars) (d : Delta) (u : Upsilon) (g : Gamma)
                               (k : Kappa) (tau tau' : Tau)
                               (s : St) (e : E),
                         (forall (x : var) (alpha : var),
                             x \notin L ->
                             alpha \notin L ->
                             styp ((alpha ~ k) & d)
                                  u
                                  (g & (x ~ (T.open_rec 0 (ftvar alpha) tau')))
                                  (TTM.open_rec_st 0 (ftvar alpha)
                                                   (TM.open_rec_st 0 x s))
                                  tau) ->
                         rtyp d u g e tau' ->
                         K d tau A      ->
                         styp d u g (openx e s) tau

  | styp_openstar_3_8 :  forall (L : vars) (d : Delta) (u : Upsilon) (g : Gamma)
                               (k : Kappa) (tau tau' : Tau)
                               (s : St) (e : E),
                         (forall (x : var) (alpha : var),
                             x \notin L ->
                             alpha \notin L ->
                             styp (d & (alpha ~ k))
                                  u
                                  (g & (x ~ (T.open_rec 0 (ftvar alpha) (ptype tau')))) 
                                  (TTM.open_rec_st 0 (ftvar alpha)
                                                   (TM.open_rec_st 0 x s))
                                  tau) ->
                          ltyp d u g e tau' ->
                          K d tau A      ->
                          styp d u g (openstar e s) tau 

with      ltyp :   Delta -> Upsilon -> Gamma -> E -> Tau -> Prop := 

  | SL_3_1     : forall (d : Delta) (g : Gamma) (u : Upsilon) 
                           (x : var) (p : Path) (tau tau': Tau),
                      binds x tau' g ->
                      (* get x g = Some tau' -> *)
                      gettype u x nil tau' p tau ->
                      WFC d u g ->
                      K d tau' A -> 
                      ltyp d u g (p_e (fevar x) p) tau

  | SL_3_2     : forall (d : Delta) (u : Upsilon) (g : Gamma)
                        (e : E) (tau : Tau) ,
                      rtyp d u g e (ptype tau) ->
                      K d tau A ->
                      ltyp d u g (star e) tau

  | SL_3_3     : forall (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t0 t1 : Tau),
                      ltyp d u g e (cross t0 t1) ->
                      ltyp d u g (dot e zero_pe) t0

  | SL_3_4     : forall (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t0 t1 : Tau),
                      ltyp d u g e (cross t0 t1) ->
                      ltyp d u g (dot e one_pe) t1

with      rtyp :  Delta -> Upsilon -> Gamma -> E   -> Tau -> Prop := 
  | SR_3_1  : forall (d : Delta) (g : Gamma) (u : Upsilon) 
                        (x  : var) (p : Path) (tau tau': Tau),
                   binds x tau' g ->
                   (* get x g = Some tau' ->  *)
                   gettype u x nil tau' p tau ->
                   K d tau' A ->
                   WFC d u g ->
                   rtyp d u g (p_e (fevar x) p) tau

  | SR_3_2  :  forall (e : E) (tau : Tau) 
                      (d : Delta) (u : Upsilon) (g : Gamma),
                    rtyp d u g e (ptype tau) ->
                    K d tau A ->
                    rtyp d u g (star e) tau
                            
  | SR_3_3  :  forall (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t0 t1 : Tau),
                        rtyp d u g e (cross t0 t1) ->
                        rtyp d u g (dot e zero_pe) t0

  | SR_3_4  : forall (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t0 t1 : Tau),
                      rtyp d u g e (cross t0 t1) ->
                      rtyp d u g (dot e one_pe) t1

  | SR_3_5  : forall (d : Delta) (u : Upsilon) (g : Gamma) (n : nat),
                   WFC d u g ->
                   rtyp d u g (i_e (i_i n)) cint

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
                   styp d u g s tau ->
                   ret s ->
                   rtyp d u g (call s) tau

  | SR_3_11 : forall (d : Delta) (u : Upsilon) (g : Gamma) (e : E) 
                        (tau tau' tau'': Tau) (k : Kappa),
                   rtyp d u g e (utype k tau') ->
                   AK   d tau k ->
                   (T.open_rec 0 tau tau') = tau'' ->
                   rtyp d u g (inst e tau) tau''

  | SR_3_12 : forall (L : vars) (d : Delta) (u : Upsilon) (g : Gamma) (e : E) 
                        (tau tau': Tau) (k : Kappa) (p : Phi),
               (forall (alpha : var),
                   alpha \notin L ->
                   rtyp d u g e (T.open_rec 0 tau' tau)) ->
                   K    d (etype p k tau) A ->
                   AK   d tau' k -> 
                   rtyp d u g (pack tau' e (etype p k tau)) 
                              (etype p k tau)

  | SR_3_13 : forall (L : vars) (d : Delta) (u : Upsilon) (g : Gamma) (tau tau': Tau) 
                     (s : St),
               (forall (x : var),
                   x \notin L ->
                   styp d u (g & (x ~ tau)) (TM.open_rec_st 0 x s) tau') ->
                   ret s ->
                   rtyp d u g (f_e (dfun tau tau' s)) (arrow tau tau')

  | SR_3_14 : forall (L : vars) (d : Delta) (u : Upsilon) (g : Gamma) (f : F)
                        (tau : Tau) (k : Kappa),
                 (forall alpha,
                     alpha \notin L ->
                     rtyp (d & (alpha ~ k)) u g (f_e (TTM.open_rec_f 0 (ftvar alpha) f))
                          (T.open_rec 0 (ftvar alpha) tau)) ->
                   WFC  d u g ->
                   rtyp d u g (f_e (ufun k f)) (utype k tau).


Scheme styp_ind_mutual := Induction for styp Sort Prop
with   ltyp_ind_mutual := Induction for ltyp Sort Prop
with   rtyp_ind_mutual := Induction for rtyp Sort Prop.
Combined Scheme typ_ind_mutual from
          styp_ind_mutual, ltyp_ind_mutual, rtyp_ind_mutual.

Hint Constructors styp.
Hint Constructors rtyp.
Hint Constructors ltyp.
Hint Extern 6 (rtyp _ _       (?E & (?x ~ ?t')) (p_e (fevar ?x) nil) ?t') =>
idtac "find_tau" t';
apply SR_3_1 with (tau':= t'); auto.

Inductive htyp: Upsilon -> Gamma -> Heap -> Gamma -> Prop :=
   | htyp_empty : forall (u : Upsilon) (g: Gamma),
                       htyp u g hdot gdot

   | htyp_xv    : forall (u : Upsilon) (g g' g'': Gamma) (h h': Heap) (x : var)
                         (v : E) (tau : Tau),
                      Value v ->
                      (* Question is this env hacking right ? *)
                      (* Arthur works from the right. *)
                      htyp u g (h & h') (g' & g'') ->
                      rtyp ddot u g v tau ->
                      htyp u g (h & (x ~ v) & h') (g' & (x ~ tau) & g'').
Hint Constructors htyp.


Inductive refp  : Heap -> Upsilon -> Prop :=
  | refp_empty  : forall (h : Heap),
                       refp h udot

  | refp_pack  : forall (h : Heap) (u : Upsilon) (x : var) (p : Path)
                        (tau tau' : Tau) (k : Kappa) (v v' : E),
                      binds x v' h ->
                      (* get x h = Some v' ->  *)
                      get' v' p (pack tau' v (etype aliases k tau)) ->
                      refp h u ->
                      refp h (u &p ((x,p) ~p tau')).
Hint Constructors refp.

(* This has an arbitrary return type due to Dan's style. So it is not syntax directed. *)
Inductive prog  : Heap -> St -> Prop := 
  | program  : forall (h : Heap) (u : Upsilon) (g : Gamma) (tau : Tau) (s : St),
                    htyp u g h g ->
                    refp h u     ->
                    styp ddot u g s tau ->
                    ret s -> 
                    prog h s.
Hint Constructors prog.