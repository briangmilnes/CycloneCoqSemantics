(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

 This defines the static semantics of statements and expressions, pg. 63. 

*)

Set Implicit Arguments.
Require Export LanguageModuleDef.
Require Export DynamicSemanticsHeapObjects.
Require Export StaticSemanticsTypingHeapObjects.
Require Export StaticSemanticsKindingAndContextWellFormedness.
(* I want to be able to work with Tau and Term without module paths. *)
(* But they collide. *)
(* and if I change TM then I I have to fold/unfold in places. *)


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
                       ret s' ->
                       ret (seq s s')

| ret_let       : forall (x : EVar) (e : E) (s : St),
                       ret s ->
                       ret (letx x e s)

| ret_open      : forall (e : E) (alpha : TVar) (x : EVar) (s : St),
                       ret s ->
                       ret (open e alpha x s)

| ret_openstar  : forall (e : E) (alpha : TVar) (x : EVar) (s : St),
                       ret s ->
                       ret (openstar e alpha x s).

(* TODO inconsistent naming. *)
Inductive styp : Delta -> Upsilon -> Gamma -> Tau -> St   -> Prop :=
(* This is correct, return at end of program. *)
  | styp_e_3_1    : forall (d : Delta) (u : Upsilon) (g : Gamma) 
                           (tau tau': Tau) (e : E),      
                      (* This just messes up the proofs. *)
                      rtyp d u g e  tau' -> 
                      (* rtyp d u g e  tau -> *)
                      styp d u g tau (e_s e)

  | styp_return_3_2 : forall (d : Delta) (u : Upsilon) (g : Gamma)
                             (tau : Tau) (e : E),
                         rtyp d u g e tau ->
                         styp d u g tau (retn e)

  | styp_seq_3_3    : forall (d : Delta) (u : Upsilon) (g : Gamma)
                             (tau : Tau) (s1 s2 : St),
                         styp d u g tau s1 ->
                         styp d u g tau s2 ->
                         styp d u g tau (seq s1 s2)

  | styp_while_3_4  : forall (d : Delta) (u : Upsilon) (g : Gamma) 
                             (tau : Tau) (e: E) (s : St),
                         rtyp d u g e T.cint ->
                         styp d u g tau s ->
                         styp d u g tau (while e s)

  | styp_if_3_5     :  forall (d : Delta) (u : Upsilon) (g : Gamma) 
                              (tau : Tau) (e: E) (s1 s2 : St),
                          rtyp d u g e T.cint ->
                          styp d u g tau s1 ->
                          styp d u g tau s2 ->
                          styp d u g tau (if_s e s1 s2)

(* Bug 38 wrong tau' in styp. *)
  | styp_let_3_6    :  forall (d : Delta) (u : Upsilon) (g : Gamma)
                               (x : EVar)  (tau tau' : Tau) 
                               (s : St) (e : E),
                          G.map g x = None ->
                          K d tau' A ->  (* Thesis change. *)
                          styp d u (G.ctxt x tau' g) tau s ->
                          rtyp d u g e    tau' ->
                          styp d u g tau  (letx x e s)

(* Bug 33, alpha conversion of alpha here ? *)
(* TODO can I unfold the expected pack here and make these syntax directed ? *)
(* I think so. *)
(* Bug 44, forgot not in domain checks. *)
  | styp_open_3_7   :  forall (d : Delta) (u : Upsilon) (g : Gamma)
                               (x : EVar)  (p : Phi) (alpha : TVar)
                               (k : Kappa) (tau tau' : Tau)
                               (s : St) (e : E),
                          D.map d alpha = None ->
                          G.map g x = None ->
                          K d tau A      ->
                          rtyp d u g e (T.etype p alpha k tau') ->
                          styp (D.ctxt alpha k d) u (G.ctxt x tau' g)
                               tau s ->
                          styp d u g tau (open e alpha x s)

  | styp_openstar_3_8 :  forall (d : Delta) (u : Upsilon) (g : Gamma)
                               (x : EVar)  (alpha : TVar)
                               (k : Kappa) (tau tau' : Tau)
                               (s : St) (e : E),
                          rtyp d u g e (T.etype aliases alpha k tau') -> 
                          styp (D.ctxt alpha k d)
                               u 
                               (G.ctxt x tau' g)
                               tau s ->
                          D.map d alpha = None ->
                          G.map g x = None ->
                          K d tau A      ->
                          styp d u g tau (openstar e alpha x s)

with      ltyp :   Delta -> Upsilon -> Gamma -> E -> Tau -> Prop := 

  | SL_3_1     : forall (d : Delta) (g : Gamma) (u : Upsilon) 
                           (x : EVar) (p : Path) (tau tau': Tau),
                      G.map g x = Some tau' ->
                      gettype u x nil tau' p tau ->
                      WFC d u g ->
                      K d tau' A -> 
                      ltyp d u g (p_e x p) tau

  | SL_3_2     : forall (d : Delta) (u : Upsilon) (g : Gamma)
                        (e : E) (tau : Tau) ,
                      rtyp d u g e (T.ptype tau) ->
                      K d tau A ->
                      ltyp d u g (star e) tau

  | SL_3_3     : forall (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t0 t1 : Tau),
                      ltyp d u g e (T.cross t0 t1) ->
                      ltyp d u g (TM.dot e Pth.zero_pe) t0

  | SL_3_4     : forall (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t0 t1 : Tau),
                      ltyp d u g e (T.cross t0 t1) ->
                      ltyp d u g (TM.dot e Pth.one_pe) t1

with      rtyp :  Delta -> Upsilon -> Gamma -> E   -> Tau -> Prop := 
  | SR_3_1  : forall (d : Delta) (g : Gamma) (u : Upsilon) 
                        (x  : EVar) (p : Path) (tau tau': Tau),
                   G.map g x = Some tau' -> 
                   gettype u x nil tau' p tau ->
                   K d tau' A ->
                   WFC d u g ->
                   rtyp d u g (p_e x p) tau

  | SR_3_2  :  forall (e : E) (tau : Tau) 
                      (d : Delta) (u : Upsilon) (g : Gamma),
                    rtyp d u g e (T.ptype tau) ->
                    K d tau A ->
                    rtyp d u g (TM.star e) tau
                            
  | SR_3_3  :  forall (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t0 t1 : Tau),
                        rtyp d u g e (T.cross t0 t1) ->
                        rtyp d u g (TM.dot e Pth.zero_pe) t0

  | SR_3_4  : forall (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t0 t1 : Tau),
                      rtyp d u g e (T.cross t0 t1) ->
                      rtyp d u g (TM.dot e Pth.one_pe) t1

  | SR_3_5  : forall (d : Delta) (u : Upsilon) (g : Gamma) (z : Z),
                   WFC d u g ->
                   rtyp d u g (i_e (i_i z)) T.cint

  | SR_3_6  : forall (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau : Tau),
                   ltyp d u g e tau ->
                   rtyp d u g (amp e) (T.ptype tau)

  | SR_3_7  : forall (d : Delta) (u : Upsilon) (g : Gamma) (e0 e1: E) (t0 t1 : Tau),
                   rtyp d u g e0 t0 ->
                   rtyp d u g e1 t1 ->
                   rtyp d u g (cpair e0 e1) (T.cross t0 t1)

  | SR_3_8  : forall (d : Delta) (u : Upsilon) (g : Gamma) (e1 e2 : E) (tau : Tau),
                   ltyp d u g e1 tau ->
                   rtyp d u g e2 tau ->
                   ASGN d tau    ->
                   rtyp d u g (assign e1 e2) tau

  | SR_3_9  : forall (d : Delta) (u : Upsilon) (g : Gamma) (e1 e2 : E) (tau tau' : Tau),
                   rtyp d u g e1 (T.arrow tau' tau) ->
                   rtyp d u g e2 tau' ->
                   rtyp d u g (TM.appl e1 e2) tau

  | SR_3_10 : forall (d : Delta) (u : Upsilon) (g : Gamma) (tau : Tau) (s : St),
                   styp d u g tau s ->
                   ret s ->
                   rtyp d u g (call s) tau

  | SR_3_11 : forall (d : Delta) (u : Upsilon) (g : Gamma) (e : E) 
                        (tau tau': Tau) (alpha : TVar) (k : Kappa),
                   rtyp d u g e (T.utype alpha k tau') ->
                   AK   d tau k ->
                   rtyp d u g (inst e tau) (subst_Tau tau' tau alpha)

  | SR_3_12 : forall (d : Delta) (u : Upsilon) (g : Gamma) (e : E) 
                        (tau tau': Tau) (alpha : TVar) (k : Kappa) (p : Phi),
                   rtyp d u g e (subst_Tau tau tau' alpha) ->
                   AK   d tau' k -> 
                   K    d (T.etype p alpha k tau) A ->
                   rtyp d u g (pack tau' e (T.etype p alpha k tau)) 
                              (T.etype p alpha k tau)

  | SR_3_13 : forall (d : Delta) (u : Upsilon) (g : Gamma) (tau tau': Tau) 
                     (s : St) (x : EVar),
                   G.map g x = None ->
                   styp d u (G.ctxt x tau g) tau' s ->
                   ret s ->
                   rtyp d u g (f_e (dfun tau x tau' s)) (T.arrow tau tau')

  | SR_3_14 : forall (d : Delta) (u : Upsilon) (g : Gamma) (f : F)
                        (tau : Tau) (alpha : TVar) (k : Kappa),
                   D.map d alpha = None ->
                   WFC  d u g ->
                   rtyp (D.ctxt alpha k d) u g (f_e f) tau ->
                   rtyp d u g (f_e (ufun alpha k f)) (T.utype alpha k tau).

Scheme styp_ind_mutual := Induction for styp Sort Prop
with   ltyp_ind_mutual := Induction for ltyp Sort Prop
with   rtyp_ind_mutual := Induction for rtyp Sort Prop.
Combined Scheme typ_ind_mutual from
          styp_ind_mutual, ltyp_ind_mutual, rtyp_ind_mutual.

(*
Lemma ltyp_context_dependent_induction_mutual:
  forall P : forall (beta : TVar) (k : Kappa) (d : Delta) (u : Upsilon) (g : Gamma)
                    (t : Tau) (s : St),
       styp (D.ctxt beta k d) u g t s -> Prop, 
    forall P0 : forall (beta : TVar) (k : Kappa) (d : Delta) (u : Upsilon) 
                       (g : Gamma) (e : E) (t : Tau),
        ltyp (D.ctxt beta k d) u g e t -> Prop, 
     forall P1 : forall (beta : TVar) (k : Kappa) (d : Delta) (u : Upsilon) 
                        (g : Gamma) (e : E) (t : Tau),
        rtyp (D.ctxt beta k d) u g e t -> Prop,
  (forall (beta : TVar) (k' : Kappa) (d : Delta) (u : Upsilon) (g : Gamma) 
         (tau tau' : Tau) (e : E) (r : rtyp (D.ctxt beta k' d) u g e tau'),
       P1 beta k' d u g e tau' r -> 
       P beta k' d u g tau (e_s e) (styp_e_3_1 tau r)) ->
  (forall (beta : TVar) (k' : Kappa) (d : Delta) (u : Upsilon) (g : Gamma) 
          (tau : Tau) (e : E) (r : rtyp (D.ctxt beta k' d) u g e tau),
        P1 beta k' d u g e tau r -> 
        P beta k' d u g tau (retn e) (styp_return_3_2 r)) ->
  (forall (beta : TVar) (k' : Kappa) (d : Delta) (u : Upsilon) (g : Gamma) 
          (tau : Tau) (s1 s2 : St) (s : styp (D.ctxt beta k' d) u g tau s1),
        P beta k' d u g tau s1 s ->
        forall s0 : styp (D.ctxt beta k' d) u g tau s2,
        P beta k' d u g tau s2 s0 -> 
        P beta k' d u g tau (seq s1 s2) (styp_seq_3_3 s s0)) ->
  (forall (beta : TVar) (k' : Kappa) (d : Delta) (u : Upsilon) (g : Gamma) 
          (tau : Tau) (e : E) (s : St) (r : rtyp (D.ctxt beta k' d) u g e T.cint),
        P1 beta k' d u g e T.cint r ->
        forall s0 : styp (D.ctxt beta k' d) u g tau s,
        P beta k' d u g tau s s0 -> 
        P beta k' d u g tau (while e s) (styp_while_3_4 r s0)) ->
  (forall (beta : TVar) (k' : Kappa) (d : Delta) (u : Upsilon) (g : Gamma) 
          (tau : Tau) (e : E) (s1 s2 : St) (r : rtyp (D.ctxt beta k' d) u g e T.cint),
        P1 beta k' d u g e T.cint r ->
        forall s : styp (D.ctxt beta k' d) u g tau s1,
        P beta k' d u g tau s1 s ->
        forall s0 : styp (D.ctxt beta k' d) u g tau s2,
        P beta k' d u g tau s2 s0 -> 
        P beta k' d u g tau (if_s e s1 s2) (styp_if_3_5 r s s0)) ->
(* s0 wrong both ways *)
(* 
  (forall (beta : TVar) (k' : Kappa) (d : Delta) (u : Upsilon) (g : Gamma) 
          (x : EVar) (tau tau' : Tau) (s : St) (e : E)
          (e0 : G.map g x = None) (k : K d tau' A)
          (s0 : styp (D.ctxt beta k' d) u (G.ctxt x tau' g) tau s),
        P beta k' d u (G.ctxt x tau' g) tau s s0 ->
        forall r : rtyp (D.ctxt beta k' d) u g e tau',
        P1 beta k' d u g e tau' r ->
        P beta k' d u g tau (letx x e s) (styp_let_3_6 e0 k s0 r)) -> 
*)
  (forall (beta : TVar) (k' : Kappa) (d : Delta) (u : Upsilon) (g : Gamma) 
          (x : EVar) (p : Phi) (alpha : TVar) (k : Kappa) 
          (tau tau' : Tau) (s : St) (e : E) (e0 : D.map d alpha = None)
          (e1 : G.map g x = None) (k0 : K d tau A)
          (r : rtyp d u g e (T.etype p alpha k tau')),
        P1 beta k' d u g e (T.etype p alpha k tau') r ->
        forall s0 : styp (D.ctxt beta k' (D.ctxt alpha k d)) u (G.ctxt x tau' g) tau s,
        P beta k' (D.ctxt alpha k d) u (G.ctxt x tau' g) tau s s0 ->
        P beta k' d u g tau (open e alpha x s) (styp_open_3_7 e0 e1 k0 r s0)) ->
  (forall (beta : TVar) (k' : Kappa) (d : Delta) (u : Upsilon) (g : Gamma) 
          (x : EVar) (alpha : TVar) (k : Kappa) (tau tau' : Tau) 
          (s : St) (e : E) (r : rtyp (D.ctxt beta k' d) u g e (T.etype aliases alpha k tau')),
        P1 beta k' d u g e (T.etype aliases alpha k tau') r ->
        forall s0 : styp (D.ctxt alpha k d) u (G.ctxt x tau' g) tau s,
        P beta k' (D.ctxt alpha k d) u (G.ctxt x tau' g) tau s s0 ->
        forall (e0 : D.map d alpha = None) (e1 : G.map g x = None)
          (k0 : K d tau A),
        P beta k' d u g tau (openstar e alpha x s) (styp_openstar_3_8 r s0 e0 e1 k0)) ->
  (forall (beta : TVar) (k' : Kappa) (d : Delta) (g : Gamma) (u : Upsilon) 
          (x : EVar) (p : Path) (tau tau' : Tau) (e : G.map g x = Some tau')
          (g0 : gettype u x [] tau' p tau) (w : WFC d u g) 
          (k : K d tau' A), P0 beta k' d u g (p_e x p) tau (SL_3_1 e g0 w k)) ->
  (forall (beta : TVar) (k' : Kappa) (d : Delta) (u : Upsilon) (g : Gamma) 
          (e : E) (tau : Tau) (r : rtyp d u g e (T.ptype tau)),
        P1 beta k' d u g e (T.ptype tau) r ->
        forall k : K d tau A, P0 beta k' d u g (star e) tau (SL_3_2 r k)) ->
  (forall (beta : TVar) (k' : Kappa) (d : Delta) (u : Upsilon) (g : Gamma) 
          (e : E) (t0 t1 : Tau) (l : ltyp d u g e (T.cross t0 t1)),
        P0 beta k' d u g e (T.cross t0 t1) l ->
        P0 beta k' d u g (TM.dot e Pth.zero_pe) t0 (SL_3_3 l)) ->
  (forall (beta : TVar) (k' : Kappa) (d : Delta) (u : Upsilon) (g : Gamma) 
           (e : E) (t0 t1 : Tau) (l : ltyp d u g e (T.cross t0 t1)),
         P0 beta k' d u g e (T.cross t0 t1) l ->
         P0 beta k' d u g (TM.dot e Pth.one_pe) t1 (SL_3_4 l)) ->
  (forall (beta : TVar) (k' : Kappa) (d : Delta) (g : Gamma) (u : Upsilon) 
           (x : EVar) (p : Path) (tau tau' : Tau) (e : G.map g x = Some tau')
           (g0 : gettype u x [] tau' p tau) (k : K d tau' A) 
           (w : WFC d u g), P1 beta k' d u g (p_e x p) tau (SR_3_1 e g0 k w)) ->
  (forall (beta : TVar) (k' : Kappa) (e : E) (tau : Tau) (d : Delta) (u : Upsilon) 
           (g : Gamma) (r : rtyp d u g e (T.ptype tau)),
         P1 beta k' d u g e (T.ptype tau) r ->
         forall k : K d tau A, P1 beta k' d u g (TM.star e) tau (SR_3_2 r k)) ->
  (forall (beta : TVar) (k' : Kappa) (d : Delta) (u : Upsilon) (g : Gamma) 
           (e : E) (t0 t1 : Tau) (r : rtyp d u g e (T.cross t0 t1)),
         P1 beta k' d u g e (T.cross t0 t1) r ->
         P1 beta k' d u g (TM.dot e Pth.zero_pe) t0 (SR_3_3 r)) ->
  (forall (beta : TVar) (k' : Kappa) (d : Delta) (u : Upsilon) (g : Gamma) 
           (e : E) (t0 t1 : Tau) (r : rtyp d u g e (T.cross t0 t1)),
         P1 beta k' d u g e (T.cross t0 t1) r ->
         P1 beta k' d u g (TM.dot e Pth.one_pe) t1 (SR_3_4 r)) ->
  (forall (beta : TVar) (k' : Kappa) (d : Delta) (u : Upsilon) (g : Gamma) 
          (z : Z) (w : WFC d u g),
         P1 beta k' d u g (i_e (i_i z)) T.cint (SR_3_5 z w)) ->
  (forall (beta : TVar) (k' : Kappa) (d : Delta) (u : Upsilon) (g : Gamma) 
           (e : E) (tau : Tau) (l : ltyp d u g e tau),
         P0 beta k' d u g e tau l -> P1 beta k' d u g (amp e) (T.ptype tau) (SR_3_6 l)) ->
  (forall (beta : TVar) (k' : Kappa) (d : Delta) (u : Upsilon) (g : Gamma) 
           (e0 e1 : E) (t0 t1 : Tau) (r : rtyp d u g e0 t0),
         P1 beta k' d u g e0 t0 r ->
         forall r0 : rtyp d u g e1 t1,
         P1 beta k' d u g e1 t1 r0 ->
         P1 beta k' d u g (cpair e0 e1) (T.cross t0 t1) (SR_3_7 r r0)) ->
  (forall (beta : TVar) (k' : Kappa) (d : Delta) (u : Upsilon) (g : Gamma) 
           (e1 e2 : E) (tau : Tau) (l : ltyp d u g e1 tau),
         P0 beta k' d u g e1 tau l ->
         forall r : rtyp d u g e2 tau,
         P1 beta k' d u g e2 tau r ->
         forall a : ASGN d tau, P1 beta k' d u g (assign e1 e2) tau (SR_3_8 l r a)) ->
  (forall (beta : TVar) (k' : Kappa) (d : Delta) (u : Upsilon) (g : Gamma) 
           (e1 e2 : E) (tau tau' : Tau)
           (r : rtyp d u g e1 (T.arrow tau' tau)),
         P1 beta k' d u g e1 (T.arrow tau' tau) r ->
         forall r0 : rtyp d u g e2 tau',
         P1 beta k' d u g e2 tau' r0 -> 
         P1 beta k' d u g (TM.appl e1 e2) tau (SR_3_9 r r0)) ->
  (forall (beta : TVar) (k' : Kappa) (d : Delta) (u : Upsilon) (g : Gamma) 
           (tau : Tau) (s : St) (s0 : styp d u g tau s),
         P beta k' d u g tau s s0 ->
         forall r : ret s, P1 beta k' d u g (call s) tau (SR_3_10 s0 r)) ->
  (forall (beta : TVar) (k' : Kappa) (d : Delta) (u : Upsilon) (g : Gamma) 
           (e : E) (tau tau' : Tau) (alpha : TVar) 
           (k : Kappa) (r : rtyp d u g e (T.utype alpha k tau')),
         P1 beta k' d u g e (T.utype alpha k tau') r ->
         forall a : AK d tau k,
         P1 beta k' d u g (inst e tau) (subst_Tau tau' tau alpha) (SR_3_11 r a)) ->
  (forall (beta : TVar) (k' : Kappa) (d : Delta) (u : Upsilon) (g : Gamma) 
           (e : E) (tau tau' : Tau) (alpha : TVar) 
           (k : Kappa) (p : Phi)
           (r : rtyp d u g e (subst_Tau tau tau' alpha)),
         P1 beta k' d u g e (subst_Tau tau tau' alpha) r ->
         forall (a : AK d tau' k) (k0 : K d (T.etype p alpha k tau) A),
         P1 beta k' d u g (pack tau' e (T.etype p alpha k tau))
           (T.etype p alpha k tau) (SR_3_12 r a k0)) ->
  (forall (beta : TVar) (k' : Kappa) (d : Delta) (u : Upsilon) (g : Gamma) 
           (tau tau' : Tau) (s : St) (x : EVar) (e : G.map g x = None)
           (s0 : styp d u (G.ctxt x tau g) tau' s),
         P beta k' d u (G.ctxt x tau g) tau' s s0 ->
         forall r : ret s,
         P1 beta k' d u g (f_e (dfun tau x tau' s)) (T.arrow tau tau')
           (SR_3_13 e s0 r)) ->
  (forall (beta : TVar) (k' : Kappa) (d : Delta) (u : Upsilon) (g : Gamma) 
           (f24 : F) (tau : Tau) (alpha : TVar) (k : Kappa)
           (e : D.map d alpha = None) (w : WFC d u g)
           (r : rtyp (D.ctxt alpha k d) u g (f_e f24) tau),
         P1 beta k' (D.ctxt alpha k d) u g (f_e f24) tau r ->
         P1 beta k' d u g (f_e (ufun alpha k f24)) (T.utype alpha k tau)
           (SR_3_14 e w r)) ->
  forall (beta : TVar) (k' : Kappa) (d : Delta) (u : Upsilon) (g : Gamma) 
         (e : E) (t : Tau) (l : ltyp d u g e t), P0 beta k' d u g e t l.
Proof.
Admitted.
*)

(* Bug 42, getH *)

Inductive htyp: Upsilon -> Gamma -> Heap -> Gamma -> Prop :=
   | htyp_empty : forall (u : Upsilon) (g: Gamma),
                       htyp u g H.dot G.dot
   | htyp_xv    : forall (u : Upsilon) (g g': Gamma) (h h': Heap) (x : EVar) (v : E) (tau : Tau),
                      H.map h x = Some v ->
                      Value v ->
                      H.delete h x = h' ->
                      htyp u g h' g' ->
                      rtyp D.dot u g v tau ->
                      htyp u g h (G.ctxt x tau g').

(* Bug 43, HM.map *)
Inductive refp  : Heap -> Upsilon -> Prop :=
  | refp_empty  : forall (h : Heap),
                       refp h U.dot
  | refp_pack  : forall (h : Heap) (u : Upsilon) (x : EVar) (p : Path) (tau tau' : Tau) (alpha : TVar) (k : Kappa) (v v' : E),
                      H.map h x = Some v' -> 
                      get v' p (pack tau' v (etype aliases alpha k tau)) ->
                      refp h u ->
                      refp h (U.ctxt (x,p) tau' u).

Inductive prog  : Heap -> St -> Prop := 
  | program  : forall (h : Heap) (u : Upsilon) (g : Gamma) (tau : Tau) (s : St),
                    htyp u g h g ->
                    refp h u     ->
                    styp D.dot u g tau s ->
                    ret s -> 
                    prog h s.
