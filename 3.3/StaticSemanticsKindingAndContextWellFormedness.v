(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

 This defines the static semantics of statements and expressions, pg. 63. 

*)
Set Implicit Arguments.
Require Export LanguageModuleDef.

(* TODO Not in the thesis. I need it and in K when the context is formed. *)
      
Inductive WFD : Delta -> Prop :=
  | WFD_nil    : WFD D.dot
  | WFD_xtau   : forall (d : Delta) (alpha : TVar) (k : Kappa),
                 D.map d alpha = None ->
                 WFD  d ->
                 WFD (D.ctxt alpha k d).

Inductive K : Delta -> Tau -> Kappa -> Prop :=

 | K_int   : forall (d : Delta),
                  K d cint B

 | K_B     : forall (d : Delta) (alpha : TVar),
               D.map d alpha = Some B ->
               K d (tv_t alpha) B

 | K_star_A  : forall (d : Delta) (alpha : TVar),
                 D.map d alpha = Some A -> 
                 K  d (ptype (tv_t alpha)) B

 | K_B_A     : forall (d : Delta) (tau : Tau),
                  K  d tau B ->
                  K  d tau A

 | K_cross   : forall (d : Delta) (t0 t1 : Tau),
                    K d t0 A ->
                    K d t1 A ->
                    K d (cross t0 t1) A

 | K_arrow   : forall (d : Delta) (t0 t1 : Tau),
                    K d t0 A ->
                    K d t1 A ->
                    K d (arrow t0 t1) A

 | K_ptype    :  forall (d : Delta) (tau : Tau),
                    K d tau A ->
                    K d (ptype tau) B

 | K_utype  : forall (d : Delta) (alpha : TVar) (k : Kappa) (tau : Tau),
                   WFD (D.ctxt alpha k d) ->
                   D.map d alpha = None -> 
                   K  (D.ctxt alpha k d) tau A ->
                   K d (utype alpha k tau) A

 | K_etype  : forall (d : Delta) (alpha : TVar) (k : Kappa) (tau : Tau) (p : Phi),
                   WFD (D.ctxt alpha k d) ->
                   D.map d alpha = None -> 
                   K (D.ctxt alpha k d) tau A ->
                   K d (etype p alpha k tau) A.


(* This unproven lemma is used to do induction on terms of the form K
 (D.ctxt alpha k d) tau k' as higher order unification is undecidable
 and Coq thusly can't do this. Hopefully, this does it and correctly. *)

Lemma K_context_dependent_induction:
  forall P : TVar -> Kappa -> Delta -> Tau -> Kappa -> Prop,
    (* K_int *)
    (forall alpha k d, P alpha k d cint B) ->
    (* K_B *)
    (forall (alpha a': TVar) (k k': Kappa) (d : Delta) (tau : Tau),
        D.map (D.ctxt alpha k d) a' = Some B -> 
        P alpha k d (tv_t a') B) ->
    (* K_star *) 
    (forall (d : Delta) (alpha : TVar) (k : Kappa),
        D.map (D.ctxt alpha k d) alpha = Some A -> 
        P alpha k d (ptype (tv_t alpha)) B) -> 
    (* K_B_A ? *)
    (forall alpha k (d : Delta) (tau : Tau), 
            K (D.ctxt alpha k d) tau B -> 
            P alpha k d tau B ->
            P alpha k d tau A) ->
    (* K_cross *)
    (forall (alpha : TVar) (k : Kappa) (d : Delta) (t0 t1 : Tau),
        K (D.ctxt alpha k d) t0 A -> 
        P alpha k d t0 A -> 
        K (D.ctxt alpha k d) t1 A -> 
        P alpha k d t1 A -> 
        P alpha k d (cross t0 t1) A) -> 
    (* K_arrow *)
    (forall (alpha : TVar) (k : Kappa) (d : Delta) (t0 t1 : Tau),
        K (D.ctxt alpha k d) t0 A -> 
        P alpha k d t0 A -> 
        K (D.ctxt alpha k d) t1 A -> 
        P alpha k d t1 A -> 
        P alpha k d (arrow t0 t1) A) -> 
    (* K_ptype *)
    (forall (alpha : TVar) (k : Kappa) (d : Delta) (tau : Tau),
        K (D.ctxt alpha k d) tau A ->
        P alpha k d tau A -> 
        P alpha k d (ptype tau) B) ->
    (* K_utype *)
    (forall (d : Delta) (alpha a' : TVar) (k k': Kappa) (tau : Tau),
        D.map d alpha = None ->
        K (D.ctxt alpha k d) tau A ->
        P alpha k d tau A -> 
        P alpha k d (utype a' k tau) A) ->
    (* K_etype *)
    (forall (d : Delta) (alpha a' : TVar) (k : Kappa) (tau : Tau) (p : Phi),
        WFD (D.ctxt alpha k d) ->
        D.map d alpha = None ->
        K (D.ctxt alpha k d) tau A ->
        P alpha k d tau A -> 
        P alpha k d (etype p a' k tau) A) ->
    (forall (alpha : TVar) (k : Kappa) (d : Delta) (tau : Tau) (k' : Kappa),
      P alpha k d tau k').
Proof.
Admitted.


Inductive AK : Delta -> Tau -> Kappa -> Prop :=

 | AK_AK_K  : forall (d : Delta) (tau : Tau) (k : Kappa),
                   K  d tau k ->
                   AK d tau k

 | AK_A     : forall (d : Delta) (alpha : TVar),
                D.map d alpha = Some A ->
                AK d (tv_t alpha) A.

Lemma AK_context_induction_dependent:
  forall P: TVar -> Kappa -> Delta -> Tau -> Kappa -> Prop,
    (forall (alpha : TVar) (d : Delta) (tau : Tau) (k k': Kappa), 
           K d tau k -> P alpha k' d tau k) ->
  (forall (d : Delta) (alpha a': TVar) (k : Kappa),
     D.map (D.ctxt alpha k d) a' = Some A -> 
     P alpha k d (tv_t a') A) ->
  (forall (alpha : TVar) (k : Kappa) (d : Delta) (tau : Tau) (k' : Kappa),
      P alpha k d tau k').
Proof.
Admitted.

Inductive ASGN : Delta -> Tau -> Prop :=

  | ASGN_cint  : forall (d : Delta),
                      ASGN d cint

  | ASGN_B     : forall (d : Delta) (alpha : TVar),
                   D.map d alpha = Some B ->
                   ASGN d (tv_t alpha)

  | ASGN_ptype : forall (d : Delta) (tau : Tau),
                   ASGN d (ptype tau)

  | ASGN_cross : forall (d : Delta) (t0 t1 : Tau),
                   ASGN d t0 -> 
                   ASGN d t1 -> 
                   ASGN d (cross t0 t1)

  | ASGN_arrow : forall (d : Delta) (t0 t1 : Tau),
                   ASGN d t0 -> 
                   ASGN d t1 -> 
                   ASGN d (arrow t0 t1)

  | ASGN_utype : forall (d : Delta) (alpha : TVar) (k : Kappa) (tau : Tau),
                   D.map d alpha = None ->
                   ASGN (D.ctxt alpha k d) tau ->
                   ASGN d (utype alpha k tau)

  | ASGN_etype : forall (d : Delta) (alpha : TVar) (k : Kappa) (tau : Tau),
                   D.map d alpha = None ->
                   ASGN (D.ctxt alpha k d) tau ->
                   ASGN d (etype witnesschanges alpha k tau).

Lemma ASGN_context_induction_dependent:
  forall P : TVar -> Kappa -> Delta -> Tau -> Prop,
  (* ASGN_cint *)
  (forall (beta : TVar) (k : Kappa) (d : Delta), 
     P beta k d cint) ->
  (* ASGN_B *)
  ( forall (beta : TVar) (k : Kappa) (d : Delta) (alpha : TVar),
      D.map d alpha = Some B -> 
      P beta k d (tv_t alpha)) ->
  (* ASGN_ptype *)
  (forall (beta : TVar) (k : Kappa) (d : Delta) (tau : Tau), 
     P beta k d (ptype tau)) ->
  (* ASGN_cross *)
  (forall (beta : TVar) (k : Kappa) (d : Delta) (t0 t1 : Tau),
     ASGN d t0 -> 
     P beta k d t0 -> 
     ASGN d t1 -> 
     P beta k d t1 -> 
     P beta k d (cross t0 t1)) ->
  (* ASGN_arrow *)
  ( forall (beta : TVar) (k : Kappa) (d : Delta) (t0 t1 : Tau),
      ASGN d t0 -> 
      P beta k d t0 -> 
      ASGN d t1 -> 
      P beta k d t1 -> 
      P beta k d (arrow t0 t1)) ->
  (* ASGN_utype *)
  (forall (beta : TVar) (k : Kappa) (d : Delta) (alpha : TVar) (k : Kappa) (tau : Tau),
     D.map d alpha = None ->
     ASGN (D.ctxt alpha k d) tau ->
     P beta k (D.ctxt alpha k d) tau -> 
     P beta k d (utype alpha k tau)) ->
  (* ASGN_etype *)
  (forall (beta : TVar) (k: Kappa) (d : Delta) (alpha : TVar) (k : Kappa) (tau : Tau),
     D.map d alpha = None ->
     ASGN (D.ctxt alpha k d) tau ->
     P beta k (D.ctxt alpha k d) tau -> 
     P beta k d (etype witnesschanges alpha k tau)) ->
  (forall (beta : TVar) (k: Kappa) (d : Delta) (tau : Tau),
         P beta k d tau).
Proof.
Admitted.


Inductive WFU : Upsilon -> Prop :=
  | WFU_nil : WFU U.dot
  | WFU_A   : forall (u : Upsilon) (tau : Tau) (p : Path) (x : EVar),
                 U.map u (x,p) = None ->
                 WFU  u ->
                 K D.dot tau A ->
                 WFU (U.ctxt (x,p) tau u).

Inductive WFDG : Delta -> Gamma -> Prop :=
  | WFDG_d_nil : forall (d: Delta),
                     WFDG d G.dot
  | WFDG_xt      : forall (d: Delta) (g: Gamma) (x : EVar) (tau : Tau),
                     G.map g x = None -> 
                     K d tau A ->
                     WFDG d g ->
                     WFDG d (G.ctxt x tau g)
(* Proposed Thesis bug, I have to be able to extend WFDG with a new type variable. *)                          
  | WFDG_alphak   : forall (d: Delta) (g: Gamma) (alpha : TVar) (k : Kappa),
                     D.map d alpha = None -> 
                     WFDG d g ->
                     WFDG (D.ctxt alpha k d) g.

Lemma WFDG_context_dependent_induction:
  forall P : TVar -> Kappa -> Delta -> Gamma -> Prop, 
    (* WFDG_d_nil *)
    (forall  (beta : TVar) (k : Kappa) (d : Delta), 
       P beta k d G.dot) -> 
    (* WFDG_xt *)
    (forall (beta : TVar) (k : Kappa) (d : Delta) (g : Gamma) (x : EVar) (tau : Tau),
        G.map g x = None ->
        K (D.ctxt beta k d) tau A -> 
        WFDG (D.ctxt beta k d) g -> 
        P beta k d g -> 
        P beta k d (G.ctxt x tau g)) ->
    (* WFDG_alphak *)
    (forall  (beta : TVar) (k : Kappa) (d : Delta) (g : Gamma) (alpha : TVar) (k : Kappa),
        D.map (D.ctxt beta k d) alpha = None -> 
        WFDG (D.ctxt beta k d) g -> 
        P beta k d g -> 
        P beta k (D.ctxt alpha k d) g) ->
    (forall (beta : TVar) (k : Kappa) (d : Delta) (g: Gamma) (tau : Tau),
         P beta k d g).
Proof.
Admitted.

(* Thesis change, we really need to know that kinding contexts are unique,
   so we're adding it here. Another option is to add it inside WFDG. *)
Inductive WFC : Delta -> Upsilon -> Gamma -> Prop :=
  | WFC_DUG : forall (d : Delta) (g: Gamma) (u : Upsilon),
                WFD d -> 
                WFDG d g ->
                WFU u ->
                WFC d u g.
