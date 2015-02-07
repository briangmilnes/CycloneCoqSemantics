(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

 This defines the static semantics of statements and expressions, pg. 63. 

*)
Set Implicit Arguments.
Require Export LanguageModuleDef.

(* TODO Not in the thesis. I need it and in K when the context is formed. *)
      
Inductive WFD : Delta -> Prop :=
  | WFD_nil    : WFD ddot
  | WFD_xtau   : forall (d : Delta) (alpha : TVar) (k : Kappa),
                 DM.map d alpha = None ->
                 WFD  d ->
                 WFD (dctxt alpha k d).

Inductive K : Delta -> Tau -> Kappa -> Prop :=

 | K_int   : forall (d : Delta),
                  K d cint B

 | K_B     : forall (d : Delta) (alpha : TVar),
               DM.map d alpha = Some B ->
               K d (tv_t alpha) B

 | K_star_A  : forall (d : Delta) (alpha : TVar),
                 DM.map d alpha = Some A -> 
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
                   WFD (dctxt alpha k d) ->
                   DM.map d alpha = None -> 
                   K  (dctxt alpha k d) tau A ->
                   K d (utype alpha k tau) A

 | K_etype  : forall (d : Delta) (alpha : TVar) (k : Kappa) (tau : Tau) (p : Phi),
                   WFD (dctxt alpha k d) ->
                   DM.map d alpha = None -> 
                   K (dctxt alpha k d) tau A ->
                   K d (etype p alpha k tau) A.


Inductive AK : Delta -> Tau -> Kappa -> Prop :=

 | AK_AK_K  : forall (d : Delta) (tau : Tau) (k : Kappa),
                   K  d tau k ->
                   AK d tau k

 | AK_A     : forall (d : Delta) (alpha : TVar),
                DM.map d alpha = Some A ->
                AK d (tv_t alpha) A.
                         
Inductive ASGN : Delta -> Tau -> Prop :=

  | ASGN_cint  : forall (d : Delta),
                      ASGN d cint

  | ASGN_B     : forall (d : Delta) (alpha : TVar),
                   DM.map d alpha = Some B ->
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
                   DM.map d alpha = None ->
                   ASGN (dctxt alpha k d) tau ->
                   ASGN d (utype alpha k tau)

  | ASGN_etype : forall (d : Delta) (alpha : TVar) (k : Kappa) (tau : Tau),
                   DM.map d alpha = None ->
                   ASGN (dctxt alpha k d) tau ->
                   ASGN d (etype witnesschanges alpha k tau).

Inductive WFU : Upsilon -> Prop :=
  | WFU_nil : WFU udot
  | WFU_A   : forall (u : Upsilon) (tau : Tau) (p : Path) (x : EVar),
                 UM.map u (x,p) = None ->
                 WFU  u ->
                 K ddot tau A ->
                 WFU (uctxt (x,p) tau u).

Inductive WFDG : Delta -> Gamma -> Prop :=
  | WFDG_d_nil : forall (d: Delta),
                     WFDG d gdot
  | WFDG_xt      : forall (d: Delta) (g: Gamma) (x : EVar) (tau : Tau),
                     GM.map g x = None -> 
                     K d tau A ->
                     WFDG d g ->
                     WFDG d (gctxt x tau g)
(* Proposed Thesis bug, I have to be able to extend WFDG with a new type variable. *)                          
  | WFDG_alphak   : forall (d: Delta) (g: Gamma) (alpha : TVar) (k : Kappa),
                     DM.map d alpha = None -> 
                     WFDG d g ->
                     WFDG (dctxt alpha k d) g.

(* Thesis change, we really need to know that kinding contexts are unique,
   so we're adding it here. Another option is to add it inside WFDG. *)
Inductive WFC : Delta -> Upsilon -> Gamma -> Prop :=
  | WFC_DUG : forall (d : Delta) (g: Gamma) (u : Upsilon),
                WFD d -> 
                WFDG d g ->
                WFU u ->
                WFC d u g.
