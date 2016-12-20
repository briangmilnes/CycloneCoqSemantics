(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

 This defines the static semantics of statements and expressions, pg. 63. 

*)
Set Implicit Arguments.
Require Export Cyclone_Formal_Syntax Cyclone_Static_Semantics_Typing_Heap_Objects.
Require Export Cyclone_LN_Env.
Import LibEnvNotations.
Import LVPE.LibVarPathEnvNotations.

(* TODO Not in the thesis. I need it and in K when the context is formed. *)
      
(* This is equivalent to OK from LibEnv. *)
Inductive WFD : Delta -> Prop :=
  | WFD_ddot   : WFD ddot
  | WFD_xtau   : forall (d : Delta) (alpha : var) (k : Kappa),
                 get alpha d = None ->
                 WFD  d ->
                 WFD (d & alpha ~ k).
Hint Constructors WFD.
Hint Extern 1 (WFD ddot) => unfold ddot.

Inductive K : Delta -> Tau -> Kappa -> Prop :=
 | K_cint   : forall (d : Delta),
                  K d cint B

 | K_B     : forall (d : Delta) (alpha : var),
              (* binds alpha B d -> *)
               get alpha d = Some B ->
               K d (ftvar alpha) B

 | K_star_A  : forall (d : Delta) (alpha : var),
                 (* binds  alpha A d -> *)
                  get alpha d = Some A -> 
                 K  d (ptype (ftvar alpha)) B

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

 | K_utype  : forall (L : vars) (d : Delta) (k : Kappa) (tau : Tau),
                (forall (alpha : var),
                   alpha \notin L ->
                   ok (d & alpha ~ k) ->
                   K  (d & alpha ~ k) (T.open_rec 0 (ftvar alpha) tau) A) ->
                K d (utype k tau) A

 | K_etype  : forall (L : vars) (d : Delta) (k : Kappa) (tau : Tau) (p : Phi),
              (forall (alpha : var),
                 alpha \notin L ->
                 ok (d & alpha ~ k) ->
                 K (d & alpha ~ k) (T.open_rec 0 (ftvar alpha) tau) A) ->
              K d (etype p k tau) A
                
 | K_B_A     : forall (d : Delta) (tau : Tau),
     K d tau B ->
     K d tau A.

Ltac K_constructors :=
  match goal with
   | H: K _ ?t B |- K _ ?t A => try apply K_B_A
   | |-  (K _ _ _)  => 
    try apply K_cint; try apply K_B; try apply K_star_A; try apply K_cross; 
    try apply K_arrow; try apply K_ptype
  end.
Hint Extern 3 (K _ _ _) => try K_constructors.

Inductive AK : Delta -> Tau -> Kappa -> Prop :=

 | AK_AK_K  : forall (d : Delta) (tau : Tau) (k : Kappa),
                   K  d tau k ->
                   AK d tau k

 | AK_A     : forall (d : Delta) (alpha : var),
                (* binds alpha A d -> *)
                get alpha d = Some A -> 
                AK d (ftvar alpha) A.

Hint Constructors AK.
Hint Extern 1 (AK ddot) => unfold ddot.

Inductive ASGN : Delta -> Tau -> Prop :=

  | ASGN_cint  : forall (d : Delta),
                      ASGN d cint

  | ASGN_B     : forall (d : Delta) (alpha : var),
                   (* binds alpha B d -> *)
                   get alpha d = Some B ->
                   ASGN d (ftvar alpha)

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

  | ASGN_utype : forall (L : vars) (d : Delta)  (k : Kappa) (tau : Tau),
                 (forall (alpha : var),
                     alpha \notin L ->
                   ASGN (d & alpha ~ k) (T.open_rec 0 (ftvar alpha) tau)) ->
                   ASGN d (utype k tau)

  | ASGN_etype : forall (L : vars) (d : Delta) (k : Kappa) (tau : Tau),
                 (forall (alpha : var),
                     alpha \notin L ->
                     ASGN (d & alpha ~ k) (T.open_rec 0 (ftvar alpha) tau)) ->
                   ASGN d (etype witnesschanges k tau).
Hint Constructors ASGN.
Hint Extern 1 (ASGN ddot) => unfold ddot.

Inductive WFU : Upsilon -> Prop :=
  | WFU_udot : WFU udot
  | WFU_A   : forall (u : Upsilon) (tau : Tau) (p : Path) (x : var),
                 LVPE.V.get (x,p) u = None ->
                 WFU  u ->
                 K ddot tau A ->
                 WFU (u &p ((x,p) ~p tau)).
Hint Constructors WFU.
Hint Extern 1 (WFU udot) => unfold udot.

Inductive WFDG : Delta -> Gamma -> Prop :=
  | WFDG_d_gdot : forall (d: Delta),
                     WFDG d gdot
  | WFDG_xt      : forall (d: Delta) (g: Gamma) (x : var) (tau : Tau),
                     get x g = None -> 
                     K d tau A ->
                     WFDG d g ->
                     WFDG d (g & (x ~ tau))
(* Proposed Thesis bug, I have to be able to extend WFDG with a new type variable. *)                          
  | WFDG_alphak   : forall (d: Delta) (g: Gamma) (alpha : var) (k : Kappa),
                     get alpha d = None -> 
                     WFDG d g ->
                     WFDG (d & (alpha ~ k)) g.

Hint Constructors WFDG.
Hint Extern 6 (WFDG _ _) => try apply WFDG_xt; auto.
Hint Extern 1 (WFDG ddot _) => unfold ddot.
Hint Extern 1 (WFDG _ gdot) => unfold gdot.

(* Thesis change, we really need to know that kinding contexts are unique,
   so we're adding it here. Another option is to add it inside WFDG. *)
Inductive WFC : Delta -> Upsilon -> Gamma -> Prop :=
  | WFC_DUG : forall (d : Delta) (g: Gamma) (u : Upsilon),
                ok d -> 
                WFDG d g ->
                LVPE.okp u ->
                WFC d u g.
Hint Constructors WFC.
Hint Extern 10 (WFC _ _ _) => try solve[constructor; auto].
Hint Extern 1  (WFC ddot _ _) => unfold ddot.
Hint Extern 1  (WFC _ udot _) => unfold udot.
Hint Extern 1  (WFC _ _ gdot) => unfold udot.

(* Automation for judgements with LN constructors. *)

Ltac fv_of_kinding_goal :=
  match goal with
    | |- K ?d (utype _ ?tau) _   => constr:((fv_delta d) \u  (T.fv tau))
    | |- K ?d (etype _ _ ?tau) _ => constr:((fv_delta d) \u  (T.fv tau))
    | |- ASGN ?d (utype _ ?tau)  => constr:((fv_delta d) \u  (T.fv tau))
    | |- ASGN ?d (etype _ _ ?tau)  => constr:((fv_delta d) \u  (T.fv tau))
    | |- ASGN ?d (etype _ _ ?tau)  => constr:((fv_delta d) \u  (T.fv tau))
  end.




