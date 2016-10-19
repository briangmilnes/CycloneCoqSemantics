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

Inductive K : Delta -> Tau -> Kappa -> Prop :=

 | K_int   : forall (d : Delta),
                  K d cint B

 | K_B     : forall (d : Delta) (alpha : TVar),
                  K (d ++ [(alpha, B)]) (tv_t alpha) B

 | K_star_A  : forall (d : Delta) (alpha : TVar),
                  K  (d ++ [(alpha, A)]) (ptype (tv_t alpha)) B

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

 | K_A_B    :  forall (d : Delta) (tau : Tau),
                    K d tau A ->
                    K d (ptype tau) B

 | K_utype  : forall (d : Delta) (alpha : TVar) (k : Kappa) (tau : Tau),
                   K (d ++ [(alpha, k)]) tau A ->
                   getD d alpha = None -> 
                   K d (utype alpha k tau) A

 | K_etype  : forall (d : Delta) (alpha : TVar) (k : Kappa) (tau : Tau) (p : Phi),
                   getD d alpha = None -> 
                   K (d ++ [(alpha, k)]) tau A ->
                   K d (etype p alpha k tau) A.

Inductive AK : Delta -> Tau -> Kappa -> Prop :=

 | AK_K_AK  : forall (d : Delta) (tau : Tau) (k : Kappa),
                   K  d tau k ->
                   AK d tau k

 | AK_A     : forall (d : Delta) (alpha : TVar),
                   AK d (tv_t alpha) A.
                         
Inductive ASGN : Delta -> Tau -> Prop :=

  | ASGN_cint  : forall (d : Delta),
                      ASGN d cint

  | ASGN_B     : forall (d : Delta) (alpha : TVar),
                      ASGN (d ++ [(alpha, B)]) (tv_t alpha)

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
                      ASGN (d ++ [(alpha, k)]) tau ->
                      ASGN d (utype alpha k tau)

  | ASGN_etype : forall (d : Delta) (alpha : TVar) (k : Kappa) (tau : Tau),
                      ASGN (d ++ [(alpha, k)]) tau ->
                      ASGN d (etype nowitnesschange alpha k tau).

Inductive WFDG : Delta -> Gamma -> Prop :=
  | WFDG_d_nil : forall (d: Delta),
                     WFDG d nil
  | WFDG_xt      : forall (d: Delta) (g: Gamma) (x : EVar) (tau : Tau),
                     K d tau A ->
                     WFDG d g ->
                     WFDG d (g ++ [(x,tau)]).

Inductive WFU : Upsilon -> Prop :=
  | WFU_nil : WFU nil
  | WFU_A   : forall (u : Upsilon) (tau : Tau) (p : P) (x : EVar),
                 WFU  u ->
                 K nil tau A ->
                 WFU (u ++ [(p_e x p, tau)]).

Inductive WFC : Delta -> Upsilon -> Gamma -> Prop :=
  | WFC_DGU : forall (d : Delta) (g: Gamma) (u : Upsilon),
                WFDG d g ->
                WFU u ->
                WFC d u g.
