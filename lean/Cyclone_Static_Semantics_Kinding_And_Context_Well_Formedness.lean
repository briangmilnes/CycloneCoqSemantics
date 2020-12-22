/- 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

 This defines the static semantics of statements and expressions, pg. 63. 
-/

import .Cyclone_Formal_Syntax
import .Environments

inductive WFD : list (string × Kappa) → Prop
| empty : WFD []
| xtau   : forall (d : list (string × Kappa)) (alpha : string) (k : Kappa),
            binds alpha d = none →
            ok d →
            WFD  d →
            WFD (d ++ [(alpha, k)])

@[simp] lemma WFD_empty : 
  WFD [] := 
begin
  apply WFD.empty,
end 

lemma WFD_empty₂ : WFD [] :=
begin
 simp, 
end

inductive K : list (string × Kappa) → Tau → Kappa → Prop 
 | cint   : forall (d : list (string × Kappa)), K d cint B
 | B      : forall (alpha : string) (d : list (string × Kappa)),
               binds alpha d = some B →
               K d (ftvar alpha) B
 | star_A  : forall (alpha : string) (d : list (string × Kappa)), 
                 binds alpha d = some A → 
                 K  d (ptype (ftvar alpha)) B
 | cross   : forall (d : list (string × Kappa)) (t0 t1 : Tau),
                    K d t0 A →
                    K d t1 A →
                    K d (cross t0 t1) A
 | arrow   : forall (d : list (string × Kappa)) (t0 t1 : Tau),
                    K d t0 A →
                    K d t1 A →
                    K d (arrow t0 t1) A

 | ptype   : forall (d : list (string × Kappa)) (tau : Tau),
                    K d tau A →
                    K d (ptype tau) B
/-
 | utype  : forall (L : set string) (d : list (string × Kappa)) (k : Kappa) (tau : Tau),
            (forall (alpha : string),
              ¬ has_mem alpha L →
              ok (d :: [(alpha, k)]) →
              K (d :: (alpha, k)) (T.open_rec 0 (ftvar alpha) tau) A) →
              K d (utype k tau) A
 | etype  : forall (L : set string) (d : list (string × Kappa)) (k : Kappa) (tau : Tau) (p : Phi),
              (forall (alpha : string),
              ¬ has_mem alpha L →
                ok (d & alpha ~ k) →
                K (d & alpha ~ k) (T.open_rec 0 (ftvar alpha) tau) A) →
              K d (etype p k tau) A
-/
 | B_A     : forall (d : list (string × Kappa)) (tau : Tau),
              K d tau B →
              K d tau A

inductive AK : list (string × Kappa) → Tau → Kappa → Prop
 | AAK  : forall (d : list (string × Kappa)) (tau : Tau) (k : Kappa),
           K  d tau k →
           AK d tau k
 | AA   : forall (d : list (string × Kappa)) (alpha : string),
           binds alpha d = some A → 
           AK d (ftvar alpha) A

inductive ASGN : list (string × Kappa) → Tau → Prop
  | ASGN_cint  : forall (d : list (string × Kappa)),
                      ASGN d cint
  | ASGN_B     : forall (d : list (string × Kappa)) (alpha : string),
                   binds alpha d = some B →
                   ASGN d (ftvar alpha)
  | ASGN_ptype : forall (d : list (string × Kappa)) (tau : Tau),
                   ASGN d (ptype tau)
  | ASGN_cross : forall (d : list (string × Kappa)) (t0 t1 : Tau),
                   ASGN d t0 → 
                   ASGN d t1 → 
                   ASGN d (cross t0 t1)
  | ASGN_arrow : forall (d : list (string × Kappa)) (t0 t1 : Tau),
                   ASGN d t0 → 
                   ASGN d t1 → 
                   ASGN d (arrow t0 t1)
/-
  | ASGN_utype : forall (L : strings) (d : list (string × Kappa))  (k : Kappa) (tau : Tau),
                 (forall (alpha : string),
                     alpha \notin L →
                   ASGN (d & alpha ~ k) (T.open_rec 0 (ftvar alpha) tau)) →
                   ASGN d (utype k tau)

  | ASGN_etype : forall (L : strings) (d : list (string × Kappa)) (k : Kappa) (tau : Tau),
                 (forall (alpha : string),
                     alpha \notin L →
                     ASGN (d & alpha ~ k) (T.open_rec 0 (ftvar alpha) tau)) →
                   ASGN d (etype witnesschanges k tau)
-/

inductive WFU : list ((string × list PE) × Tau) → Prop 
  | empty : WFU []
  | A   : forall (u : list ((string × list PE) × Tau)) (tau : Tau) (p : list PE) (x : string),
           ok u →
           binds (x,p) u = none →
           WFU  u →
           K [] tau A →
           WFU (u ++ [((x,p),tau)])

inductive WFDG : list (string × Kappa) → list (string × Tau) → Prop 
  | d_empty : forall (d: list (string × Kappa)),
                     ok d →
                     WFDG d []
  | xt      : forall (d: list (string × Kappa)) (g: list (string × Tau)) (x : string) (tau : Tau),
                     ok g →
                     ok d →
                     binds x g = none → 
                     K d tau A →
                     WFDG d g →
                     WFDG d (g ++ [(x, tau)])

inductive WFC : list (string × Kappa) → list Tau → list (string × Tau) → Prop 
  | DUG : forall (d : list (string × Kappa)) (g: list (string × Tau)) (u : list Tau),
                WFDG d g →
                WFU u →
                WFC d u g
-/
