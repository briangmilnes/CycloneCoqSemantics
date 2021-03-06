/-
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

 This defines the static semantics of statements and expressions, pg. 63. 
-/

import .Cyclone_Formal_Syntax
import .Environments

/- This is nothing but ok. -/
inductive WFD : Delta → Prop
| empty : WFD []
| xtau   : ∀ (d : Delta) (alpha : Var) (k : Kappa),
            binds alpha d none →
            ok d →
            WFD  d →
            WFD ((alpha, k) :: d)

@[simp] lemma WFD_empty : 
  WFD [] := 
begin
  apply WFD.empty,
end

lemma WFD_empty₂ : WFD [] :=
begin
 simp, 
end

inductive K : Delta → Tau -> Kappa → Prop
 | cint   : ∀ (d : Delta), K d cint B
 | B      : ∀ (alpha : Var) (d : Delta),
               binds alpha d (some B) →
               K d (ftvar alpha) B
 | star_A  : ∀ (alpha : Var) (d : Delta), 
                 binds alpha d (some A) → 
                 K  d (ptype (ftvar alpha)) B
 | cross   : ∀ (d : Delta) (t0 t1 : Tau),
                    K d t0 A →
                    K d t1 A →
                    K d (cross t0 t1) A
 | arrow   : ∀ (d : Delta) (t0 t1 : Tau),
                    K d t0 A →
                    K d t1 A →
                    K d (arrow t0 t1) A

 | ptype   : ∀ (d : Delta) (tau : Tau),
                    K d tau A →
                    K d (ptype tau) B

 | B_A     : ∀ (d : Delta) (tau : Tau),
              K d tau B →
              K d tau A
/-
 | utype  : forall (L : set Var) (d : Delta) (k : Kappa) (tau : Tau),
            (forall (alpha : Var),
              ¬ has_mem alpha L →
              ok (d ++ [(alpha, k)]) →
              K (d ++ [(alpha, k)]) (T.open_rec 0 (ftvar alpha) tau) A) →
              K d (utype k tau) A
 | etype  : forall (L : set Var) (d : Delta) (k : Kappa) (tau : Tau) (p : Phi),
              (forall (alpha : Var),
              ¬ has_mem alpha L →
                ok (d & alpha ~ k) →
                K (d & alpha ~ k) (T.open_rec 0 (ftvar alpha) tau) A) →
              K d (etype p k tau) A
-/



inductive AK : Delta → Tau → Kappa → Prop
 | AAK  : ∀ (d : Delta) (tau : Tau) (k : Kappa),
           K  d tau k →
           AK d tau k
 | AA   : ∀ (d : Delta) (alpha : Var),
           binds alpha d (some A) → 
           AK d (ftvar alpha) A

inductive ASGN : Delta → Tau → Prop
  | ASGN_cint  : ∀ (d : Delta),
                      ASGN d cint
  | ASGN_B     : ∀ (d : Delta) (alpha : Var),
                   binds alpha d (some B) →
                   ASGN d (ftvar alpha)
  | ASGN_ptype : ∀ (d : Delta) (tau : Tau),
                   ASGN d (ptype tau)
  | ASGN_cross : ∀ (d : Delta) (t0 t1 : Tau),
                   ASGN d t0 → 
                   ASGN d t1 → 
                   ASGN d (cross t0 t1)
  | ASGN_arrow : ∀ (d : Delta) (t0 t1 : Tau),
                   ASGN d t0 → 
                   ASGN d t1 → 
                   ASGN d (arrow t0 t1)
/-
  | ASGN_utype : ∀ (L : Vars) (d : Delta)  (k : Kappa) (tau : Tau),
                 (∀ (alpha : Var),
                   alpha \notin L →
                   ASGN (d & alpha ~ k) (T.open_rec 0 (ftvar alpha) tau)) →
                   ASGN d (utype k tau)

  | ASGN_etype : ∀ (L : Vars) (d : Delta) (k : Kappa) (tau : Tau),
                 (∀ (alpha : Var),
                   alpha \notin L →
                   ASGN (d & alpha ~ k) (T.open_rec 0 (ftvar alpha) tau)) →
                   ASGN d (etype witnesschanges k tau)
-/

inductive WFU : Upsilon → Prop 
  | empty : WFU []
  | A   : ∀ (u : Upsilon) (tau : Tau) (p : Path) (x : Var),
           ok u →
           binds (x,p) u none →
           WFU  u →
           K [] tau A →
           WFU (((x,p),tau) :: u)

inductive WFDG : Delta → Gamma → Prop 
  | d_empty : ∀ (d: Delta),
                     ok d →
                     WFDG d []
  | xt      : ∀ (d: Delta) (g: Gamma) (x : Var) (tau : Tau),
                     ok g →
                     ok d →
                     binds x g none → 
                     K d tau A →
                     WFDG d g →
                     WFDG d ((x, tau) :: g)

inductive WFC : Delta → Upsilon → Gamma → Prop 
  | DUG : ∀ (d : Delta) (g: Gamma) (u : Upsilon),
                WFDG d g →
                WFU u →
                WFC d u g
