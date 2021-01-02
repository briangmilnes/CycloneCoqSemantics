/-
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Term Weakening 
-/

import .Cyclone_Static_Semantics_Kinding_And_Context_Well_Formedness

/- TODO It's not clear to me which way to order environments, add on the left here. -/

lemma ok_strength {K : Type} {V : Type} [decidable_eq K] (d : list (K × V)) (k : K) (v : V):
   ok d →
   binds k d = none → 
   ok ((k,v) :: d) :=
begin
  assume okd b,
  apply ok.notin,
  exact b,
  exact okd,
end

lemma ok_change_value {K : Type} {V : Type} [decidable_eq K] 
  (d : list (K × V)) (k : K) (v : V):
    ok ((k, v) :: d) →
    ∀ v' : V, 
      ok ((k, v') :: d) := 
begin
  intros okkvd v',
  induction' okkvd,
  apply ok.notin,
  exact h,
  exact okkvd,
end

lemma ok_pop {K : Type} {V : Type} [decidable_eq K] 
  (d : list (K × V)) (k : K) (v : V) :
    ok ((k,v) :: d) →
    binds k d = none := 
begin
  intros okkvd,
  induction' okkvd,
  exact h,
end
  
lemma ok_fresh {K : Type} {V : Type} [decidable_eq K] 
  (d : list (K × V)) (k : K) (v : V) :
    ok((k, v) :: d) →
    binds k d = none :=
begin
  intros, 
  induction' a,
  exact h,
end
