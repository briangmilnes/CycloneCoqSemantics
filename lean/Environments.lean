import .Cyclone_Formal_Syntax

/- 
 This is the most general binds and ok that I can make, 
 involving an instance of a decidable type class that 
 Lean must find. 
 So I'll need typeclasses and instances to make this work.
 Do I want this that general or as in the coq model with different specializations.
 Not sure what lemmas and meta programming we'll need for ok and binds. 
 Will have to see them in action in a theorem. 

-/

def binds {key : Type} [eq : decidable_eq key] {value : Type} : key → list (key × value) → option value
| _ [] := none
| v ((v',a) :: r) := if v = v' then some a else binds v r

@[simp] lemma binds_empty_is_none {key : Type} {value : Type} [eq : decidable_eq key] (k : key) :
  @binds key eq value k [] = @none value := by refl

lemma binds_empty_is_none₂ {key : Type} {value : Type} [eq : decidable_eq key] (k : key) :
  binds k [] = @none value := by simp 

@[simp] lemma binds_some_first {key : Type} {value : Type} [eq : decidable_eq key] (k : key) (v : value) (b : list (key × value)) :
  binds k ((k,v) :: b) = some v :=
begin
 unfold binds,
 cc,
end
 
@[simp] lemma binds_none_first {key : Type} {value : Type} [eq : decidable_eq key] (k k': key) (v : value) (b : list (key × value)) :
  k ≠ k' →
  binds k ((k',v) :: b) = binds k b := 
begin
 intros vnev',
 unfold binds,
 cc,
end

lemma binds_string_none {value : Type}: 
 binds "fred" [] = @none value := 
begin
  simp,
end 

/- Check which binds's can find a type instance, they all work with
 a simple @[derive decidable_eq]

lemma binds_Heap_some (v : Var) (h : Heap) (e : E) :
   binds v h = some e := 
sorrycharlie

lemma binds_Heap_none (v : Var) (h : Heap):
   binds v h = none := 
sorrycharlie

lemma binds_Delta_some (v : Var) (d : Delta) (k : Kappa) :
   binds v d = some k := 
sorrycharlie

lemma binds_Delta_none (v : Var) (d : Delta) :
   binds v d = none := 
sorrycharlie

lemma binds_Gamma_some (v : Var) (g : Gamma) (t : Tau) : 
   binds v g = some t := 
sorrycharlie

lemma binds_Gamma_none (v : Var) (g : Gamma) : 
   binds v g = none := 
sorrycharlie

lemma binds_Upsilon_some (v : Var) (p : Path) (u : Upsilon) (t : Tau) : 
   binds (v,p) u = some t := 
sorrycharlie

lemma binds_Upsilon_none (v : Var) (p : Path) (u : Upsilon) : 
   binds (v,p) u = none := 
sorrycharlie
-/

/- Evals don't work as you can't print a prop. -/

#check binds "fred" [] = @none string

inductive ok {key : Type} [eq : decidable_eq key] {value : Type} : list (key × value) → Prop
| empty {} : ok []
| notin : forall (k : key) (v : value) (d : list (key × value)), 
            binds k d = none →
            ok d →
            ok ((k, v) :: d)

@[simp] lemma ok_empty {key : Type} [eq : decidable_eq key] {value : Type} :
  @ok key eq value [] :=
begin
  apply ok.empty,
end

lemma ok_empty₂ {key : Type} [eq : decidable_eq key] {value : Type} :
  @ok key eq value [] := by simp

@[simp] lemma ok_singleton {key : Type} [eq : decidable_eq key] {value : Type} (k : key) (v : value):
  ok [(k,v)] :=
begin
  apply ok.notin,
  simp,
  simp,
end

lemma ok₂ : ok [("fred",1)] := by simp 

lemma not_ok₂ : ¬ ok [("fred",1),("fred",2)] :=
begin
 intros n,
 induction' n,
 induction' h,
end

/- Too hard, let's get some more lemmas. -/ 
lemma ok₃ : ok [("fred",1),("joe",2)] :=
begin
  apply ok.notin,
  unfold binds,
  cc,
  simp,
end


/- Check which ok's can find a type instance, they all work with
 a simple @[derive decidable_eq].
-/
-- lemma ok_Heap (h : Heap) :
--    ok h := 
-- sorrycharlie
-- 
-- lemma ok_Delta (d : Delta) :
--   ok d :=
-- sorrycharlie
-- 
-- lemma ok_Gamma (g : Gamma) :
--  ok g  :=
-- sorrycharlie 
--
-- lemma ok_Upsilon (u : Upsilon) :
--  ok u :=
-- sorrycharlie




