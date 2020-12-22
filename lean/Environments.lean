import .Cyclone_Formal_Syntax

/- This is the most general binds and ok that I can make, 
 involving an instance of a decidable type class that 
 Lean must find. None must have its full type in 
 some of these examples.
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

/- To hard, let's get some more lemmas. -/ 
lemma ok₃ : ok [("fred",1),("joe",2)] :=
begin
  apply ok.notin,
  unfold binds,
  cc,
  simp,
end
