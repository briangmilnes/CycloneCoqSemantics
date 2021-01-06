import .Cyclone_Formal_Syntax

/- 
 This is the most general binds and ok that I can make, 
 involving an instance of a decidable type class that 
 Lean must find and not functions but inductive properties.
 Unlike Coq functional induction is not in this Lean but it
 was difficult in Coq anyway.

 @[derive decideable_eq] made the few typeclasses we need for
 Path element lists.  
 Not sure what lemmas and meta programming we'll need for ok and binds. 
 Will have to see them in action in a theorem. 

 This is three definitions and supporting lemmas: binds, ok and extends.
-/

inductive binds {key : Type} [eq : decidable_eq key] {value : Type} : key → list (key × value) → option value → Prop 
| nil  : ∀ (k : key), binds k [] none
| eq   : ∀ (k k' : key) (v : value) (d' : list (key × value)),
           k = k' ->
           binds k ((k',v) :: d') (some v)
| ne  : ∀ (k k' : key) (v : value) (ov : option value) (d' : list (key × value)),
           k ≠ k' →
           binds k d' ov -> 
           binds k ((k',v) :: d') ov

@[simp] lemma binds_empty_is_none {key : Type} [eq : decidable_eq key] {value : Type}  (k : key) :
  binds k [] (@none value) := by apply binds.nil

@[simp] lemma binds_nil_not_some 
{key : Type} [eq : decidable_eq key] {value : Type}  
(k : key) (v : value) :
  ¬ binds k [] (some v) := 
begin
  intros n,
  cases n,
end

@[simp] lemma binds_some_first {key : Type} {value : Type} [eq : decidable_eq key] 
  (k : key) (v : value) (b : list (key × value)) :
  binds k ((k,v) :: b) (some v) := 
begin
 apply binds.eq,
 refl,
end
 
@[simp] lemma binds_none_first {key : Type} {value : Type} [eq : decidable_eq key] 
  (k k': key) (v : value) (b : list (key × value)) (ov : option value) :
  k ≠ k' →
  binds k b ov → 
  binds k ((k',v) :: b) ov :=
begin
 intros knek' bkbov, 
 apply binds.ne; assumption,
end

@[simp] lemma binds_cons_none_ne {key : Type} {value : Type} [eq : decidable_eq key] 
  (k k': key) (v : value) (b : list (key × value)) :
  binds k ((k',v) :: b) none →
  k ≠ k' :=
begin
  intros bkk'vnone,
  cases bkk'vnone,
  assumption
end 

/- Try addding a domain of an environment to decouple OK from binds. -/

inductive dom {key : Type} [eq : decidable_eq key] {value : Type} : 
list (key × value) → list key → Prop
| nil_nil : dom [] []
| nil_d : ∀ (d : list key), dom [] d
| e_d   : ∀ (k : key) (v : value) (e : list (key × value)) (d : list key), 
  dom ((k,v) :: e) d ->
  dom e (k :: d)

/- Ok i.e., no duplicate keys -/

inductive ok {key : Type} [eq : decidable_eq key] {value : Type} : list (key × value) → Prop
| empty : ok []
| notin : forall (k : key) (v : value) (d : list (key × value)), 
            binds k d none →
            ok d →
            ok ((k, v) :: d)

@[simp] lemma ok_empty {key : Type} [eq : decidable_eq key] {value : Type} :
  @ok key eq value [] :=
begin
  apply ok.empty,
end

@[simp] lemma ok_empty₂ {key : Type} [eq : decidable_eq key] {value : Type} :
  @ok key eq value [] := by simp

@[simp] lemma ok_singleton {key : Type} [eq : decidable_eq key] {value : Type} (k : key) (v : value):
  ok [(k,v)] :=
begin
  apply ok.notin,
  simp,
  simp,
end

@[simp] lemma ok_cdr {key : Type} [eq : decidable_eq key] {value : Type}
 (k : key) (v : value) (b : list (key × value)): 
  ok((k,v) :: b) -> ok b :=
begin
  intros okl,
  cases okl,
  assumption,
end 

@[simp] lemma ok_cons_binds_none_cdr
{key : Type} [eq : decidable_eq key] {value : Type}
(k : key) (v : value) (b : list (key × value)): 
  ok((k,v) :: b) -> binds k b none :=
begin
  intros okl,
  cases okl,
  assumption,
end 

/- extendedby d d' means d' extends d, i.e., has all its bindings. -/

inductive extendedby {key : Type} [eq : decidable_eq key] {value : Type}: 
  list (key × value) → list (key × value) → Prop
| nil_nil : extendedby [] []
| nil_d   : ∀ (d : list (key × value)), extendedby [] d
| binds   : ∀  (d d' : list (key × value)),
  (∀ (k : key) (v : value),
   (binds k d (some v) → binds k d' (some v)))
   -> extendedby d d'
    
@[simp] lemma binds_extendedby {key : Type} [eq : decidable_eq key] {value : Type}
      (k : key) (v : value) (d : list (key × value)) :
      binds k d (some v) →
      ∀ (d' : list (key × value)),
      extendedby d d' →
      binds k d' (some v) :=
begin
 intros bkdv d' extdd',
 induction' extdd',
 assumption,
 exfalso,
 apply binds_nil_not_some k v,
 assumption,
 apply (h k v),
 assumption,
end

@[simp] lemma ok_double_push {key : Type} {value : Type} [eq: decidable_eq key] 
  (k : key) (v v' : value) (b : list (key × value)) :
  ¬ ok ((k, v) :: (k, v') :: b) := 
begin
 intros h,
 cases h,
 cases h_a,
 cc,
end

@[simp] lemma binds_cons_none {key : Type} {value : Type} [eq: decidable_eq key] 
  (k k': key) (v : value) (b : list (key × value)) :  
binds k ((k', v) :: b) none →
binds k b none := 
begin
  intros x,
  cases x,
  assumption
end

@[simp] lemma binds_some_none_ne {key : Type} {value : Type} [eq: decidable_eq key] 
  (j k: key) (v : value) (b : list (key × value)) :
  ok b →
  binds j b (some v) →
  binds k b none →
  j ≠ k :=
begin
  intros okb jb kb,
  induction' jb,
  rw h,
  symmetry,
  apply binds_cons_none_ne k k' v b,
  assumption,
  apply ih,
  apply ok_cdr k' v_1 b; assumption,
  apply binds_cons_none k k' v_1 b,
  assumption,
end

@[simp] lemma binds_some_ok_ne 
 {key : Type} {value : Type} [eq: decidable_eq key] 
(j k: key) (x y: value) (b : list (key × value)) :
  binds j b (some x) →
  ok ((k, y) :: b) →
  j ≠ k :=
begin
  intros bjbx okkyb,
  let h: binds k b none,
    apply ok_cons_binds_none_cdr k y b,
    assumption,
    apply binds_some_none_ne j k x b,
    apply ok_cdr k y b,
    repeat {assumption},
end

@[simp] lemma binds_weakening {key : Type} {value : Type} [eq: decidable_eq key] 
  (j k: key) (x y z: value) (b : list (key × value)) :
   binds j b (some x) →
   ok ((k,y) :: b) →
   binds j ((k,z) :: b) (some x) :=
begin
  intros bjbsx okkyb,
  constructor; try {assumption},
  apply binds_some_ok_ne j k x y b; assumption,
end
