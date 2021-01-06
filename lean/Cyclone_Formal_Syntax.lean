/- Rewriting the Coq Cyclone Formal Syntax in Lean. -/

import .LeanLib

/- TODO Lean 4 has enumerations, should I be using it? -/

inductive Kappa : Type
| B    /- 'boxed' kind. -/ 
| A    /- 'any'   kind. -/
export Kappa

inductive Phi : Type
| witnesschanges /- Allowing witness changes. \delta -/
| aliases        /- Allowing aliases as the opened type. \amp -/ 

export Phi

/- Path elements -/
@[derive decidable_eq]
inductive IPE: Type
| zero_pe    
| one_pe
export IPE

@[derive decidable_eq]
inductive PE : Type 
| i_pe      : IPE → PE
| u_pe      : PE

export PE 

notation `Var`     := string

inductive V : Type
| bevar : nat → V     /- A bound expression variable, a de Bruijn index. -/
| fevar : Var → V  /- A free expression variable. -/

export V

inductive Tau : Type
 | btvar  : nat → Tau                /- A bound type variable, a de Bruijn index. -/
 | ftvar  : Var → Tau                /- A free type variable. -/
 | cint   : Tau                      /- Cyclone's Integers. -/
 | cross  : Tau → Tau → Tau          /- Pairs. -/
 | arrow  : Tau → Tau → Tau          /- Function    type. -/
 | ptype  : Tau → Tau                /- Pointer     type. -/
/-
 | utype  : Kappa → Tau → Tau        /- Universal   type. -/
 | etype  : Phi → Kappa → Tau → Tau  /- Existential type. -/
-/
export Tau

mutual inductive St, E, F
with St : Type 
 | e_s       : E   → St              /- An expression in a statement. -/
 | retn      : E   → St              /- Returns are required in this syntax. -/
 | seqx      : St  → St → St         /- Statement sequencing. -/
 | if_s      : E   → St → St   → St  /- if expression in a statement. -/
 | while     : E   → St → St         /- A while statement. -/
 | letx      : E   → St → St         /- A let expression. -/
 | openx     : E   → St → St         /- open an existential package (elimination) to a value. -/
 | openstar  : E   → St → St         /- open an existential package (elimination) with a pointer to the value. -/
with E : Type                        /- Terms for expressions. -/
 | v_e        : V → E                /- Put a variable into an expression, either bound or free. -/
 | i_e        : ℤ → E                /- An integer value in an expression. -/
 | p_e        : V → list PE → E      /- This is a term that derefences a path into the value of the variable. -/
 | f_e        : F → E                /- A function identifier in an expression or statement. -/
 | amp        : E → E                /- Take the address of an expression. -/
 | star       : E → E                /- Derefence an expression of a pointer type. -/
 | cpair      : E → E → E            /- A pair in an expression. -/
 | dot        : E → IPE → E          /- A deference of a pair. -/
 | assign     : E → E → E            /- Assignment. -/
 | appl       : E → E → E            /- Application expression. app is append. -/
 | call       : St → E               /- A call expression for the semantics use. -/
 | inst       : E → Tau → E          /- Type instantiation, e[\tau]. -/
 | pack       : Tau → E → Tau → E    /- Existential type introduction. -/
with F : Type 
 | dfun       : Tau → Tau → St → F    /- Function definition. -/
 | ufun       : Kappa → F → F         /- Univerally quantified polymorphic function definition.  -/

export St
export E 
export F 

inductive Term : Type
| term_st : St → Term 
| term_e :  E → Term 
| term_f :  F → Term
export Term

inductive Value : E → Prop
| IIsAValue    : forall (i : ℤ), Value (E.i_e i)
| AmpIsAValue  : forall (v : Var) (p : list PE),  Value (amp (E.p_e (V.fevar v) p)) 
| DfunIsAValue : forall (t1 t2 : Tau) (s : St), Value (E.f_e (F.dfun t1 t2 s))
| UfunIsAValue : forall (k : Kappa) (f : F),    Value (E.f_e (F.ufun k f))
| PairIsAValue : forall (v0 v1 : E), Value v0 → Value v1 → Value (E.cpair v0 v1)
| PackIsAValue : forall (tau tau': Tau) (v : E), Value v → Value (E.pack tau v tau')

notation `Path`    := list PE
notation `Binding` := Var × E 
notation `Heap`    := list Binding
notation `State`   := Heap × St
notation `Delta`   := list (Var × Kappa) 
notation `Gamma`   := list (Var × Tau)
notation `Upsilon` := list ((Var × Path) × Tau)
