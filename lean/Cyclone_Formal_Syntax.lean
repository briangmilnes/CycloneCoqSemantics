/- Rewriting the Coq Cyclone Formal Syntax in Lean. -/

import .LeanLib

/- TODO Lean 4 has enumerations, should I be using it? -/

inductive Kappa : Type
| B    /- 'boxed' kind. -/ 
| A    /- 'any'   kind. -/
export Kappa

#print Kappa

inductive Phi : Type
| witnesschanges /- Allowing witness changes. \delta -/
| aliases        /- Allowing aliases as the opened type. \amp -/ 

export Phi

/- Path elements -/
inductive IPE: Type
| zero_pe    
| one_pe
export IPE

inductive PE : Type 
| i_pe      : IPE -> PE
| u_pe      : PE

export PE 

inductive V : Type
| bevar : nat -> V     /- A bound expression variable, a de Bruijn index. -/
| fevar : string -> V  /- A free expression variable. -/

export V

mutual inductive St, E, F, Tau 
with St : Type 
 | e_s       : E   -> St                 /- An expression in a statement. -/
 | retn      : E   -> St                 /- Returns are required in this syntax. -/
 | seqx      : St  -> St -> St           /- Statement sequencing. -/
 | if_s      : E   -> St -> St   -> St   /- if expression in a statement. -/
 | while     : E   -> St -> St           /- A while statement. -/
 | letx      : E   -> St -> St           /- A let expression. -/
 | openx     : E   -> St -> St           /- open an existential package (elimination) to a value. -/
 | openstar  : E   -> St -> St           /- open an existential package (elimination) with a pointer to the value. -/
with E : Type                            /- Terms for expressions. -/
 | v_e        : V -> E                   /- Put a variable into an expression, either bound or free. -/
 | i_e        : ℤ -> E                   /- An integer value in an expression. -/
 | p_e        : V -> list PE -> E        /- This is a term that derefences a path into the value of the variable. -/
 | f_e        : F -> E                   /- A function identifier in an expression or statement. -/
 | amp        : E -> E                   /- Take the address of an expression. -/
 | star       : E -> E                   /- Derefence an expression of a pointer type. -/
 | cpair      : E -> E -> E              /- A pair in an expression. -/
 | dot        : E -> IPE -> E            /- A deference of a pair. -/
 | assign     : E -> E -> E              /- Assignment. -/
 | appl       : E -> E -> E              /- Application expression. app is append. -/
 | call       : St -> E                  /- A call expression for the semantics use. -/
 | inst       : E -> Tau -> E            /- Type instantiation, e[\tau]. -/
 | pack       : Tau -> E -> Tau -> E     /- Existential type introduction. -/
/- This was done in Coq to make induction work, perhaps it works without it? -/
with F : Type 
 | dfun       : Tau -> Tau -> St -> F    /- Function definition. -/
 | ufun       : Kappa -> F -> F          /- Univerally quantified polymorphic function definition.  -/
with Tau : Type
 | btvar  : nat -> Tau                   /- A bound type variable, a de Bruijn index. -/
 | ftvar  : string -> Tau                /- A free type variable. -/
 | cint   : Tau                          /- Cyclone's Integers. -/
 | cross  : Tau -> Tau -> Tau            /- Pairs. -/
 | arrow  : Tau -> Tau -> Tau            /- Function    type. -/
 | ptype  : Tau -> Tau                   /- Pointer     type. -/
 | utype  : Kappa -> Tau -> Tau          /- Universal   type. -/
 | etype  : Phi -> Kappa -> Tau -> Tau   /- Existential type. -/

export St
export E 
export F 
export Tau

inductive Term : Type
| term_st : St -> Term 
| term_e :  E -> Term 
| term_f :  F -> Term
export Term

inductive Value : E -> Prop
| IIsAValue    : forall (i : ℤ), Value (E.i_e i)
| AmpIsAValue  : forall (v : string) (p : list PE),  Value (amp (E.p_e (V.fevar v) p)) 
| DfunIsAValue : forall (t1 t2 : Tau) (s : St), Value (E.f_e (F.dfun t1 t2 s))
| UfunIsAValue : forall (k : Kappa) (f : F),    Value (E.f_e (F.ufun k f))
| PairIsAValue : forall (v0 v1 : E), Value v0 -> Value v1 -> Value (E.cpair v0 v1)
| PackIsAValue : forall (tau tau': Tau) (v : E), Value v -> Value (E.pack tau v tau')

/- TODO I'm pretty sure these are not correct. -/
/- Environments are forwards at the moment: the last is the latest binding. -/
/- This is going to take lots of dereferncing which is going to be annoying notation. -/
/- I'm going to expand these to start, these are then only notational. -/
structure Binding := (var : string) (e : E) 
structure Env     := (bindings : list Binding)
structure Heap    := (env : list Binding) (exp : E)
structure State   := (h : Heap) (st : St)
/- These should be type abbreviations, but I don't see that in lean 3. -/ 
structure Delta   := (env : list (string × Kappa))
structure Gamma   := (env : list (string × Tau))
/- I don't even remember what this was in Coq. -/
structure Upsilon := (vpe : list ((string × list PE) × Tau))
