(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION".   Daniel Grossman, August 2003 *)
(* Definitions from Section 3.5.1 *)
(* Brian Milnes *)

Set Implicit Arguments.
Require Export TLC.LibLN TLC.LibNat TLC.LibEnv.
Require Export LibVarPathEnv.

(* Question: can var be the same for types and programming variables? He does so in ML. *)
(* Arthur uses Set not type, switching. I wonder if it matters. *)

Inductive Kappa : Set :=
 | B                         (* 'boxed' kind. *)
 | A.                        (* 'any'   kind. *)

Inductive Phi : Set :=
 | witnesschanges  : Phi     (* Allowing witness changes. \delta *)
 | aliases        : Phi.     (* Allowing aliases as the opened type. \amp *)

Inductive IPE: Set :=
 | zero_pe    
 | one_pe.

Inductive PE : Set := 
 | i_pe      : IPE -> PE
 | u_pe      : PE.

(* Question: will list PE work as paths in TLC? *)
Definition Path : Set := list PE.

Inductive I  : Set :=  
 | i_i       : nat -> I.                 (* An integer value in an expression or statement. *)

Inductive V : Set :=
 | bevar      : nat -> V                 (* A bound expression variable, a de Bruijn index. *)
 | fevar      : var -> V.                 (* A free expression variable. *)

Inductive St : Set :=                    (* Terms for statements. *)
 | e_s       : E   -> St                 (* An expression in a statement. *)
 | retn      : E   -> St                 (* Returns are required in this syntax. *)
 | seq       : St  -> St -> St           (* Statement sequencing. *)
 | if_s      : E   -> St -> St   -> St   (* if expression in a statement. *)
 | while     : E   -> St -> St           (* A while statement. *)
 | letx      : E   -> St -> St           (* A let expression. *)
 | openx     : E   -> St -> St           (* open an existential package (elimination) to a value. *)
 | openstar  : E   -> St -> St           (* open an existential package (elimination) with a pointer to the value. *)
with E : Set :=                          (* Terms for expressions. *)
 | v_e        : V -> E                   (* Put a variable into an expression, either bound or free. *)
 | i_e        : I -> E                   (* An integer value in an expression. *)
 | p_e        : V -> list PE -> E        (* This is a term that derefences a path into the value of the variable. *)
 | f_e        : F -> E                   (* A function identifier in an expression or statement. *)
 | amp        : E -> E                   (* Take the address of an expression. *)
 | star       : E -> E                   (* Derefence an expression of a pointer type. *)
 | cpair      : E -> E -> E              (* A pair in an expression. *)
 | dot        : E -> IPE -> E            (* A deference of a pair. *)
 | assign     : E -> E -> E              (* Assignment. *)
 | appl       : E -> E -> E              (* Application expression. app is append. *)
 | call       : St -> E                  (* A call expression for the semantics use. *)
 | inst       : E -> Tau -> E            (* Type instantiation, e[\tau]. *)
 | pack       : Tau -> E -> Tau -> E     (* Existential type introduction. *)
with F : Set :=
 | dfun       : Tau -> Tau -> St -> F    (* Function definition. *)
 | ufun       : Kappa -> F -> F         (* Univerally quantified polymorphic function definition.  *)
with Tau : Set :=
 | btvar  : nat -> Tau                   (* A bound type variable, a de Bruijn index. *)
 | ftvar  : var -> Tau                   (* A free type variable. *)
 | cint   : Tau                          (* Cyclone's Integers. *)
 | cross  : Tau -> Tau -> Tau            (* Pairs. *)
 | arrow  : Tau -> Tau -> Tau            (* Function    type. *)
 | ptype  : Tau -> Tau                   (* Pointer     type. *)
 | utype  : Kappa -> Tau -> Tau          (* Universal   type. *)
 | etype  : Phi -> Kappa -> Tau -> Tau.  (* Existential type. *)


Inductive Term : Set := 
  | term_st : St -> Term 
  | term_e :  E -> Term 
  | term_f :  F -> Term.

(* Question: what about an inductive schema? *)

Scheme St_ind_mutual := Induction for St Sort Prop
with    E_ind_mutual := Induction for E Sort Prop
with    F_ind_mutual := Induction for F Sort Prop.
Combined Scheme Term_ind_mutual from St_ind_mutual, E_ind_mutual, F_ind_mutual.

Scheme Tau_St_ind_mutual := Induction for St Sort Prop
with   Tau_E_ind_mutual := Induction for E Sort Prop
with   Tau_F_ind_mutual := Induction for F Sort Prop
with   Tau_Tau_ind_mutual := Induction for Tau Sort Prop.
Combined Scheme Tau_Term_ind_mutual from Tau_St_ind_mutual, Tau_E_ind_mutual, Tau_F_ind_mutual, Tau_Tau_ind_mutual.

(* Question: do I need lc? Yes I think so. So this has to move also. *)

Inductive Value : E -> Prop :=
 | IIsAValue    : forall (i : I),              Value (i_e i)
                                                     
 | AmpIsAValue  : forall (v : V) (p : Path),   Value (amp (p_e v p)) 

 | DfunIsAValue : forall (t1 t2 : Tau) (s : St), 
                        Value (f_e (dfun t1 t2 s))
 | UfunIsAValue : 
     forall (k : Kappa) (f : F),
       Value (f_e (ufun k f))
 | PairIsAValue :
     forall (v0 v1 : E), 
       Value v0 ->
       Value v1 ->
       Value (cpair v0 v1)
 | PackIsAValue :
     forall (tau tau': Tau) (v : E),
       Value v -> 
       Value (pack tau v tau').

(* Problem: With pathing contexts and heaps we may run into problems with TLC, as it
really must map a variable path pair to a Type. 

  TLC has 200 lines of definitions and 1000 lines of theorems in LibEnv that
 may need to be rebuilt or generalized.

  Additionally, Heap is defined as mapping free variables to values so this Heap is overly
 general for the thesis. 

  Finally, should these be free variables or LibLN style variables?
*)

Definition Heap  := env E.
Definition State := prod Heap St.  
Definition Delta := env Kappa.
Definition Gamma := env Tau.
Definition Upsilon := LVPE.varpathenv E.

(* 
   BUG: This has a GIANT problem. Arthur's env are abstract and yet I want
   to compute with them to build the free variable list.
*)