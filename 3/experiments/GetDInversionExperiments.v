(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  A copy to try and get inversion working on getD as it breaks
 K induction.

*)

(*
  Typographic conventions 

   Upper case for inductive types. 
   Using only Dan's greek names.
   Context is C. 
   P for path (p).
   Phi went from lower case delta/ampersand to human readable witnesschange/aliases.
   s for the judgement, St for statements and State for states.

   YE for elements that go in lists of type Y.
*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.

Require Export CpdtTactics.
Require Export Case.
(* The abstract syntax of kinds. *)

Inductive Kappa : Type :=
 | B                         (* 'boxed' kind. *)
 | A.                        (* 'any'   kind. *)

Function beq_kappa (k k' : Kappa) : bool :=
   match k, k' with
     |  A, A => true
     |  B, B => true
     |  _, _ => false
  end.


(* The abstract syntax of types. *)

(* A type variable, numbered. *)
Inductive TVar : Type :=
 | tvar   : nat -> TVar.

Function beq_tvar (x y : TVar) : bool :=
   match x, y with
     | (tvar x'), (tvar y') => beq_nat x' y'
  end.

(* A type limiting the opening of existential types. *)

Inductive Phi : Type :=
 | witnesschanges  : Phi                            (* Allowing witness changes. \delta *)
 | aliases        : Phi.                             (* Allowing aliases as the opened type. \amp *)

(* The types. *)

Inductive Tau : Type :=
 | tv_t   : TVar -> Tau                              (* A type variable is a type. *)
 | cint   : Tau                                      (* Cyclone's Integers. *)
 | cross  : Tau -> Tau -> Tau                        (* Pairs. *)
 | arrow  : Tau -> Tau -> Tau                        (* Function    type. *)
 | ptype  : Tau -> Tau                               (* Pointer     type. *)
 | utype  : TVar -> Kappa -> Tau -> Tau              (* Universal   type. *)
 | etype  : Phi -> TVar -> Kappa -> Tau -> Tau.      (* Existential type. *)

Function removeTVar (alpha : TVar) (tvars : list TVar) : list TVar :=
  match alpha, tvars with 
   | _, [] => []
   | tvar n, (tvar n') :: tvars' =>
     if beq_nat n n' 
     then removeTVar alpha tvars' 
     else (tvar n) :: (removeTVar alpha tvars')
  end.

Function FreeVariablesTau (tau : Tau) : list TVar :=
  match tau with 
   | tv_t alpha   => [alpha]
   | cint         => []
   | cross t0 t1  => (FreeVariablesTau t0) ++ (FreeVariablesTau t1)
   | arrow t0 t1  => (FreeVariablesTau t0) ++ (FreeVariablesTau t1)
   | ptype t      => (FreeVariablesTau t)
   | utype alpha _ t    => removeTVar alpha (FreeVariablesTau t)
   | etype _ alpha _ t  => removeTVar alpha (FreeVariablesTau t)
  end.

(* The abstract syntax of expression variables. *)

Inductive EVar : Type :=                                        
 | evar : nat -> EVar.                                          (* variables appearing in the source language. *)

Function beq_evar (x y : EVar) : bool :=
   match x, y with
     | (evar x'), (evar y') => beq_nat x' y'
  end.

(* The abstract syntax of terms, split into statements and expressions. *)
(* Got rid of a bunch of _e but still have four to simplify.  *)

Inductive I  : Type :=  
 | i_i       : Z -> I.                         (* An integer value in an expression or statement. *)

(* Bug 45, should have made this just zero/one not an i to make the inductions
   work. *)
Inductive IPE: Type :=
 | zero_pe                                 (* Access first of pair. *)
 | one_pe                                  (* Access second of pair. *) 
with PE : Type :=                          (* Path Element, the empty path is nil. *)
 | i_pe      : IPE -> PE                   (* An access into a pair. *)
 | u_pe      : PE.                         (* An access into an existential type. *)

Definition P : Type := list PE.              (* Paths are lists of path elements. *)

Inductive St : Type :=                        (* Terms for statements. *)
 | e_s       : E   -> St                      (* An expression in a statement. *)
 | retn      : E   -> St                      (* Returns are required in this syntax. *)
 | seq       : St  -> St -> St                (* Statement sequencing. *)
 | if_s      : E   -> St -> St   -> St        (* if expression in a statement. *)
 | while     : E   -> St -> St                (* A while statement. *)
 | letx      : EVar -> E -> St   -> St        (* A let expression. *)
 | open      : E -> TVar -> EVar -> St -> St  (* open an existential package (elimination) to a value. *)
 | openstar  : E -> TVar -> EVar -> St -> St  (* open an existential package (elimination) with a pointer to the value. *)
with E : Type :=                              (* Terms for expressions. *)
 | i_e       : I -> E                         (* An integer value in an expression. *)
 | p_e       : EVar -> list PE -> E           (* This is a term that derefences a path into the value of the variable. *)
 | f_e       : F -> E                         (* A function identifier in an expression or statement. *)
 | amp       : E -> E                         (* Take the address of an expression. *)
 | star      : E -> E                         (* Derefence an expression of a pointer type. *)
 | cpair     : E -> E -> E                    (* A pair in an expression. *)
 | dot       : E -> IPE -> E                  (* A deference of a pair. *)
 | assign    : E -> E -> E                    (* Equality expression. *)
 | appl      : E -> E -> E                    (* Application expression. app is append. *)
 | call      : St -> E                        (* A call expression for the semantics use. *)
 | inst      : E -> Tau -> E                  (* Type instantiation, e[\tau]. *)
 | pack      : Tau -> E -> Tau -> E           (* Existential type introduction. *)
with F : Type :=
 | dfun      : Tau -> EVar -> Tau -> St -> F  (* Function definition. *)
 | ufun      : TVar -> Kappa -> F -> F        (* Univerally quantified polymorphic function definition.  *)
.

Scheme St_ind_mutual := Induction for St Sort Prop
with    E_ind_mutual := Induction for E Sort Prop
with    F_ind_mutual := Induction for F Sort Prop.
Combined Scheme Term_ind_mutual from St_ind_mutual, E_ind_mutual, F_ind_mutual.

(* jrw why can't coqie invert? *)
Function beq_path (p q : P) : bool := 
  match p, q with
    | [], [] => true
    | (i_pe zero_pe) :: p', (i_pe zero_pe) :: q' => beq_path p' q'
    | (i_pe one_pe)  :: p', (i_pe one_pe ) :: q' => beq_path p' q'
    | u_pe :: p', u_pe :: q'  => beq_path p' q' (* Bug 39, failed to recurse. *)
    | _  , _ => false
  end.
(* TODO on inversion write the last clause to explicitly match the other cases. *)

(* Make a value type judgement. The thesis does this syntactically 
but that's not representable in Coq. *)

Inductive Value : E -> Prop :=
 | IIsAValue    : forall (i : I),              Value (i_e i)
                                                     
 | AmpIsAValue  : forall (x : EVar) (p : P),   Value (amp (p_e x p)) 

 | DfunIsAValue : forall (t1 t2 : Tau) (x : EVar) (s : St), 
                        Value (f_e (dfun t1 x t2 s))
 | UfunIsAValue : 
     forall (t : TVar) (k : Kappa) (f : F),
       Value (f_e (ufun t k f))

 | PairIsAValue :
     forall (v0 v1 : E), 
       Value v0 ->
       Value v1 ->
       Value (cpair v0 v1)

(* Bug 40, forget a subvalue here. *)
 | PackIsAValue :
     forall (tau tau': Tau) (v : E),
       Value v -> 
       Value (pack tau v tau').

(* The abstract syntax of H values. *)

Definition HE : Type := prod EVar E.
Definition H  : Type := list HE.

(* Bug 2, 3 *)

Function getH (h : H) (x : EVar) : option E :=
    match x, h with 
    | x, (y,v) :: h' =>
      if beq_evar x y
      then Some v 
      else getH h' x
    | _ , nil => None
  end.

(* TODO move to beq_evar. *)

Function setH (h : H) (x : EVar) (e : E) : H :=
  match x, h with
    | evar x', (evar y',v) :: h' =>
      if beq_nat x' y'
      then [(x,e)] ++ h'
      else (evar y',v) :: (setH h' x e)
    | (evar x'), _ => [(x,e)]
 end.

Function deleteH (h : H) (x : EVar) : H :=
    match x, h with
    | evar x', (evar y',v) :: h' =>
      if beq_nat x' y'
      then h'
      else (evar y',v) :: (deleteH h' x)
    | _, [] => []
 end.

(* The context is three part: kind assignment, type assignments and path assignments. *)

Definition DE : Type := prod TVar Kappa.
Definition Delta     := list DE.
 
(* Inversion on getD may be the bug in K induction as d0 keeps appearing. *)

Function getD (d : Delta) (alpha : TVar) : option Kappa :=
  match alpha, d with 
    | a, (b, k) :: d' =>
      if beq_tvar a b 
      then Some k 
      else getD d' alpha
    | _ , nil => None
  end.

Print getD_equation.
Print getD_ind.
Print getD_rec.
Print getD_rect.
Print R_getD_correct.
Print R_getD_complete.

