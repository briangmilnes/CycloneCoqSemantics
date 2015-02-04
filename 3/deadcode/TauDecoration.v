(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  A very separate attempt to augment etypes with an optional witness type.

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


Inductive Tau : Type :=
 | tv_t   : TVar -> Tau                              (* A type variable is a type. *)
 | cint   : Tau                                      (* Cyclone's Integers. *)
 | cross  : Tau -> Tau -> Tau                        (* Pairs. *)
 | arrow  : Tau -> Tau -> Tau                        (* Function    type. *)
 | ptype  : Tau -> Tau                               (* Pointer     type. *)
 | utype  : TVar -> Kappa -> Tau -> Tau              (* Universal   type. *)
 | etype  : Phi -> TVar -> Kappa -> Tau -> option Tau -> Tau.      (* Existential type. *)

Inductive EVar : Type :=                                        
 | evar : nat -> EVar.

Function beq_evar (x y : EVar) : bool :=
   match x, y with
     | (evar x'), (evar y') => beq_nat x' y'
  end.


Inductive IPE: Type :=
 | zero_pe                                 (* Access first of pair. *)
 | one_pe                                  (* Access second of pair. *) 
with PE : Type :=                          (* Path Element, the empty path is nil. *)
 | i_pe      : IPE -> PE                   (* An access into a pair. *)
 | u_pe      : PE.                         (* An access into an existential type. *)

Definition P : Type := list PE.              (* Paths are lists of path elements. *)

Function beq_path (p q : P) : bool := 
  match p, q with
    | [], [] => true
    | (i_pe zero_pe) :: p', (i_pe zero_pe) :: q' => beq_path p' q'
    | (i_pe one_pe)  :: p', (i_pe one_pe ) :: q' => beq_path p' q'
    | u_pe :: p', u_pe :: q'  => beq_path p' q' (* Bug 39, failed to recurse. *)
    | _  , _ => false
  end.

Definition UE        := prod (prod EVar P) Tau.
Definition Upsilon   := list UE.

(* Can I just build a function or do I need a relation to do a settype? *)


Function NotInDomU (u : Upsilon) (x : EVar) (p : P) : bool :=
  match x, u with 
    | _, [] => true
    | x, (((y,p'),_) :: u') =>
       if andb (beq_evar x y) (beq_path p p')
       then true
       else NotInDomU u' x p
   end.

Function union_Upsilon (u u1 : Upsilon) : Upsilon :=
  match u with
    | (x, p, tau) :: u' => 
      if (NotInDomU u1 x p) 
      then (x, p, tau) :: (union_Upsilon u' u1)
      else union_Upsilon u' u1
    | [] => u1
  end.

(* Todo how much do I recurse? 
I have no pathing information for universals, ptypes or function types. *)
Function settype (x : EVar) (p : P) (t : Tau) : Upsilon :=
  match t with 
   | tv_t _ => []
   | cint => []
   | cross t0 t1 => 
     (union_Upsilon (settype x (p ++ [i_pe zero_pe]) t0) (settype x (p ++ [i_pe one_pe]) t1))
   | arrow _ _ => []
   | etype aliases alpha k tau' (Some tau) => 
     (union_Upsilon [(x,p++[u_pe],tau)] (settype x (p ++ [u_pe]) tau')).
   (* The idea hear is that this None path should not ever happen. *)
   | etype aliases alpha k tau' None       => (settype x (p ++ [u_pe]) tau') 
   | etype witnesschange _ _ _ _ => []
   | ptype _ => []
   | utype _ _ _ => []
  end.
(* No inversion. *)

(* In SR3.1 and SL3.1 Upsilon is set to settype x p t, that's it for a change. *)