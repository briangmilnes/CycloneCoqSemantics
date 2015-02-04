Require Import List.
Export ListNotations.
Require Export ZArith.
Require Import Init.Datatypes.

(* Print IPE. *)
(* Print zero_pe. *)
(* Print one_pe. *)

Inductive IPE: Type :=
 | zero_pe    
 | one_pe.

(* Print PE. *)
(* Print i_pe.*)
(* Print u_pe. *)

Inductive PE : Type := 
 | i_pe      : IPE -> PE
 | u_pe      : PE.

(* Print P. *)
Definition P : Type := list PE.
 
(* Print beq_IPE. *)
Function beq_IPE (i i' : IPE) : bool := 
  match i, i' with
    | zero_pe, zero_pe => true
    | one_pe, one_pe => true
    | _, _ => false
  end.

(* Print beq_PE. *)
Function beq_PE (p p' : PE) : bool :=
  match p, p' with
    | i_pe x, i_pe y => beq_IPE x y
    | u_pe, u_pe => true
    | _, _ => false
  end.
 
(* Print beq_path.*)
Function beq_path (p q : P) : bool := 
  match p, q with
    | [], [] => true
    | x :: p', y :: q' => andb (beq_PE x y) (beq_path p' q')
    | _  , _ => false
  end.
