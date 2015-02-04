Require Import List.
Export ListNotations.
Require Export ZArith.
Require Import Init.Datatypes.

Inductive IPE: Type :=
 | zero_pe    
 | one_pe.

Inductive PE : Type := 
 | i_pe      : IPE -> PE
 | u_pe      : PE.

Definition P : Type := list PE.
 
Function beq_IPE (i i' : IPE) : bool := 
  match i, i' with
    | zero_pe, zero_pe => true
    | one_pe, one_pe => true
    | _, _ => false
  end.

Function beq_PE (p p' : PE) : bool :=
  match p, p' with
    | i_pe x, i_pe y => beq_IPE x y
    | u_pe, u_pe => true
    | _, _ => false
  end.
 
Function beq_path (p q : P) : bool := 
  match p, q with
    | [], [] => true
    | x :: p', y :: q' => andb (beq_PE x y) (beq_path p' q')
    | _  , _ => false
  end.
