Require Import List.
Export ListNotations.
Require Export ZArith.
Require Import Init.Datatypes.

Inductive IPE2: Type :=
 | zero_pe2    
 | one_pe2.

Inductive PE2 : Type := 
 | i_pe2      : IPE2 -> PE2
 | u_pe2      : PE2.

Definition P2 : Type := list PE2.
 
Function beq_IPE2 (i i' : IPE2) : bool := 
  match i, i' with
    | zero_pe2, zero_pe2 => true
    | one_pe2, one_pe2 => true
    | _, _ => false
  end.

Function beq_PE2 (p p' : PE2) : bool :=
  match p, p' with
    | i_pe2 x, i_pe2 y => beq_IPE2 x y
    | u_pe2, u_pe2 => true
    | _, _ => false
  end.
 
Function beq_path2 (p q : P2) : bool := 
  match p, q with
    | [], [] => true
    | x :: p', y :: q' => andb (beq_PE2 x y) (beq_path2 p' q')
    | _  , _ => false
  end.
