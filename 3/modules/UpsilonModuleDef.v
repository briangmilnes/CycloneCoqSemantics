(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  An attempt at a context module, just the operations, proofs in 
 another module.

*)

Require Import List.
Export ListNotations.
Require Export ZArith.
Require Import Init.Datatypes.
Require Export Coq.Bool.Bool.

Add LoadPath "/home/milnes/Desktop/Research/Cyclone/CycloneCoq/3".
Require Export CpdtTactics.
Require Export Case.

Require Export ContextSigDef.
Require Export BoolEqualitySigDef.
Require Export EVarModuleDef.

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

Definition UE        := prod (prod EVar P) Tau.
Definition Upsilon   := list UE.
 
(* Why can't Brian invert? *)
Function beq_path (p q : P) : bool := 
  match p, q with
    | [], [] => true
    | (i_pe zero_pe) :: p', (i_pe zero_pe) :: q' => beq_path p' q'
    | (i_pe one_pe)  :: p', (i_pe one_pe ) :: q' => beq_path p' q'
    | u_pe :: p', u_pe :: q'  => beq_path p' q' (* Bug 39, failed to recurse. *)
    | _  , _ => false
  end.

Function map
  False.

Inductive getU : Upsilon -> EVar -> P -> Tau -> Prop :=
  | getU_top  : forall (u : Upsilon) (x : EVar) (p : P) (tau : Tau),
                 getU ([((x,p),tau)] ++ u) x p tau
  | getU_next : forall (u : Upsilon) (x y: EVar) (p p': P) (tau tau': Tau),
                 beq_evar x y = false \/ beq_path p p' = false ->
                 getU u x p tau ->
                 getU ([((y,p'),tau')] ++ u) x p tau.

(* TODO warning on inversion, do I need a relation here also? *)
Function NotInDomU (u : Upsilon) (x : EVar) (p : P) : Prop :=
  match x, u with 
    | _, [] => True
    | x, (((y,p'),_) :: u') =>
       if andb (beq_evar x y) (beq_path p p')
       then True
       else NotInDomU u' x p
   end.

