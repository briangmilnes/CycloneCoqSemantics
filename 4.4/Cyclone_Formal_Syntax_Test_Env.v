(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION".   Daniel Grossman, August 2003 *)
(* Test code for Environments in the formal syntax. *)
(* Brian Milnes 2016 *)

Set Implicit Arguments.
Require Export Cyclone_Formal_Syntax TLC.LibEnv TLC.LibLN.
Open Scope env_scope.
Close Scope type_scope.
Import LibEnvNotations.
Import LVPE.LibVarPathEnvNotations.

(* Open Scope varpathenv_scope. *)
(* BUG: serious notation bug! *)

(* 

  We use four types of environments in the Cyclone semantics, two of
 which are directly supported by TLC: Delta, or Kinding, and Gamma or
 Typing.

 However, two are not supported directly, Heap or variables to values for the
 store and Pathing, variables x paths to a Type. 

 So this test file is to allow us to work out how this is going to work.
*)

(* There is some notation parsing bug between ~ for not and ~ for singleton
  environments. *)

(* Kinds are right. *)
Check A.
Check B.    

Module TestUpsilon.
  Parameter U : Upsilon.
  Parameter V : Upsilon.
  Parameter vp : varpath.
  Parameter t : Tau.
  Check U &p V.
  Check (U &p (vp ~p t)).
End TestUpsilon.


Module TestDelta.
  Parameter a : Delta.
  Parameter b : Delta.
  Parameter c : Gamma.
  Parameter v : var.
  Parameter E : Delta.
  Parameter x : var.
  Parameter K : Kappa.
  Parameter Z : list var.
  Parameter Q : list Kappa.

  Check a & b.
(* Why am I not getting ~? *)
  Check (single v a).
  Check (E & E).
  Check (x # E).
  Check (E & (Z ~* Q)).
  (* Basically ~ works where it is defined and then not again. *)
  (* Check (E & (x ~ A)).*)
End TestDelta.



Module TestGamma.
  Parameter a : Gamma.
  Parameter b : Gamma.
  Parameter c : Delta.
  Parameter v : var.
  Parameter E : Gamma.
  Parameter x : var.
  Parameter K : Tau.

  Check a & b.
(* Why am I not getting ~? *)
  Check (single v a).
(*  Check (E & (x ~ K)). *)
(* Notation "x ~ a" := (single x a)
  (at level 27, left associativity) : env_scope.
*)
(* Check (E & (x ~ K)). *)
(* This is some wierd ass bug I would say in the notation overlay. *)
End TestGamma.

(* Question: what about heap overwriting? *)
Module TestHeap.
 Parameter H : Heap.  
 Parameter I : Heap.
 Parameter x : var.
 Parameter e : E.

 Check H & I.
 (* Check (H & (x ~ e)). *)

End TestHeap.

