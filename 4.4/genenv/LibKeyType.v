(**************************************************************************
* TLC: A library for Coq                                                  *
* Keys for environment signature. 
**************************************************************************)

Set Implicit Arguments.
Require Import TLC.LibTactics TLC.LibList TLC.LibLogic TLC.LibNat TLC.LibEpsilon TLC.LibReflect.
Require Export TLC.LibFset.
Require Export LibFresh.

(** * Abstract Definition of Key for an environment. *)

Module Type KeyType.

(** We leave the type of variables abstract. *)

Parameter key : Set.

(** This type is inhabited. *)

Parameter key_inhab : Inhab key.

(** This type is comparable. *)
Parameter key_comp : Comparable key.
Instance  key_comparable : Comparable key := key_comp.

(** We can build sets of variables. *)

Definition keys := fset key.

(** Finally, we have a means of generating fresh variables. *)

Parameter key_gen : keys -> key.
Parameter key_gen_spec : forall E, (key_gen E) \notin E.
Parameter key_fresh : forall (L : keys), { x : key | x \notin L }.

Axiom key_freshes : forall L n, { xs : list key | fresh key L n xs}.
End KeyType.