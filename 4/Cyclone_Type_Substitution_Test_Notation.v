(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION".   Daniel Grossman, August 2003 *)
(* Testing ~n~> notations. *)
(* Brian Milnes 2016 *)

Set Implicit Arguments.
Require Export Cyclone_Type_Substitution.

Example no_notation_subst_Tau:
     forall tau0 alpha trm,
       [ tau0 ~ty~> alpha]trm= tau0.

Example no_notation_subst_V:
     forall tau0 alpha trm,
       [ tau0 ~tyv~> alpha]trm= tau0.

Example no_notation_subst_E:
     forall tau0 alpha trm,
       [ tau0 ~tye~> alpha]trm= tau0.

Example no_notation_subst_St:
     forall tau0 alpha trm,
       [ tau0 ~tyst~> alpha]trm= tau0.

Example no_notation_subst_F:
     forall tau0 alpha trm,
       [ tau0 ~tyf~> alpha]trm= tau0.

Example no_notation_subst_Type_Term:
     forall tau0 alpha trm,
       [ tau0 ~tytm~> alpha]trm= tau0.

