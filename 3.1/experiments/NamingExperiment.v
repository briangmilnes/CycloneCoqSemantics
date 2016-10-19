(* See if I can figgure out a better way to make Terms and Types available without
prefixes and without conflict. *)

Set Implicit Arguments.

Require Export List.
Export ListNotations.
Require Export ZArith.
Require Export Init.Datatypes.

Module Types.

 Inductive Tau :=  
 | cint   : Tau.

 Definition T := Tau.
 Function beq_t (t t : T) := true.
End Types.

Module Terms.
 Inductive St : Type :=
 | retn      : St.

 Definition T := St.
 Function beq_st (t t : T) := true.
 Definition beq_t := beq_st.

End Terms.

Check Types.cint.
Check Terms.retn.

Import Types.
Import Terms.

(* Now use them without qualification. *)

Check cint.
Check retn.

(* This just works without conflict. What is generating my conflict in
