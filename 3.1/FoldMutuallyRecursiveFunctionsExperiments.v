(* Why can't Coq unfold/fold mutually recursive functions? *)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.
Require Import Coq.Init.Logic.
Require Import Coq.Bool.Bool.

Require Export EVarModuleDef.
Require Export TauModuleDef.
Require Export CpdtTactics. 
Require Export Case.

Import TauModule.
Import EVarModule.
Definition EVar := EVarModule.Var.
Definition evar := EVarModule.var.
Definition beq_evar := EVarModule.beq_t.

Inductive St : Type :=                        (* Terms for statements. *)
 | e_s       : E   -> St                      (* An expression in a statement. *)
with E : Type :=                              (* Terms for expressions. *)
 | call      : St -> E                        (* A call expression for the semantics use. *)
.

Function beq_st (s s' : St) : bool := 
  match s, s' with
    | (e_s e), (e_s e') => beq_e e e'
  end
with beq_e (e e' : E) : bool := 
 match e, e' with 
 | call s, call s'               => beq_st s s'
end.

Lemma fu:
  forall e, beq_st (e_s e) (e_s e) = true.
Proof.
  intros.
  unfold beq_st.
  fold beq_st.
  fold beq_e.