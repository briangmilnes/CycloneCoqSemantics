(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Try subset typing ala Chlipala.

*)

Require Import List.
Export ListNotations.
Require Export ZArith.
Require Import Init.Datatypes.

Require Import DynamicSemanticsTypeSubstitution.
Require Export CpdtTactics.
Require Export Case.
Require Import FormalSyntax.
Require Export Equalities.

Set Implicit Arguments.

Definition K    := nat.
Definition K_eq := beq_nat.
Definition T    := nat.
Definition T_eq := beq_nat.

  Inductive Context (K : Type) (T : Type) : Type :=
  | Ctxt_dot  : Context K T
  | Ctxt      : K -> T -> Context K T -> Context K T.


  Inductive In (k : K) : Context K T ->  Prop := 
   | In_hd : forall k' t' c, K_eq k k' = true -> In k (Ctxt k' t' c)
   | In_tl : forall k' t' c, In k c -> In k (Ctxt k' t' c).

  Inductive  NoDup : Context K T -> Prop :=
    | NoDup_dot  : NoDup (Ctxt_dot K T)
    | NoDup_ctxt : forall k t c,
                     NoDup c ->
                     ~In k c ->
                     NoDup (Ctxt k t c).

  Definition Context' := 
    fun (k : Type) (t : Type)  => { c : Context K T  | NoDup c }.

Print Context'.
Print sig.
Print ex.

Fixpoint trivial (f : Context' K T) (k: K) (t : T)  : Context' K T :=
  exist (Ctxt_dot K T).


Fixpoint add (f : Context' K T) (k: K) (t : T)  : Context' K T :=
  match f with
    | exist Ctxt_dot _ =>  (Ctxt k t (Ctxt_dot K T))
      | exist (Ctxt k' t' f') _ =>
        match K_eq k k' with
          | true  => (Ctxt k  t  f')
          | false => (Ctxt k' t' (add f' k t))
        end
  end.