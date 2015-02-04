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

Require Import DynamicSemanticsTypeSubstitution.
Require Export CpdtTactics.
Require Export Case.
Require Import FormalSyntax.

Require Export ContextSigDef.
Require Export VariablesProofsSigDef.

Set Implicit Arguments.

Module ContextFun(KVPS : VariablesProofsSig) (TVPS : VariablesProofsSig) 
                              <: ContextSig.
  Module K := KVPS.
  Module T := TVPS.

  Definition K    := KVPS.Var.
  Definition K_eq := KVPS.beq_var.
  Definition T    := TVPS.Var. (* TOD change For the moment. *)
  Definition T_eq := TVPS.beq_var.
  Definition beq_t := TVPS.beq_var.

Inductive Context' (K : Type) (T : Type) : Type :=
| Ctxt_dot  : Context' K T
| Ctxt      : K -> T -> Context' K T -> Context' K T.

Definition Context := Context'.
Tactic Notation "Context_ind_cases" tactic(first) ident(c) :=
 first;
[ Case_aux c "(Ctxt_dot K T)"
| Case_aux c "(Ctxt k t c)"
].

Definition empty  := Ctxt_dot K T.

Function add (c : Context' K T) (k: K) (t : T)  : Context' K T :=
  match c with
    | Ctxt_dot => (Ctxt k t (Ctxt_dot K T))
    | (Ctxt k' t' c') =>
      match K_eq k k' with
        | true  => (Ctxt k  t  c')
        | false => (Ctxt k' t' (add c' k t))
      end
  end.

Function map (c : Context' K T) (k: K) : option T :=
  match c with
    | Ctxt_dot => None
    | (Ctxt k' t' c') =>
      match K_eq k k' with
        | true  => Some t'
        | false => (map c' k)
      end
  end.

Function nodup (c : (Context' K T)) : bool :=
  match c with
    | Ctxt_dot => true
    | (Ctxt k' t' c') =>
      match map c' k' with
        | Some t  => false
        | None  => nodup c'
      end
end.

Function extends (c c' : Context' K T) : bool :=
  match c with 
    | Ctxt_dot => true
    | Ctxt k t c'' =>
      match map c' k with
       | Some t' => 
         match (T_eq t t') with
           | true => extends c'' c' 
           | false => false
         end
       | None => false
      end
  end.

Function equal (c c' : Context' K T) : bool :=
  andb (extends c c') (extends c' c).


Lemma map_empty_none: forall k, map empty k = None.
Proof.
   crush.
Qed.

Lemma nodup_empty: nodup empty = true.
Proof.
  crush.
Qed.

(* TODO update these with abstract proofs using variable properties. *)
Lemma map_add: forall c k t, map (add c k t) k = Some t.
Proof.
  intros.
  induction c.
  Case "Ctxt_dot".
   crush.
   rewrite KVPS.beq_var_refl.
   reflexivity.
  Case "(Ctxt k0 t0 c)".
   crush.
   case_eq (K_eq k k0).
   SCase "K_eq k k0 = true".
    intros.
    unfold map.
    rewrite KVPS.beq_var_refl.
    reflexivity.
   SCase "K_eq k k0 = false".
    intros.
    unfold map.
    rewrite H.
    fold map.
    assumption.
Qed.

End ContextFun.