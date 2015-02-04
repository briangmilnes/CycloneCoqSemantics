(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  An attempt at a variable module in a context. 

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.
Require Import Coq.Init.Logic.

Require Export CpdtTactics.
Require Export Case.
Require Export TacticNotations.
Require Import VariablesProofsSigDef.
Require Import TypingInfoSigDef.

Module Type TauTypingInfo <: TypingInfoSig.
  Include VariablesProofsSig. 
  (* this is going to be a problem in some contexts as Var will appear twice. *)

Inductive Tau : Type :=
 | tv_t   : Var -> Tau                              (* A type variable is a type. *)
 | cint   : Tau                                      (* Cyclone's Integers. *)
 | cross  : Tau -> Tau -> Tau                        (* Pairs. *)
 | arrow  : Tau -> Tau -> Tau                        (* Function    type. *)
 | ptype  : Tau -> Tau                               (* Pointer     type. *)
 | utype  : Var -> Kappa -> Tau -> Tau              (* Universal   type. *)
 | etype  : Phi -> Var -> Kappa -> Tau -> Tau.      (* Existential type. *)

Definition T := Tau.

Function beq_kappa (k k' : Kappa) : bool :=
   match k, k' with
     |  A, A => true
     |  B, B => true
     |  _, _ => false
  end.
Hint Resolve beq_kappa.

Lemma beq_kappa_refl:
  forall k, beq_kappa k k = true.
Proof.
  induction k; crush.
Qed.
Hint Rewrite beq_kappa_refl.

Lemma beq_kappa_sym:
  forall k k', beq_kappa k k' = beq_kappa k' k.
Proof.
  induction k; crush.
Qed.
Hint Rewrite beq_kappa_sym.

Function beq_phi (p p' : Phi) : bool :=
  match p, p' with
    | witnesschanges, witnesschanges => true
    | aliases, aliases => true
    | _, _ => false
  end.
Hint Resolve beq_phi.

Lemma beq_phi_refl:
  forall p, beq_phi p p = true.
Proof.
  induction p; crush.
Qed.
Hint Resolve beq_phi_refl.

Lemma beq_phi_sym:
  forall p p', beq_phi p p' = beq_phi p' p.
Proof.
  induction p; crush.
Qed.
Hint Rewrite beq_phi_sym.

Function beq_tau (t t' : T) : bool :=
 match t, t' with
 | tv_t alpha, tv_t beta => beq_var alpha beta
 | cint, cint => true
 | (cross t0 t1), (cross t0' t1') => andb (beq_tau t0 t0') (beq_tau t1 t1')
 | (arrow t0 t1), (arrow t0' t1') => andb (beq_tau t0 t0') (beq_tau t1 t1')
 | ptype t, ptype t' => (beq_tau t t')
(* No alpha conversion for the moment. *)
 | utype alpha kappa tau, utype alpha' kappa' tau' =>
   andb (andb (beq_var alpha alpha') (beq_kappa kappa kappa'))
        (beq_tau tau tau')
 | etype p alpha kappa tau, etype p' alpha' kappa' tau' =>
   andb (andb (beq_phi p p')  (beq_var alpha alpha'))
        (andb (beq_kappa kappa kappa') (beq_tau tau tau'))
   
 | _ , _ => false
end.
Hint Resolve beq_tau.

Definition beq_t := beq_tau.
End TauTypingInfo.


