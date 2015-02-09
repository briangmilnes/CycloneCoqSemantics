(*
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

   Bind all the modules together, rename things for convenience.

   Require Export LanguageModuleDef to get this.
*)


Set Implicit Arguments.
Require Export List.
Export ListNotations.
Require Export ZArith.
Require Export Init.Datatypes.

Require Export CpdtTactics.
Require Export Case.

Require Import EVarModuleDef.
Require Import EVarPathModuleDef.
Require Import TauModuleDef.
Require Import PathModuleDef.
Require Import PhiModuleDef.
Require Import TermModuleDef.
Require Import DeltaModuleDef.
Require Import GammaModuleDef.
Require Import HeapModuleDef.
Require Import UpsilonModuleDef.

Module LanguageModule.
  Module T   := TauModule.
  (* Paths come from terms. *)
  Module Pth := PathModule.   

  Export TermModule.
  Module TM := TermModule.
  Module EVP := EVarPathModule.

  Module D := DeltaModule.
  Definition Delta    := (D.Context  D.K D.T).
  Definition ddot     := (D.cdot D.K D.T).
  Definition dctxt    := D.ctxt.

  Module U := UpsilonModule.
  Definition Upsilon  := (U.Context U.K U.T).
  Definition udot     := (U.cdot U.K U.T).
  Definition uctxt    := U.ctxt.

  Module H := HeapModule.
  Definition Heap     := (H.Context H.K H.T).
  Definition hdot     := (H.cdot H.K H.T).
  Definition hctxt    := H.ctxt.

  Module G := GammaModule.
  Definition Gamma    := (G.Context G.K G.T).
  Definition gdot     := (G.cdot G.K G.T).
  Definition gctxt    := G.ctxt.
End LanguageModule.

Export LanguageModule.
