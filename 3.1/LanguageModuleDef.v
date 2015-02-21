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
  (* I'd have to functorize this to show the dependencies to TM.EV and Path and so on. *)
  Module EVP := EVarPathModule.

  Module D := ContextFun T.TV T.K.
  (* Now what happens here if I use D.K/D.T vs TV.T T.K ? *)
  Definition Delta    := (D.Context  T.TV.Var Kappa).
  Definition ddot     := (D.cdot     T.TV.Var Kappa).
  Definition dctxt    := (D.ctxt     T.TV.Var Kappa).
  (* Can I just drop these and get rid of some unfolding? Seems likely. *)

  Module U := ContextFun EVarPathModule T.
  Definition Upsilon  := (U.Context EVP.T Tau).
  Definition udot     := (U.cdot EVP.T Tau).
  Definition uctxt    := (U.ctxt EVP.T Tau).

  Module H := ContextFun TM.EV TM.
  Definition Heap     := (H.Context TM.EV.T TM.E).
  Definition hdot     := (H.cdot    TM.EV.T TM.E).
  Definition hctxt    := (H.ctxt    TM.EV.T TM.E).
  

  Module G := ContextFun TM.EV T.
  Definition Gamma    := (G.Context TM.EV.T Tau).
  Definition gdot     := (G.cdot    TM.EV.T Tau).
  Definition gctxt    := (G.ctxt    TM.EV.T Tau).

End LanguageModule.

Export LanguageModule.
