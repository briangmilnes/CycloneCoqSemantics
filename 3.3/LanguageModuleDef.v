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
  Include T.Types.
  Definition TVar := T.TV.t.
  (* Paths come from terms. *)
  Module Pth := PathModule.   

  Export TermModule.
  Module TM := TermModule.
  (* I'd have to functorize this to show the dependencies to TM.EV and Path and so on. *)
  Include TM.Types.
  Definition EVar := TM.EV.t.

  Module EVP := EVarPathModule.

  Module D := ContextFun T.TV T.K.
  (* Now what happens here if I use D.K/D.T vs TV.T T.K ? *)
  Definition Delta    := (D.Context  T.TV.Var Kappa).
  Definition ddot     := (D.cdot     T.TV.Var Kappa).
  Definition dctxt    := (D.ctxt     T.TV.Var Kappa).
  (* Can I just drop these and get rid of some unfolding? Seems likely. *)

  Module U := ContextFun EVarPathModule T.
  Definition Upsilon  := (U.Context EVarPathModule.t Tau).
  Definition udot     := (U.cdot    (prod EVar Path) Tau).
  Definition uctxt    := (U.ctxt    (prod EVar Path) Tau).

  Module H := ContextFun TM.EV TM.
  Definition Heap     := (H.Context EVar TM.E).
  Definition hdot     := (H.cdot    EVar TM.E).
  Definition hctxt    := (H.ctxt    EVar TM.E).
  

  Module G := ContextFun TM.EV T.
  Definition Gamma    := (G.Context EVar Tau).
  Definition gdot     := (G.cdot    EVar Tau).
  Definition gctxt    := (G.ctxt    EVar Tau).

End LanguageModule.

Export LanguageModule.
