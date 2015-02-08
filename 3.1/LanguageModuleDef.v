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
Require Import TVarModuleDef.
Require Import EVarPathModuleDef.
Require Import KappaModuleDef.
Require Import PathModuleDef.
Require Import PhiModuleDef.
Require Import TauModuleDef.
Require Import TermModuleDef.
Require Import DeltaModuleDef.
Require Import GammaModuleDef.
Require Import HeapModuleDef.
Require Import UpsilonModuleDef.

Module LanguageModule.
  Export EVarModule.
  Module EVarModule  := EVarModule.
  Definition EVar    := EVarModule.Var.
  Definition evar    := EVarModule.var.
  Definition beq_evar := EVarModule.beq_t.

  Export TVarModule.
  Module TVarModule := TVarModule.
  Definition TVar := TVarModule.Var.
  Definition tvar := TVarModule.var.
  Definition beq_tvar := TVarModule.beq_t.
  
  Export EVarPathModule.
  Module EVarPathModule := EVarPathModule.
  Definition HE := EVarPathModule.T.

  Export KappaModule.
  Module KappaModule := KappaModule.
  Definition Kappa     := KappaModule.T.
  Definition beq_kappa := KappaModule.beq_t.

  Export PathModule.
  Module PathModule := PathModule.
  Definition Path     := PathModule.T.
  Definition beq_path := PathModule.beq_t.

  Export PhiModule.
  Module PhiModule := PhiModule.
  Definition Phi     := PhiModule.T.
  Definition beq_phi := PhiModule.beq_t.

  Export TauModule.
  Module TauModule := TauModuleDef.TauModule.
  Definition Tau     := TauModuleDef.TauModule.T.
  Definition beq_tau := TauModuleDef.TauModule.beq_t.
  
  Export TermModule.
  Module TermModule := TermModule.
  Definition St := TermModule.St.
  Definition E  := TermModule.E.
  Definition F  := TermModule.F.

(* I might have to rename these all two letters to shorten the context 
  printing. *)

  Export DeltaModule.
  Module DM := DeltaModule.
  Definition Delta    := (DeltaModule.Context  TVar Kappa).
  Definition ddot     := (DeltaModule.cdot TVar Kappa).
  Definition dctxt    := DeltaModule.ctxt.

  Export UpsilonModule.
  Module UM := UpsilonModule.
  Definition Upsilon  := (UpsilonModule.Context  HE Tau).
  Definition udot     := (UpsilonModule.cdot HE Tau).
  Definition uctxt    := UpsilonModule.ctxt.

  Export HeapModule.
  Module HM := HeapModule.
  Definition Heap     := (HeapModule.Context  EVar E).
  Definition H        := Heap.
  Definition hdot     := (HeapModule.cdot EVar E).
  Definition hctxt    := HeapModule.ctxt.

  Export GammaModule.
  Module GM := GammaModule.
  Definition Gamma    := (GammaModule.Context  EVar Tau).
  Definition gdot     := (GammaModule.cdot EVar Tau).
  Definition gctxt    := GammaModule.ctxt.
End LanguageModule.

Export LanguageModule.
