(*
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

   Bind all the modules together, rename things for convenience.

   Require Export LanguageModule to get this.
*)


Set Implicit Arguments.
Require Export CpdtTactics.
Require Export Case.

Require Export EVarModuleDef.
Require Export EVarPathModuleDef.
Require Export TauModuleDef.
Require Export PathModuleDef.
Require Export PhiModuleDef.
Require Export TermModuleDef.

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

  Definition EVar := TM.EVar.

  Module EVP := EVarPathModule.

  Module D := ContextFun T.TV T.K.
  (* Now what happens here if I use D.K/D.T vs TV.T T.K ? *)
  Definition Delta    := D.Context.
  Module TVSM         := D.KSet.


  (* Can I just drop these and get rid of some unfolding? Seems likely. *)
  Notation "x '~_d' a" := (D.ctxt x a D.dot)
                           (at level 27, left associativity).
  Notation "E '&_d' F" := (D.concat E F) 
                           (at level 28, left associativity).

  Module U := ContextFun EVarPathModule T.
  Definition Upsilon  := U.Context.

  Module H := ContextFun TM.EV TM.
  Definition Heap     := H.Context.

  Module G := ContextFun TM.EV T.
  Definition Gamma    := G.Context.
  Module EVSM         := G.KSet.


  Notation "x '~_g' a" := (G.ctxt x a G.dot)
                           (at level 27, left associativity).
  Notation "E '&_g' F" := (G.concat E F) 
                           (at level 28, left associativity).



  Notation "\{}_t" := (TVSM.empty).
  Notation "\{ x }_t" := (TVSM.singleton x).
  Notation "E \u_t F" := (TVSM.union E F)
                           (at level 37, right associativity).
  Notation "E \n_t F" := (TVSM.inter E F)
                           (at level 36, right associativity).
  Notation "E \-_t F" := (TVSM.remove E F)
                           (at level 35).
  Notation "x \in_t E" := ((TVSM.mem x E) = true) (at level 39).
  Notation "x \notin_t E" := ((TVSM.mem x E) = false) (at level 39).
  Notation "E \c_t F" := (TVSM.subset E F)
                           (at level 38).

  Notation "\{}_e" := (EVSM.empty).
  Notation "\{ x }_e" := (EVSM.singleton x).
  Notation "E \u_e F" := (EVSM.union E F)
                           (at level 37, right associativity).
  Notation "E \n_e F" := (EVSM.inter E F)
                           (at level 36, right associativity).
  Notation "E \-_e F" := (EVSM.remove E F)
                           (at level 35).
  Notation "x \in_e E" := ((EVSM.mem x E) = true) (at level 39).
  Notation "x \notin_e E" := ((EVSM.mem x E) = false) (at level 39).
  Notation "E \c_e F" := (EVSM.subset E F)
                           (at level 38).

End LanguageModule.

Export LanguageModule.
