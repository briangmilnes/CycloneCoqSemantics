(*
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

   Bind all the modules together, rename things for convenience.

   Require Export LanguageModule to get this.
*)

Require Export CpdtTactics.
Require Export Case.

Require Export EVarModuleDef.
Require Export EVarPathModuleDef.
Require Export TauModuleDef.
Require Export PathModuleDef.
Require Export PhiModuleDef.
Require Export TermModuleDef.
Require Export ContextFunDef.

(* Modules:
   kappa - K
   phi   - P
   Path  - Path
   Tau   - T
   Term  - TM
   TVar - TV.
   TVars - TVS.
   EVar - EV.
   EVars - EVS.
*)
Module TM := TermModule.
Include TermModule.Types.
(*
  Print Module K.
  Print Module P.
  Print Module Path.
  Print Module T.
  Print Module TM.
  Print Module TV.
  Print Module TVS.
  Print Module EV.
  Print Module EVS.
*)
Definition tau  := cint.
Definition x    := (EV.var 0).
Definition f           :=
  (dfun cint cint (retn (inst (p_e (fevar x) []) tau))).

  Module D := ContextFun TV K.
  Definition Delta    := D.Context.
  Definition ddot     := D.dot.
  Definition dctxt    := D.ctxt.

  Definition alpha := (TV.var 0).
  Definition d    := (D.ctxt alpha K.A D.dot).
  Definition domd := D.dom d.

  (* Can I just drop these and get rid of some unfolding? Seems likely. *)
  Notation "x '~_d' a" := (D.ctxt x a D.dot)
                           (at level 27, left associativity).
  Notation "E '&_d' F" := (D.concat E F) 
                           (at level 28, left associativity).

  Module G := ContextFun EV T.
  Definition Gamma    := G.Context.

  Notation "x '~_g' a" := (G.ctxt x a G.dot)
                           (at level 27, left associativity).
  Notation "E '&_g' F" := (G.concat E F) 
                           (at level 28, left associativity).




  Module U := ContextFun EVarPathModule T.
  Definition Upsilon  := U.Context.

  Module H := ContextFun EV TM.
  Definition Heap     := H.Context.


  Notation "\{}_t" := (TVS.empty).
  Notation "\{ x }_t" := (TVS.singleton x).
  Notation "E \u_t F" := (TVS.union E F)
                           (at level 37, right associativity).
  Notation "E \n_t F" := (TVS.inter E F)
                           (at level 36, right associativity).
  Notation "E \-_t F" := (TVS.remove E F)
                           (at level 35).
  Notation "x \in_t E" := ((TVS.mem x E) = true) (at level 39).
  Notation "x \notin_t E" := ((TVS.mem x E) = false) (at level 39).
  Notation "E \c_t F" := (TVS.subset E F)
                           (at level 38).

  Notation "\{}_e" := (EVS.empty).
  Notation "\{ x }_e" := (EVS.singleton x).
  Notation "E \u_e F" := (EVS.union E F)
                           (at level 37, right associativity).
  Notation "E \n_e F" := (EVS.inter E F)
                           (at level 36, right associativity).
  Notation "E \-_e F" := (EVS.remove E F)
                           (at level 35).
  Notation "x \in_e E" := ((EVS.mem x E) = true) (at level 39).
  Notation "x \notin_e E" := ((EVS.mem x E) = false) (at level 39).
  Notation "E \c_e F" := (EVS.subset E F)
                           (at level 38).

(* Test for the bug by turning these on. 
Definition tau'  := cint.
Definition x'    := (EV.var 0).
Definition f'           :=
  (dfun cint cint (retn (inst (p_e (fevar x') []) tau'))).
*)
