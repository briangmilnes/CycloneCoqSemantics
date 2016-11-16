(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION", Daniel Grossman, August 2003 *)
(* Other required infrastructure from LN *)
(* Brian Milnes 2016 *)

Set Implicit Arguments.
Require Export LibVarPathEnv Cyclone_Formal_Syntax.

(* Questions:

 Do I have all of the following and what's actually necessary.

 SPLIT THIS INTO FILES, it's too big. 

 Subst for FTV in Envs

  Do I need body? 
    He says it is 'lighter and handier from a proof engineering point of view'. 
    He uses it a lot but NOT in Fsub because he's typing not executing in that
    model.

  I think I need locally closed in Value.

*)
