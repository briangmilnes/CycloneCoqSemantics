(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

 This defines the dynamic semantics of heap objects, pg. 60.

*)

Set Implicit Arguments.
Require Export List.
Require Export Cyclone_Formal_Syntax Cyclone_LN_Types_In_Terms.
Open Scope env_scope.
Open Scope list_scope.
Import ListNotations.

Inductive get' : E -> Path -> E -> Prop := 
 | get'_pdot: forall (v : E),
               Value v ->
               get' v [] v
 | get'_l:    forall (v v0 v1 : E) (p : Path),
               Value v  ->
               Value v0 ->
               Value v1 ->
               get' v0 p v ->
               get' (cpair v0 v1) ((i_pe zero_pe) :: p) v
 | get'_r:    forall (v v0 v1 : E) (p : Path),
               Value v  ->
               Value v0 ->
               Value v1 ->
               get' v1 p v ->
               get' (cpair v0 v1) ((i_pe one_pe) :: p) v
 | get'_pack: forall (v v1 : E) (p : Path) (tau tau' : Tau) (k : Kappa),
               Value v  ->
               Value v1 ->
               get' v1 p v ->
               get' (pack tau' v1 (etype aliases k tau)) (u_pe :: p) v.
Hint Constructors get'.
               
Inductive set' : E -> Path -> E -> E -> Prop :=
  | set'_ip: forall (v v' : E),
                Value v  ->
                Value v' -> 
                set' v' [] v v

  | set'_l:    forall (v v' v0 v1 : E) (p : Path),
                Value v  ->
                Value v' ->
                Value v0 ->
                set' v0 p v v' ->
                set' (cpair v0 v1)  ((i_pe zero_pe) :: p) v (cpair v' v1)

  | set'_r:    forall (v v' v0 v1 : E) (p : Path),
                Value v  ->
                Value v' ->
                Value v0 ->
                set' v1 p v v' ->
                set' (cpair v0 v1)  ((i_pe one_pe) :: p) v (cpair v0 v')

  | set'_pack: forall (v v' v1 : E) (p : Path) (tau tau' : Tau) 
                     (q : Phi) (alpha : var) (k : Kappa),
                Value v  ->
                Value v' ->
                Value v1 ->
                set' (pack tau' v1 (etype q k tau))
                    (u_pe :: p) v (pack tau' v' (etype q k tau)).
Hint Constructors set'.