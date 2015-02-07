(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

 This defines the dynamic semantics of heap objects, pg. 60.

*)


Require Export LanguageModuleDef.

Inductive get : E -> Path -> E -> Prop := 
 | get_pdot: forall (v : E),
               Value v ->
               get v [] v
 | get_l:    forall (v v0 v1 : E) (p : Path),
               Value v  ->
               Value v0 ->
               Value v1 ->
               get v0 p v ->
               get (cpair v0 v1) ((i_pe zero_pe) :: p) v
 | get_r:    forall (v v0 v1 : E) (p : Path),
               Value v  ->
               Value v0 ->
               Value v1 ->
               get v1 p v ->
               get (cpair v0 v1) ((i_pe one_pe) :: p) v
 | get_pack: forall (v v1 : E) (p : Path) (tau tau' : Tau) (alpha : TVar) (k : Kappa),
               Value v  ->
               Value v1 ->
               get v1 p v ->
               get (pack tau' v1 (etype aliases alpha k tau)) (u_pe :: p) v.
               
Inductive set : E -> Path -> E -> E -> Prop :=
  | set_ip: forall (v v' : E),
                Value v  ->
                Value v' -> 
                set v' [] v v

  | set_l:    forall (v v' v0 v1 : E) (p : Path),
                Value v  ->
                Value v' ->
                Value v0 ->
                set v0 p v v' ->
                set (cpair v0 v1)  ((i_pe zero_pe) :: p) v (cpair v' v1)

  | set_r:    forall (v v' v0 v1 : E) (p : Path),
                Value v  ->
                Value v' ->
                Value v0 ->
                set v1 p v v' ->
                set (cpair v0 v1)  ((i_pe one_pe) :: p) v (cpair v0 v')

  | set_pack: forall (v v' v1 : E) (p : Path) (tau tau' : Tau) 
                     (q : Phi) (alpha : TVar) (k : Kappa),
                Value v  ->
                Value v' ->
                Value v1 ->
                set (pack tau' v1 (etype q alpha k tau))
                    (u_pe :: p) v (pack tau' v' (etype q alpha k tau)).
