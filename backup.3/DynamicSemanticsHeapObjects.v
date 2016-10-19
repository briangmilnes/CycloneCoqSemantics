(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

 This defines the dynamic semantics of heap objects, pg. 60.

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.

Require Export FormalSyntax.

(* TODO can I make get and set assume Value v? then make then functions? *)

Inductive get : E -> P -> E -> Prop := 
(* Dan Bug, v' required. *)
 | get_pdot: forall (v v': E),
               Value v ->
               get v [] v'
 | get_l:    forall (v v0 v1 : E) (p : P),
               Value v  ->
               Value v0 ->
               Value v1 ->
               get v0 p v ->
               get (cpair v0 v1) ((i_pe (i_i 0)) :: p) v
 | get_r:    forall (v v0 v1 : E) (p : P),
               Value v  ->
               Value v0 ->
               Value v1 ->
               get v1 p v ->
               get (cpair v0 v1) ((i_pe (i_i 1)) :: p) v
 | get_pack: forall (v v1 : E) (p : P) (tau tau' : Tau) (alpha : TVar) (k : Kappa),
               Value v  ->
               Value v1 ->
               get v1 p v ->
               get (pack tau' v1 (etype aliases alpha k tau)) (u_pe :: p) v.
               
Inductive set : E -> P -> E -> E -> Prop :=
  (* Dan ? *)
  | set_ip: forall (v v' v'': E),
                Value v  ->
                Value v' -> 
                Value v'' -> 
                set v' [] v v''


  | set_l:    forall (v v' v0 v1 : E) (p : P),
                Value v  ->
                Value v' ->
                Value v0 ->
                set v0 p v v' ->
                set (cpair v0 v1)  ((i_pe (i_i 0)) :: p) v (cpair v' v1)
  | set_r:    forall (v v' v0 v1 : E) (p : P),
                Value v  ->
                Value v' ->
                Value v0 ->
                set v1 p v v' ->
                set (cpair v0 v1)  ((i_pe (i_i 1)) :: p) v (cpair v0 v')
  | set_pack: forall (v v' v1 : E) (p : P) (tau tau' : Tau) (q : Phi) (alpha : TVar) (k : Kappa),
                Value v  ->
                Value v' ->
                Value v1 ->
                set (pack tau' v1 (etype q alpha k tau)) (u_pe :: p) v (pack tau' v' (etype q alpha k tau)).
