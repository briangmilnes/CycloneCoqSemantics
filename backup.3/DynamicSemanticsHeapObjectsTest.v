(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

 This tests the dynamic semantics of heap objects, pg. 60.

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.

Require Export FormalSyntax.
Require Export DynamicSemanticsHeapObjects.
Require Export TestUtilities.
Require Export Tacticals.


Example test_get_pdot : get vi0 [] vi0.
Proof.
  apply get_pdot.
  eauto 10 with Chapter3.
Qed.

Example test_get_l: get (cpair vi0 vi1) [i_pe (i_i 0)] vi0. 
Proof.
  apply get_l;    
  eauto 10 with Chapter3.
Qed.

Example test_get_r: 
  get (cpair vi0 vi1) [i_pe (i_i 1)] vi1.
Proof.
  apply get_r; 
  eauto 10 with Chapter3.
Qed.

Example test_get_pack: 
  get (pack 
         (cross cint cint) 
         (i_e (i_i 0))
         (etype aliases alpha A cint)) 
      [u_pe]
      (i_e (i_i 0)).
Proof.
  apply get_pack; 
  eauto 10 with Chapter3.
Qed.

Example test_set_ip: set vi0 [] vi1 vi1.
Proof.
  apply set_ip; 
  eauto 10 with Chapter3.
Qed.

Example test_set_l:                 
  set (cpair (i_e (i_i 0)) (i_e (i_i 1)))
      ([i_pe (i_i 0)] ++ [])
      (i_e (i_i 2))
      (cpair (i_e (i_i 2)) (i_e (i_i 1))).
Proof.
  apply set_l;
  eauto 10 with Chapter3.
Qed.

Example test_set_r:
  set (cpair (i_e (i_i 0)) (i_e (i_i 1)))
      ([i_pe (i_i 1)] ++ [])
      (i_e (i_i 2))
      (cpair (i_e (i_i 0)) (i_e (i_i 2))).
Proof.
  apply set_r;
  eauto 10 with Chapter3.
Qed.

Example test_set_pack: 
  set (pack tau' v1 (etype q alpha k tau)) 
      (u_pe :: p0) v (pack tau' v' (etype q alpha k tau)).
Proof.
  apply set_pack;
  eauto 10 with Chapter3.
Qed.

