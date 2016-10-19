(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Getting the heap really right including issues of searching
  through the heap, assigning into the heap and getting an
  address in the heap.

  Alpha conversion can probably be ignored here.

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.

Require Export FormalSyntax.
Require Export DynamicSemanticsTypeSubstitution.
Require Export DynamicSemanticsHeapObjects.
Require Export DynamicSemantics.
Require Export Tacticals.

Require Export TestUtilities.


Example assign_int :
 S ([] ++ [(x, (i_e (i_i 0)))] ++ [])
   (seq (e_s (assign (p_e x []) (i_e (i_i 1)))) (retn (p_e x [])))
   ([] ++ [(x, (i_e (i_i 1)))] ++ [])
   (seq (e_s (i_e (i_i 1))) (retn (p_e x []))).
Proof.
  apply S_seq_3_10.
  apply S_exp_3_9_1.
  apply R_assign_3_2; 
  eauto with Chapter3.
Qed.

Example assign_int_no_nils :
 S [(x, (i_e (i_i 0)))]
   (seq (e_s (assign (p_e x []) (i_e (i_i 1)))) (retn (p_e x [])))
   [(x, (i_e (i_i 1)))]
   (seq (e_s (i_e (i_i 1))) (retn (p_e x []))).
Proof.
 eauto 20 with Chapter3.
Qed.

Example assign_x_gets_address_y :
 S [(x, (i_e (i_i 0))); (y, (i_e (i_i 0)))]
   (e_s (assign (p_e x []) (amp (p_e y []))))
   [(x, (amp (p_e y []))); (y, (i_e (i_i 0)))]
   (e_s (amp (p_e y []))).
Proof.
  debug eauto 20 with Chapter3.
  apply S_exp_3_9_1.
  debug eauto 20 with Chapter3.
  (*   apply R_assign_3_2. *)
Admitted.

