(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Getting the heap really right including issues of searching
  through the heap, assigning into the heap and getting an
  address in the heap.

  Alpha conversion can probably be ignored here.

*)

Set Implicit Arguments.
Require Export LanguageModuleDef.
Require Export DynamicSemanticsTypeSubstitution.
Require Export DynamicSemanticsHeapObjects.
Require Export DynamicSemantics.
Require Export Tacticals.

Require Export TestUtilities.


Example assign_int :
 S (H.ctxt x  (i_e (i_i 0)) hdot)
   (seq (e_s (assign (p_e x []) (i_e (i_i 1)))) (retn (p_e x [])))
   (H.ctxt x  (i_e (i_i 1)) hdot)
   (seq (e_s (i_e (i_i 1))) (retn (p_e x []))).
Proof.
  apply S_seq_3_10.
  apply S_exp_3_9_1.
  eapply R_assign_3_2; 
  eauto with Chapter3.
Qed.

Example assign_int_no_nils :
 S (H.ctxt x  (i_e (i_i 0)) hdot)
   (seq (e_s (assign (p_e x []) (i_e (i_i 1)))) (retn (p_e x [])))
   (H.ctxt x  (i_e (i_i 1)) hdot)
   (seq (e_s (i_e (i_i 1))) (retn (p_e x []))).
Proof.
 eauto 20 with Chapter3.
Qed.

Example assign_x_gets_address_y :
 S (H.ctxt x  (i_e (i_i 0)) (H.ctxt y (i_e (i_i 0)) hdot))
   (e_s (assign (p_e x []) (amp (p_e y []))))
   (H.ctxt x  (amp (p_e y [])) (H.ctxt y (i_e (i_i 0)) hdot))
   (e_s (amp (p_e y []))).
Proof.
  apply S_exp_3_9_1.
  eapply R_assign_3_2;
    eauto 20 with Chapter3.
Qed.

(* TODO make this a statement not a right hand side. *)
Example return_address_of_y :
 S (H.ctxt x (amp (p_e y []))  (H.ctxt y (i_e (i_i 0)) hdot))
   (e_s (p_e x []))
   (H.ctxt x (amp (p_e y []))  (H.ctxt y (i_e (i_i 0)) hdot))
   (e_s (amp (p_e y []))).
Proof.
  apply S_exp_3_9_1.
  eapply R_get_3_1;
  (try reflexivity;
   eauto 20 with Chapter3).
Qed.

Example return_ptr_to_y:
 S
   (H.ctxt x (amp (p_e y []))  (H.ctxt y (i_e (i_i 0)) hdot))
   (e_s (star (p_e x [])))
   (H.ctxt x (amp (p_e y []))  (H.ctxt y (i_e (i_i 0)) hdot))
   (e_s (star (amp (p_e y [])))).
Proof.
  (* eauto 20 with Chapter3. *)
  apply S_exp_3_9_1.
  apply R_star_3_10_1.
  eapply R_get_3_1.
  try reflexivity.
  try reflexivity.
  Focus 2.
  eauto 20 with Chapter3.
  Focus 2.
  eauto 20 with Chapter3.
  apply get_pdot.
  eauto 20 with Chapter3.  
Qed.

Example return_contents_of_y :
 S  (H.ctxt x (amp (p_e y []))  (H.ctxt y (i_e (i_i 0)) hdot))
    (e_s (star (amp (p_e y []))))
    (H.ctxt x (amp (p_e y []))  (H.ctxt y (i_e (i_i 0)) hdot))
    (e_s (p_e y [])).
Proof.
  eauto 20 with Chapter3.
Qed.

