(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Punting alpha conversion. 

*)

(* This marks all spots of alpha conversion. *)
Tactic Notation "AdmitAlphaConversion" :=
  admit.

(* I should be able to make this either a beq_t or a map only. *)

