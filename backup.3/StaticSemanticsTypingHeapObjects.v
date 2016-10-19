(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

 This defines the static semantics of typing in the heap, pg 64.

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.

Require Export FormalSyntax.
Require Export DynamicSemanticsTypeSubstitution.

Fixpoint gettype (u : Upsilon) (x : EVar) (p : P) (tau : Tau) (p' : P) : option Tau :=
  match u, x, p, tau, p' with
    | _, _, p, _, [] => Some tau
    | _, _, _, (etype aliases alpha k tau'), (u_pe :: p') => 
      match getU u x p with 
          | None => None
          | Some tau'' =>
            match gettype u x (p ++ [u_pe]) (subst_Tau tau' tau'' alpha) p' with
                | None => None
                | Some tau => Some tau
            end
      end
    | _, _, _, (cross t0 t1), ((i_pe (i_i 0)) :: p') =>
      match gettype u x (p ++ [(i_pe (i_i 0))]) t0 p' with
          | None => None
          | Some tau  => Some tau
      end
    | _, _, _, (cross t0 t1), ((i_pe (i_i 1)) :: p') =>
      match gettype u x (p ++ [(i_pe (i_i 1))]) t1 p' with
          | None => None
          | Some tau  => Some tau
      end
    | _, _, _, _, _ => None
end.

Functional Scheme gettype_ind := Induction for gettype Sort Prop.
