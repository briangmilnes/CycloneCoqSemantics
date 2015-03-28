(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

 This defines the formal syntax, pg. 61.

*)

Set Implicit Arguments.
Require Export LanguageModuleDef.

Fixpoint subst_Gamma (g : Gamma) (tau : Tau) (alpha : TVar) : Gamma :=
  match g with
   | G.dot => G.dot
   | (G.ctxt x tau' g') => 
     (G.ctxt x (T.subst_Tau tau' tau alpha) (subst_Gamma g' tau alpha))
end.
Functional Scheme subst_Gamma_ind := Induction for subst_Gamma Sort Prop.
