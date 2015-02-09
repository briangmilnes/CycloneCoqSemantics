(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

 This defines the static semantics of typing in the heap, pg 64.

*)

Set Implicit Arguments.

Require Export LanguageModuleDef.
Require Export DynamicSemanticsTypeSubstitution.
Require Export StaticSemanticsKindingAndContextWellFormedness.

(*
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
    | _, _, _, (cross t0 t1), ((i_pe zero_pe) :: p') =>
      match gettype u x (p ++ [(i_pe zero_pe)]) t0 p' with
          | None => None
          | Some tau  => Some tau
      end
    | _, _, _, (cross t0 t1), ((i_pe one_pe) :: p') =>
      match gettype u x (p ++ [(i_pe one_pe)]) t1 p' with
          | None => None
          | Some tau  => Some tau
      end
    | _, _, _, _, _ => None
end.
*)

(* Functional Scheme gettype_ind := Induction for gettype Sort Prop.*)

Inductive gettype : Upsilon -> EV.T -> Path -> T.T -> Path -> T.T -> Prop :=
  | gettype_nil       : 
      forall (u : Upsilon) (x : EV.T) (p : Path) (tau : T.T),
        gettype u x p tau [] tau

  | gettype_pair_zero : 
      forall (u : Upsilon) (x : EV.T) (p p': Path) (t0 t1 tau : T.T),
        gettype u x  (p ++ [Pth.i_pe Pth.zero_pe]) t0 p' tau ->
        gettype u x p (T.cross t0 t1) ([Pth.i_pe Pth.zero_pe] ++ p') tau

  | gettype_pair_one  : 
      forall (u : Upsilon) (x : EV.T) (p p': Path) (t0 t1 tau : T.T),
        gettype u x  (p ++ [Pth.i_pe Pth.one_pe]) t1 p' tau ->
        gettype u x p (T.cross t0 t1) ([Pth.i_pe Pth.one_pe] ++ p') tau

  (* TODO is there a bug here ? *)
  | gettype_etype     : 
      forall (u : Upsilon) (x : EV.T) (p p': Path) (tau tau' tau'': T.T) 
             (alpha : TV.T) (k : Kappa),
        U.map u (x,p) = Some tau'' ->
        gettype u x (p ++ [Pth.u_pe]) (subst_Tau tau' tau'' alpha) p' tau ->
        gettype u x p (T.etype aliases alpha k tau') ([Pth.u_pe] ++ p') tau.


