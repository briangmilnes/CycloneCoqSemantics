(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

 This defines the static semantics of typing in the heap, pg 64.

*)

Set Implicit Arguments.

Require Export Cyclone_Formal_Syntax.
Require Export Cyclone_LN_Types_In_Terms.
Require Export LibVarPathEnv.
Require Export List.
Close Scope list_scope.
Import LibEnvNotations.
Import LVPE.LibVarPathEnvNotations.

(* Bug. *)
Inductive gettype : Upsilon -> var -> Path -> Tau -> Path -> Tau -> Prop :=
  | gettype_nil: 
      forall (u : Upsilon) (x : var) (p : Path) (tau : Tau),
        gettype u x p tau nil tau

  | gettype_pair_zero: 
      forall (u : Upsilon) (x : var) (p p': Path) (t0 t1 tau : Tau),
        gettype u x (app p (cons (i_pe zero_pe) nil)) t0 p' tau ->
        gettype u x p (cross t0 t1) (app (cons (i_pe zero_pe) nil) p') tau

  | gettype_pair_one: 
      forall (u : Upsilon) (x : var) (p p': Path) (t0 t1 tau : Tau),
        gettype u x (app p (cons (i_pe one_pe) nil)) t1 p' tau ->
        gettype u x p (cross t0 t1) (app (cons (i_pe one_pe) nil) p') tau

  | gettype_etype: 
      forall (u : Upsilon) (x : var) (p p': Path) (tau tau' tau'': Tau) 
             (k : Kappa),
        LVPE.V.get (x,p) u = Some tau'' ->
        gettype u x (app p (cons u_pe nil)) (T.open tau'' tau') p' tau ->
        gettype u x p (etype aliases k tau') (app (cons u_pe nil) p') tau.

Hint Constructors gettype.
Hint Extern 3 (gettype _ _ _ _ nil _)
=> idtac "(gettype _ _ _ _ nil _)"; trace_goal; try solve[apply gettype_nil; auto].

Hint Extern 3 (gettype _ _ _ (etype _ _ _) _ _)
=> idtac "(gettype _ _ _ (etype _ _ _) _ _)"; trace_goal; try solve[apply gettype_etype; auto].

Hint Extern 3 (gettype _ _ _ (cross _ _) (app (cons (i_pe zero_pe) nil) _) _) 
=> idtac "(gettype _ _ _ (cross _ _) (app (cons (i_pe zero_pe) nil) _) _)"; trace_goal; try solve[apply gettype_pair_zero; auto].

Hint Extern 3 (gettype _ _ _ (cross _ _) (app (cons (i_pe one_pe) nil) _) _) 
=> idtac "(gettype _ _ _ (cross _ _) (app (cons (i_pe one_pe) nil) _) _)"; trace_goal; try solve[apply gettype_pair_one; auto].

Hint Extern 3 (gettype _ _ _ (cross _ _) (cons (i_pe zero_pe) nil) _) 
=> idtac "(gettype _ _ _ (cross _ _) (cons (i_pe zero_pe) nil) _)"; trace_goal; try solve[apply gettype_pair_zero; auto].

Hint Extern 3 (gettype _ _ _ (cross _ _) (cons (i_pe one_pe) nil) _) 
=> idtac "(gettype _ _ _ (cross _ _) (cons (i_pe one_pe) nil) _)"; trace_goal; try solve[apply gettype_pair_one; auto].
