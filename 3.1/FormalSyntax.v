(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  The top level syntax bound together.

  Needs work now that I have modules for these.

*)

(*
  Typographic conventions 

   Upper case for inductive types. 
   Using only Dan's greek names.
   Context is C. 
   P for path (p).
   Phi went from lower case delta/ampersand to human readable witnesschange/aliases.
   s for the judgement, St for statements and State for states.

   YE for elements that go in lists of type Y.
*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.

Require Export CpdtTactics.
Require Export Case.
Require Export KappaModuleDef.
Import KappaModule.
Require Export TVarModuleDef.
Import TVarModule.
Require Export TauModuleDef.
Import TauModule.

Definition TVar := TVarModule.Var.
Definition tvar := TVarModule.var.

Function removeTVar (alpha : TVar) (tvars : list TVar) : list TVar :=
  match alpha, tvars with 
   | _, [] => []
   | tvar n, (tvar n') :: tvars' =>
     if beq_nat n n' 
     then removeTVar alpha tvars' 
     else (tvar n) :: (removeTVar alpha tvars')
  end.

Function FreeVariablesTau (tau : Tau) : list TVar :=
  match tau with 
   | tv_t alpha   => [alpha]
   | cint         => []
   | cross t0 t1  => (FreeVariablesTau t0) ++ (FreeVariablesTau t1)
   | arrow t0 t1  => (FreeVariablesTau t0) ++ (FreeVariablesTau t1)
   | ptype t      => (FreeVariablesTau t)
   | utype alpha _ t    => removeTVar alpha (FreeVariablesTau t)
   | etype _ alpha _ t  => removeTVar alpha (FreeVariablesTau t)
  end.

Require Export EVarModuleDef.
Import EVarModuleDef.
Definition EVar := EVarModule.Var.
Definition evar := EVarModule.var.

Require Export PathModuleDef.
Import PathModuleDef.
Definition PE  := PathModule.PE.
Definition P   := PathModule.P.
Definition IPE := PathModule.IPE.

Inductive I  : Type :=  
 | i_i       : Z -> I.                         (* An integer value in an expression or statement. *)

Inductive St : Type :=                        (* Terms for statements. *)
 | e_s       : E   -> St                      (* An expression in a statement. *)
 | retn      : E   -> St                      (* Returns are required in this syntax. *)
 | seq       : St  -> St -> St                (* Statement sequencing. *)
 | if_s      : E   -> St -> St   -> St        (* if expression in a statement. *)
 | while     : E   -> St -> St                (* A while statement. *)
 | letx      : EVar -> E -> St   -> St        (* A let expression. *)
 | open      : E -> TVar -> EVar -> St -> St  (* open an existential package (elimination) to a value. *)
 | openstar  : E -> TVar -> EVar -> St -> St  (* open an existential package (elimination) with a pointer to the value. *)
with E : Type :=                              (* Terms for expressions. *)
 | i_e       : I -> E                         (* An integer value in an expression. *)
 | p_e       : EVar -> list PE -> E           (* This is a term that derefences a path into the value of the variable. *)
 | f_e       : F -> E                         (* A function identifier in an expression or statement. *)
 | amp       : E -> E                         (* Take the address of an expression. *)
 | star      : E -> E                         (* Derefence an expression of a pointer type. *)
 | cpair     : E -> E -> E                    (* A pair in an expression. *)
 | dot       : E -> IPE -> E                  (* A deference of a pair. *)
 | assign    : E -> E -> E                    (* Equality expression. *)
 | appl      : E -> E -> E                    (* Application expression. app is append. *)
 | call      : St -> E                        (* A call expression for the semantics use. *)
 | inst      : E -> Tau -> E                  (* Type instantiation, e[\tau]. *)
 | pack      : Tau -> E -> Tau -> E           (* Existential type introduction. *)
with F : Type :=
 | dfun      : Tau -> EVar -> Tau -> St -> F  (* Function definition. *)
 | ufun      : TVar -> Kappa -> F -> F        (* Univerally quantified polymorphic function definition.  *)
.

Scheme St_ind_mutual := Induction for St Sort Prop
with    E_ind_mutual := Induction for E Sort Prop
with    F_ind_mutual := Induction for F Sort Prop.
Combined Scheme Term_ind_mutual from St_ind_mutual, E_ind_mutual, F_ind_mutual.

(* Make a value type judgement. The thesis does this syntactically 
but that's not representable in Coq. *)

Inductive Value : E -> Prop :=
 | IIsAValue    : forall (i : I),              Value (i_e i)
                                                     
 | AmpIsAValue  : forall (x : EVar) (p : P),   Value (amp (p_e x p)) 

 | DfunIsAValue : forall (t1 t2 : Tau) (x : EVar) (s : St), 
                        Value (f_e (dfun t1 x t2 s))
 | UfunIsAValue : 
     forall (t : TVar) (k : Kappa) (f : F),
       Value (f_e (ufun t k f))

 | PairIsAValue :
     forall (v0 v1 : E), 
       Value v0 ->
       Value v1 ->
       Value (cpair v0 v1)

(* Bug 40, forget a subvalue here. *)
 | PackIsAValue :
     forall (tau tau': Tau) (v : E),
       Value v -> 
       Value (pack tau v tau').

(* The abstract syntax of H values. *)

Definition HE : Type := prod EVar E.
Definition H  : Type := list HE.

(* Bug 2, 3 *)

Function getH (h : H) (x : EVar) : option E :=
    match x, h with 
    | x, (y,v) :: h' =>
      if beq_evar x y
      then Some v 
      else getH h' x
    | _ , nil => None
  end.

(* TODO move to beq_evar. *)

Function setH (h : H) (x : EVar) (e : E) : H :=
  match x, h with
    | evar x', (evar y',v) :: h' =>
      if beq_nat x' y'
      then [(x,e)] ++ h'
      else (evar y',v) :: (setH h' x e)
    | (evar x'), _ => [(x,e)]
 end.

Function deleteH (h : H) (x : EVar) : H :=
    match x, h with
    | evar x', (evar y',v) :: h' =>
      if beq_nat x' y'
      then h'
      else (evar y',v) :: (deleteH h' x)
    | _, [] => []
 end.

(* The context is three part: kind assignment, type assignments and path assignments. *)

Definition DE : Type := prod TVar Kappa.
Definition Delta     := list DE.

Function getD (d : Delta) (alpha : TVar) : option Kappa :=
  match alpha, d with 
    | a, (b, k) :: d' =>
      if beq_tvar a b 
      then Some k 
      else getD d' alpha
    | _ , nil => None
  end.

Function setD (d : Delta) (alpha : TVar) (k : Kappa) : Delta :=
  match alpha, d with 
    | tvar a', (tvar b', k') :: d' =>
      if beq_nat a' b' 
      then (alpha,k) :: d' 
      else (tvar b', k') :: (setD d' alpha k)
    | _ , nil => [(alpha,k)]
  end.

Function deleteD (d : Delta) (alpha : TVar) : Delta :=
    match alpha, d with
    | tvar x', (tvar y',v) :: h' =>
      if beq_nat x' y'
      then h'
      else (tvar y',v) :: (deleteD h' alpha)
    | _, [] => []
 end.

Function DeleteKinding (alpha : TVar) (d : Delta) : Delta :=
  match alpha, d with 
   | _, [] => [] 
   | (tvar n), (tvar n', k) :: d' => 
     if beq_nat n n' 
     then DeleteKinding alpha d'
     else (tvar n', k) :: DeleteKinding alpha d'             
  end.

Function KindTVarsAtA (tau : Tau) : Delta :=
  match tau with
   | tv_t t            => [(t, A)]
   | cint              => []
   | cross t0 t1       => KindTVarsAtA t0 ++ KindTVarsAtA t1
   | arrow t0 t1       => KindTVarsAtA t0 ++ KindTVarsAtA t1
   | ptype t           => KindTVarsAtA t 
   | utype   alpha k t => DeleteKinding alpha (KindTVarsAtA t)
   | etype p alpha k t => DeleteKinding alpha (KindTVarsAtA t)
  end.

Function InDomD (alpha : TVar) (d : Delta) : bool :=
  match alpha, d with
   | _, [] => true
   | tvar n, ((tvar n'), _) :: d' =>
     if beq_nat n n' 
     then false 
     else InDomD alpha d'
 end.

Function KindingUnion (d d' : Delta) : Delta :=
  match d with 
   | (alpha,k) :: d0 => 
     if InDomD alpha d' 
     then KindingUnion d0 d'
     else (alpha, k) :: KindingUnion d0 d'
   | [] => []
  end.

Function KindUnkindedTVarsAtB (tau : Tau) (d : Delta) : Delta :=
  match tau with
   | tv_t t            => 
     if InDomD t d then [] else [(t, B)]
   | cint              => []
   | cross t0 t1       => KindingUnion (KindUnkindedTVarsAtB t0 d) 
                                       (KindUnkindedTVarsAtB t1 d)
   | arrow t0 t1       => KindingUnion (KindUnkindedTVarsAtB t0 d) 
                                       (KindUnkindedTVarsAtB t1 d)
   | ptype t           => KindUnkindedTVarsAtB t d
   | utype   alpha k t => DeleteKinding alpha (KindUnkindedTVarsAtB t d)
   | etype p alpha k t => DeleteKinding alpha (KindUnkindedTVarsAtB t d)
  end.

Function DisjointKinding (d d' : Delta) : bool :=
  match d with
   | (alpha,k) :: d0 => 
     if InDomD alpha d' then false else DisjointKinding d0 d
   | [] => true
  end.

Definition GE : Type := prod EVar Tau.
Definition Gamma     := list GE.

Function getG (g : Gamma) (x: EVar) : option Tau :=
  match x, g with 
    | x, (y, t) :: g' =>
      if beq_evar x y 
      then Some t
      else getG g' x
    | _, [] => None
  end.

(* The thesis uses a statement here, (p_e x p), but it certainly makes the
  proofs unnecessarily hard. So I'll use a pair. *)
Definition UE        := prod (prod EVar P) Tau.
Definition Upsilon   := list UE.
 
Inductive getU : Upsilon -> EVar -> P -> Tau -> Prop :=
  | getU_top  : forall (u : Upsilon) (x : EVar) (p : P) (tau : Tau),
                 getU ([((x,p),tau)] ++ u) x p tau
  | getU_next : forall (u : Upsilon) (x y: EVar) (p p': P) (tau tau': Tau),
                 beq_evar x y = false \/ beq_path p p' = false ->
                 getU u x p tau ->
                 getU ([((y,p'),tau')] ++ u) x p tau.

(* TODO warning on inversion, do I need a relation here also? *)
Function NotInDomU (u : Upsilon) (x : EVar) (p : P) : Prop :=
  match x, u with 
    | _, [] => True
    | x, (((y,p'),_) :: u') =>
       if andb (beq_evar x y) (beq_path p p')
       then True
       else NotInDomU u' x p
   end.
