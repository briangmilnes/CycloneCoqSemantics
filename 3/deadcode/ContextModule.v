(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  An attempt at a context module.

*)

Require Import List.
Export ListNotations.
Require Export ZArith.
Require Import Init.Datatypes.

Require Import DynamicSemanticsTypeSubstitution.
Require Export CpdtTactics.
Require Export Case.
Require Import FormalSyntax.

Set Implicit Arguments.

(* Modules for the operations. *)

Module Type Context_Type.
  Parameter K    : Type.
  Parameter K_eq : K -> K -> bool.
  Parameter T    : Type.

  
  Parameter Context : Type -> Type -> Type.
  Parameter In      : K -> Context K T ->  Prop.
  Parameter NoDup   : Context K T -> Prop.

  Parameter empty   : Context K T.
  Parameter add     : Context K T -> K -> T -> Context K T.
  Parameter map     : Context K T -> K -> option T.
  Parameter ink     : Context K T -> K -> bool.
  Parameter inkt    : Context K T -> K -> T ->  bool.
  Parameter equal   : Context K T -> Context K T -> bool.

  Parameter extends  : Context K T -> Context K T -> bool.

(*
  Parameter extends1 : Context K T -> K -> T -> Context K T -> Prop.
  Parameter remove  : Context K T -> K -> Context K T.
*)
End Context_Type.

Module Type Context_Base_Types.
  Parameter K    : Type.
  Parameter K_eq : K -> K -> bool.
  Parameter T    : Type.
  Parameter T_eq : T -> T -> bool.
End Context_Base_Types.

Module Context (CBT : Context_Base_Types) : Context_Type.
  Definition K    := CBT.K.
  Definition K_eq := CBT.K_eq.
  Definition T    := CBT.T.
  Definition T_eq := CBT.T_eq.

  Inductive Context' (K : Type) (T : Type) : Type :=
  | Ctxt_dot  : Context' K T
  | Ctxt      : K -> T -> Context' K T -> Context' K T.

  Inductive In' (k : K) : Context' K T ->  Prop := 
   | In_hd : forall k' t' c, K_eq k k' = true -> In' k (Ctxt k' t' c)
   | In_tl : forall k' t' c, In' k c -> In' k (Ctxt k' t' c).

  Inductive  NoDup' : Context' K T -> Prop :=
    | NoDup_dot  : NoDup' (Ctxt_dot K T)
    | NoDup_ctxt : forall k t c,
                     NoDup' c ->
                     ~In' k c ->
                     NoDup' (Ctxt k t c).

  Definition In := In'.
  Definition NoDup := NoDup'.
  Definition Context := Context'.

  Definition empty  := Ctxt_dot K T.

  Fixpoint add (f : Context K T) (k: K) (t : T)  : Context K T :=
    match f with
      | Ctxt_dot => (Ctxt k t (Ctxt_dot K T))
      | (Ctxt k' t' f') =>
        match K_eq k k' with
          | true  => (Ctxt k  t  f')
          | false => (Ctxt k' t' (add f' k t))
        end
    end.

  Fixpoint map (f : Context K T) (k: K) : option T :=
    match f with
      | Ctxt_dot => None
      | (Ctxt k' t' f') =>
        match K_eq k k' with
          | true  => Some t'
          | false => (map f' k)
        end
    end.

  Fixpoint ink (f : Context K T) (k: K) : bool :=
    match f with
      | Ctxt_dot => false
      | (Ctxt k' t' f') =>
        match K_eq k k' with
          | true  => true
          | false => (ink f' k)
        end
    end.

  Fixpoint inkt (f : Context K T) (k: K) (t : T) : bool :=
    match f with
      | Ctxt_dot => false
      | (Ctxt k' t' f') =>
        match K_eq k k' with
          | true => match T_eq t t' with | true => true | false => (inkt f' k t) end
          | false => (inkt f' k t)
        end
    end.

  Fixpoint lt (f f' : Context K T) : bool :=
    match f with
      | Ctxt_dot => true
      | (Ctxt k' t' f'') =>
        match inkt f' k' t' with
          | true => (lt f'' f')
          | false => false
        end
    end.
    
  Fixpoint equal (f f' : Context K T) : bool :=
    andb (lt f f') (lt f' f).

  Fixpoint extends (c c' : Context K T) : bool :=
    match c with 
     | Ctxt_dot => true
     | Ctxt k t c'' =>
       if inkt c' k t
       then extends c'' c' 
       else false
    end.

End Context.

Module Delta_Base_Types : Context_Base_Types.
  Definition K    := TVar.
  Definition K_eq := beq_tvar.
  Definition T    := Kappa.
  Definition T_eq := beq_kappa.
End Delta_Base_Types.

Module DeltaContext := Context(Delta_Base_Types).
Print DeltaContext.

Module Upsilon_Base_Types : Context_Base_Types.
  Definition K    := (prod EVar P).
  Definition K_eq := beq_evar_p.
  Definition T    := Tau.
  Definition T_eq := beq_tau. 
End Upsilon_Base_Types.

Module UpsilonContext := Context(Upsilon_Base_Types).
Print UpsilonContext.

Module Gamma_Base_Types : Context_Base_Types.
  Definition K    := EVar.
  Definition K_eq := beq_evar.
  Definition T    := Tau.
  Definition T_eq := beq_tau.
End Gamma_Base_Types.

Module GammaContext := Context(Gamma_Base_Types).
Print GammaContext.

Module H_Base_Types : Context_Base_Types.
  Definition K    := EVar.
  Definition K_eq := beq_evar.
  Definition T    := E.
  Definition T_eq := beq_e. 
End H_Base_Types.

Module HContext := Context(H_Base_Types).
Print HContext.

(* Modules for the proofs, I hope. *)

Module Type Context_Axioms.
  Declare Module C : Context_Type.
  Import C.

  Axiom nodup     : forall c,      NoDup c.
  Axiom empty1    : forall k,      map empty k = None.
  Axiom add1      : forall c k t,  map (add c k t) k = Some t.
  Axiom equal1    : forall c c' k t,
                      inkt c k t = true <-> inkt c' k t = true.

(*

  Axiom extends1'  : forall c c', extends c c' ->
                      forall k t, inkt c k t = true -> inkt c' k t = true.
  Axiom extends11 : forall c k t c', 
                      extends1 c k t c' ->
                      (forall k' t', inkt c k' t' = true -> inkt c' k' t' = true) /\
                      (forall k' t', inkt c' k' t' = true ->
                                     (inkt c k' t' = true \/ (k' = k /\ t' = t'))).


  Axiom remove1   : forall c k t, (map (remove (add c k t) k) k) = None.


*)
End Context_Axioms.

(*
Module Context_Axioms_Proofs (C : Context_Type) : Context_Axioms
            with Module C := C.
  Import C.
  
  Theorem nodup:
    forall c, NoDup c.
   Admitted.
End Context_Axioms_Proofs.
*)


Module Type Context_Theorems.
  Declare Module C : Context_Type.
  Import C.

  Axiom extension_agreement :
    forall c c' k o, 
      extends c c' = true ->
      map c  k = o ->
      map c' k = o.
                
  Axiom extension_absence :
    forall c c' k, 
      extends c c' = true ->
      map c' k = None ->
      map c  k = None.

  Axiom extension_empty :
    forall c,
      extends c empty = true ->
      equal c empty = true.
End Context_Theorems.

