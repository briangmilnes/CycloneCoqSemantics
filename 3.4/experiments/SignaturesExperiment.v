(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  A set of signatures that we need to construct boolean equalities,
 variables and variable sets. Using the standard library.

 However, the weakness of Coq modules in combination with poor type
 inference does cause us to manhandle the signatures and functors
 a little bit.
*)
Set Implicit Arguments.
Require Import Coq.Structures.Equalities.
Require Export Coq.MSets.MSets.
Require Export Coq.MSets.MSetWeakList.

(* Boolean Equalities and sets of them and variables as their element. *)

Module Type BooleanEquality.
  Include BooleanDecidableType.
  (* These exists in Boolean.v but are not in a module. *)
  Parameter eqb_refl:  forall a,     eqb a a = true.
  Parameter eqb_sym:   forall x y,   eqb x y = eqb y x.
  Parameter eqb_trans: 
    forall x y z, 
      eqb x y = true -> eqb y z = true -> eqb x z = true.
  Parameter eq_trans: 
    forall x y z, eq x y -> eq y z -> eq x z.
  Parameter eqb_to_eq:    forall a b, eqb a b = true -> a = b.
  Parameter eqb_to_neq:   forall a b, eqb a b = false -> a <> b.
  Parameter eqb_iff_eq:    forall a b, eqb a b = true <-> a = b.
  Parameter eqb_iff_neq:   forall a b, eqb a b = false <-> a <> b.
End BooleanEquality.

(* Not used. *)
Module BooleanEqualityFun.
  Include BooleanDecidableType.
  (* These exists in Boolean.v but are not in a module. *)
  Lemma eqb_refl:  forall a,     eqb a a = true. Admitted.
  Lemma eqb_sym:   forall x y,   eqb x y = eqb y x. Admitted.
  Lemma eqb_trans: forall x y z, 
      eqb x y = true -> eqb y z = true -> eqb x z = true.
  Admitted.
  Lemma eq_trans: forall x y z, eq x y -> eq y z -> eq x z.  Admitted.
  Lemma eqb_to_eq:    forall a b, eqb a b = true -> a = b. Admitted.
  Lemma eqb_to_neq:   forall a b, eqb a b = false -> a <> b. Admitted.
  Lemma eqb_iff_eq:    forall a b, eqb a b = true <-> a = b. Admitted.
  Lemma eqb_iff_neq:   forall a b, eqb a b = false <-> a <> b. Admitted.
End BooleanEqualityFun.

(* Repeat the definitions of BooleanEquality and WOps(BooleanEquality) as I can't
get type inference to work otherwise. *)
Module Type BooleanEqualitySet.
   Declare Module BE : BooleanEquality.
   Include WOps(BE).
   Parameter eq : elt -> elt -> Prop.
   Parameter eq_equiv : Equivalence eq.
   Parameter eq_dec : forall x y : elt, {eq x y} + {~ eq x y}.
   Parameter eqb : elt -> elt -> bool.
   Parameter eqb_eq : forall x y : elt, eqb x y = true <-> eq x y.
   Parameter eqb_refl : forall a : elt, eqb a a = true.
   Parameter eqb_sym : forall x y : elt, eqb x y = eqb y x.
   Parameter eqb_trans :
     forall x y z : elt, eqb x y = true -> eqb y z = true -> eqb x z = true.
   Parameter eq_trans : forall x y z : elt, eq x y -> eq y z -> eq x z.
   Parameter eqb_to_eq : forall a b : elt, eqb a b = true -> a = b.
   Parameter eqb_to_neq : forall a b : elt, eqb a b = false -> a <> b.
   Parameter eqb_iff_eq : forall a b : elt, eqb a b = true <-> a = b.
   Parameter eqb_iff_neq : forall a b : elt, eqb a b = false <-> a <> b.
End BooleanEqualitySet.

Module BooleanEqualitySetFun(BE' : BooleanEquality) : BooleanEqualitySet.
  Module BE := BE'.
  Module BESet := Ops(BE).
  Include BESet.
  Definition eq := BE.eq.
  Definition eq_equiv := BE.eq_equiv.
  Definition eq_dec := BE.eq_dec.
  Definition eqb := BE.eqb.
  Definition eqb_eq := BE.eqb_eq.
  Definition eqb_refl := BE.eqb_refl.
  Definition eqb_sym := BE.eqb_sym.
  Definition eqb_trans := BE.eqb_trans.
  Definition eq_trans := BE.eq_trans.
  Definition eqb_to_eq := BE.eqb_to_eq.
  Definition eqb_to_neq := BE.eqb_to_neq.
  Definition eqb_iff_eq := BE.eqb_iff_eq.
  Definition eqb_iff_neq := BE.eqb_iff_neq.
End BooleanEqualitySetFun.
Print BooleanEqualitySetFun.

Module Type ContextSig.
  Declare Module K : BooleanEqualitySet.
  Declare Module T : BooleanEquality.

  Parameter Context  : Type.
  Parameter empty    : Context.
  Parameter add      : Context -> K.elt -> T.t -> Context.
  Parameter map      : Context -> K.elt -> option T.t.
  Parameter nodup    : Context -> bool.
  Parameter equal    : Context -> Context -> bool.
  Parameter concat   : Context -> Context -> Context.
  Parameter dom      : Context -> K.t.
  Parameter extends  : Context -> Context -> bool.
End ContextSig.

Module ContextFun(K': BooleanEquality) (T' : BooleanEquality) <: ContextSig.
  Module K := BooleanEqualitySetFun(K').
  Module T := T'.

Inductive Context': Type :=
| dot  : Context' 
| ctxt :  K.elt -> T.t -> Context' -> Context' .

Definition Context := Context'.
Definition empty  := dot.

Function add (c : Context') (k: K.elt) (t : T.t)  : Context' :=
  match c with
    | dot => (ctxt k t (dot))
    | (ctxt k' t' c') =>
      match K.eqb k k' with
        | true  => (ctxt k  t  c')
        | false => (ctxt k' t' (add c' k t))
      end
  end.
Hint Unfold add. 

Function map (c : Context') (k : K.elt) : option T.t :=
  match c with
    | dot => None
    | (ctxt k' t' c') =>
      match K.eqb k k' with
        | true  => Some t'
        | false => (map c' k)
      end
  end.
Hint Unfold map.

Function delete (c : Context') (k : K.elt) : Context' :=
  match k, c with
    | k, dot => empty
    | k, (ctxt k' t' c') =>
      match K.eqb k k' with
        | true  => c'
        | false => (ctxt k' t' (delete c' k))
      end
  end.
Hint Unfold delete.

Function nodup (c : (Context')) : bool :=
  match c with
    | dot => true
    | (ctxt k' t' c') =>
      match map c' k' with
        | Some t  => false
        | None  => nodup c'
      end
end.
Hint Unfold nodup.

Function extends (c c' : Context') : bool :=
  match c with 
    | dot => true
    | ctxt k t c'' =>
      match map c' k with
       | Some t' => 
         match (T.eqb t t') with
           | true => extends c'' c' 
           | false => false
         end
       | None => false
      end
  end.
Hint Unfold extends.

Function equal (c c' : Context') : bool :=
  andb (extends c c') (extends c' c).
Hint Unfold equal.

Function concat (c c' : Context') {struct c'} : Context' :=
  match c' with
  | dot => c
  | (ctxt k v d) => (ctxt k v (concat c d))
  end.

Function dom (c : Context') : K.t :=
 match c with 
 | dot => K.empty
 | (ctxt k v c') => K.union (K.singleton k) (dom c')
 end.
End ContextFun.