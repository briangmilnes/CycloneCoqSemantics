(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  I'll need to build partial functions from list sets, I would say.

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.
Require Import Coq.Init.Logic.

Set Implicit Arguments.

(* Local Open Scope pfun_scope. jrw ? *)

Section PFun.

Variable D : Type.
Variable C : Type.

Hypothesis D_eq_dec : forall x y: D, {x = y} + {x <> y}.
Hypothesis C_eq_dec : forall x y: C, {x = y} + {x <> y}.

Definition pfun := list (D * C).

Definition empty_pfun : pfun := nil.

Fixpoint pfun_add (f:pfun) (dc: D * C) : pfun :=
match dc with 
 | (d,c) => 
    match f with
      | nil => dc :: nil
      | (d',c') :: f' =>
        match D_eq_dec d d' with
          | left _ => dc :: f'
          | right _ => (d',c') :: pfun_add f' dc
        end
    end
end.

Arguments pfun_add _ [dc].

(* Not sure what to do with pairing, I think leave it () 
 Notation " x |-> f "  := (pfun_add f) (at level 70, y at next level).
*)

Infix "+>" := pfun_add (at level 61, right associativity).

Fixpoint pfun_in_dom (d:D) (f:pfun) : bool :=
    match f with
    | nil => false
    | (d',c) :: f' =>
        match D_eq_dec d d' with
        | left _ => true
        | right _ => pfun_in_dom d f'
        end
    end.

Arguments pfun_in_dom [d] _.

Fixpoint pfun_remove (f:pfun) (d:D) : pfun :=
    match f with
    | nil => empty_pfun
    | (d',c) :: f' =>
        match D_eq_dec d d' with
        | left _ => f'
        | right _ => (d',c) :: pfun_remove f' d
        end
    end.

Arguments pfun_remove _ [d] .

Fixpoint pfun_get (f:pfun) (d:D) : option C :=
    match f with
    | nil => None
    | (d',c) :: f' =>
        match D_eq_dec d d' with
        | left _ => Some c
        | right _ => pfun_get f' d
        end
    end. 

(*

Theorem nil_cons : forall (x: D * C) (l:pfun), [] <> (x +> l).

Lemma pfun_extensionality :
  forall (D C : Type) (f g : pfun) ,
    (forall d : D, (pfun_get f d) = pfun_get g d) -> 
    f = g.
*)

Lemma pfun_eq_dec : 
  (forall (d d': D), {d = d'} + {d <> d'}) ->
  (forall (c c': C), {c = c'} + {c <> c'}) ->
  forall x y: pfun, {x = y} + {x <> y}.
Admitted.
  
Check pfun_eq_dec.

End PFun.



Unset Implicit Arguments.


