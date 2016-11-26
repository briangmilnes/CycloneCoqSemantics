(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION".   Daniel Grossman, August 2003 *)
(* This is all of the LN infrastructure packed in a module for types. *)
(* Brian Milnes 2016 *)

Set Implicit Arguments.
Require Export Cyclone_Formal_Syntax.

(* Substituting a type into a type for a type variable. *)


Module T. (* T = Types *)
Fixpoint subst  (tau : Tau) (alpha : var) (t : Tau) {struct t} : Tau := 
  match t with 
    | btvar i      => btvar i
    | ftvar beta   => If (alpha = beta) then tau else (ftvar beta)
    | cint         => cint
    | cross t0 t1  => cross (subst tau alpha t0) (subst tau alpha t1)
    | arrow t0 t1  => arrow (subst tau alpha t0) (subst tau alpha t1)
    | ptype t0     => ptype (subst tau alpha t0)
    | utype k t0   => utype k (subst tau alpha t0)
    | etype p k t0 => etype p k (subst tau alpha t0)
end.

Hint Resolve subst.

Notation "[ t 'T>' alpha ] tm" := (subst t alpha tm) (at level 68) : cyclone_scope.

Fixpoint open_rec  (k : nat) (t : Tau) (tau : Tau)  {struct tau}  : Tau :=
 match tau with 
   | btvar i       => If k = i then t else btvar i
   | ftvar i       => ftvar i
   | cint          => cint
   | cross t0 t1   => cross (open_rec k t t0) (open_rec k t t1)
   | arrow t0 t1   => arrow (open_rec k t t0) (open_rec k t t1)
   | ptype t0      => ptype (open_rec k t t0)
   | utype kp t0   => utype kp (open_rec (S k) t t0)
   | etype p kp t0 => etype p kp (open_rec (S k) t t0)
  end.

Definition open t tau := open_rec 0 t tau.

Notation "{ k T> u } t" := (open_rec k u t)        (at level 67) : cyclone_scope.
Notation "t 'T^^' u"    := (open u t)              (at level 67) : cyclone_scope.
Notation "t 'T^' alpha" := (open (ftvar alpha) t)  (at level 67) : cyclone_scope.

(** Closing a type. *)

Fixpoint close_rec (k : nat) (v : var) (t : Tau) : Tau :=
  match t with 
    | btvar i       => t
    | ftvar x       => If x = v then (btvar k) else t
    | cint          => cint
    | cross t0 t1   => cross (close_rec k v t0) (close_rec k v t1)
    | arrow t0 t1   => arrow (close_rec k v t0) (close_rec k v t1)
    | ptype t0      => ptype (close_rec k v t0)
    | utype k' t0   => utype k' (close_rec (S k) v t0)
    | etype p k' t0 => etype p k' (close_rec (S k) v t0)
end.  

Definition close v t := close_rec 0 v t.

Notation "{ k <T u } t" := (close_rec k u t) (at level 67) : cyclone_scope.

(* Free variables of types. *)

Fixpoint fv (tau : Tau) {struct tau} : vars :=
 match tau with
    | btvar i      => \{}
    | ftvar x      => \{x}
    | cint         => \{}
    | cross t0 t1  => (fv t0) \u (fv t1)
    | arrow t0 t1  => (fv t0) \u (fv t1)
    | ptype t0     => (fv t0)
    | utype k t0   => (fv t0)
    | etype _ _ t0 => (fv t0)
end.

Hint Extern 1 (_ \notin fv _) => simpl; notin_solve.

Definition closed t := fv t = \{}.

Fixpoint size (tau : Tau) {struct tau} : nat :=
  match tau with
    | btvar i      => 1
    | ftvar x      => 1
    | cint         => 1
    | cross t0 t1  => 1 + (size t0) + (size t1)
    | arrow t0 t1  => 1 + (size t0) + (size t1)
    | ptype t0     => 1 + (size t0)
    | utype k t0   => 1 + (size t0)
    | etype p k t0 => 1 + (size t0)
  end.


(* Is a type locally closed? *)

Inductive lc : Tau -> Prop := 
 | lc_ftvar : forall x, lc (ftvar x)
 | lc_cint  : lc cint
 | lc_cross : forall t0 t1, lc t0 -> lc t1 -> lc (cross t0 t1)
 | lc_arrow : forall t0 t1, lc t0 -> lc t1 -> lc (arrow t0 t1)
 | lc_ptype : forall t0, lc t0 -> lc (ptype t0)
 | lc_utype : forall L' t0 k,
                    (forall (alpha : var) , alpha \notin L' ->
                       lc (open_rec 0 (ftvar alpha) t0)) ->
                    lc (utype k t0)
 | lc_etype : forall L' t0 p k,
                  (forall (alpha : var), alpha \notin L' ->
                  lc (open_rec 0 (ftvar alpha) t0)) ->
                  lc (etype p k t0).

Definition body t :=
  exists L, forall alpha, alpha \notin L -> lc (open (ftvar alpha) t).

Hint Constructors lc.


(* Tactics for building L, our finite set for cofinite induction. *)
(* One bad consequence of this is having to triple the gather_vars/pick_fresh
 tacticals. *)

(* TODO this will have to be upgraded with functions. *)

Ltac gather_vars :=
  let A' := gather_vars_with (fun x : vars => x) in
  let B' := gather_vars_with (fun x : var  => \{x}) in
  let C' := gather_vars_with (fun x : Tau => fv x) in
  constr:(A' \u (B' \u C')).

Ltac pick_fresh X :=
  let L := gather_vars in (pick_fresh_gen L X).

Tactic Notation "pick_fresh" ident(x) :=
  let L := gather_vars in pick_fresh_gen (L) x.

Tactic Notation "pick_fresh" ident(x) "from" constr(E) :=
  let L := gather_vars in pick_fresh_gen (L \u E) x.

Tactic Notation "apply_fresh" constr(T) :=
  apply_fresh_base T gather_vars ltac_no_arg.

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; auto_star.

Tactic Notation "apply_fresh" "*" constr(T) :=
  apply_fresh T; auto_star.

Tactic Notation "exists_fresh" :=
  let y := fresh "y" in let Fry := fresh "Fr" y in
  exists_fresh_gen gather_vars y Fry.
End T.