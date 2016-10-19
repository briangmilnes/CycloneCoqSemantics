(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  A mutally recursive term and typing test example.

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.
Require Import Coq.Init.Logic.

(* TODO make use of the induction hypotheses to see that these are correct. *)
(* A very simple mutually recursive subset of our language. *)

Inductive Kappa : Type :=
 | B                                                               (* 'boxed' kind. *)
 | A.                                                              (* 'any'   kind. *)

Inductive I  : Type :=  
 | i_i       : Z -> I.

Inductive Tau : Type :=
 | cint   : Tau
 | ptype  : Tau -> Tau
 | arrow  : Tau -> Tau -> Tau
 | utype  : Tau -> Tau -> Tau.

(* Every inductive definition recurses and ST builds from E, E from F. *) 
Inductive St : Type :=
 | e_s       : E   -> St
 | retn      : E   -> St 
 | seq       : St  -> St -> St
 with E : Type :=
 | i_e       : I -> E
 | amp       : E -> E 
 | f_e       : F -> E
with F : Type :=
 | dfun      : Tau -> Tau -> St -> F
 | ufun      : Kappa -> F -> F.

Scheme St_ind_mutual := Induction for St Sort Prop
with    E_ind_mutual := Induction for E Sort Prop
with    F_ind_mutual := Induction for F Sort Prop.
Combined Scheme term_ind_mutual from St_ind_mutual, E_ind_mutual, F_ind_mutual.

(*
Check St_ind_mutual.
Check E_ind_mutual.
Check F_ind_mutual.
Check term_ind_mutual.
*)

Inductive fooS : St -> Prop :=
  | barS : forall (s : St), fooS s.
Inductive fooE : E -> Prop :=
  | barE : forall (e : E), fooE e.
Inductive fooF : F -> Prop :=
  | barF : forall (f : F), fooF f.

Hint Constructors fooS.
Hint Constructors fooE.
Hint Constructors fooF.

Theorem Test_Induction :
  forall (s : St), fooS s.
Proof.
  induction s.
  (* Too few goals, 3 of eight. I can only use this if I don't require
   testing e's and f's. *)
  eauto.
  eauto.
  eauto.
Qed.
Theorem Test_Mutual_Induction_Only_S: 
  forall (s : St), fooS s.
Proof.
   apply (St_ind_mutual 
           (fun s : St => fooS s)
           (fun e : E  => fooE e)
           (fun f : F  => fooF f));
  eauto.
Qed.

Inductive typeSt : St -> Tau -> Prop := 
 | typeSt_e_s      : forall (e : E) (tau : Tau), typeE e tau -> typeSt (e_s e) tau
 | typeSt_retn     : forall (e : E) (tau : Tau), typeE e tau -> typeSt (retn e) tau
 | typeSt_seq      : forall (s1 s2 : St) (t1 t2 : Tau), typeSt s1 t1 -> typeSt s2 t2 -> typeSt (seq s1 s2) t2
with typeE : E -> Tau -> Prop := 
 | typeE_i_e       : forall (i : I), typeE (i_e i) cint
 | typeE_amp       : forall (e : E) (tau : Tau), typeE e tau -> typeE (amp e) (ptype tau)
 | typeE_f_e       : forall (f : F) (t1 t2 : Tau), typeF f (arrow t1 t2) -> typeE (f_e f) (arrow t1 t2)
with typeF : F -> Tau -> Prop := 
 | typeF_dfun      : forall (t1 t2 : Tau) (s : St), typeSt s t2 -> typeF (dfun t1 t2 s) t2
 | typeF_ufun      : forall (f : F) (t1 t2 : Tau) (k : Kappa), 
                       typeF f (arrow t1 t2) -> typeF (ufun k f) (arrow t1 t2).

Scheme typeSt_ind_mutual := Induction for typeSt Sort Prop
with   typeE_ind_mutual  := Induction for typeE Sort Prop
with   typeF_ind_mutual  := Induction for typeF Sort Prop.
Combined Scheme type_ind_mutual from 
         typeSt_ind_mutual, typeE_ind_mutual, typeF_ind_mutual.

Theorem Well_Typed_Statements_Are_Foo:
  forall (s : St) (tau : Tau),
    typeSt s tau -> fooS s.
Proof.
  intros s tau typeS.
  induction typeS; eauto.
Qed.

Theorem Well_Typed_Terms_Are_Foo:
  forall (s : St) (tau : Tau),
    typeSt s tau -> fooS s.
Proof.
  intros s tau.
  apply (type_ind_mutual 
           (fun (s : St) (tau : Tau) (tSt : typeSt s tau) => fooS s)
           (fun (e : E ) (tau : Tau) (tE  : typeE e tau ) => fooE e)
           (fun (f : F ) (tau : Tau) (tF  : typeF f tau ) => fooF f));
  eauto.
Qed.
