(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  An attempt at a variable module in a context. 

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.
Require Import Coq.Init.Logic.
Require Import Coq.Bool.Bool.
Require Import Coq.Setoids.Setoid.

Require Export BoolEqualitySigDef.
Require Export TVarModuleDef.
Require Export EVarModuleDef.
Require Export KappaModuleDef.
Require Export PhiModuleDef.
Require Export PathModuleDef.
Require Export TauModuleDef.
Require Export CpdtTactics. 
Require Export Case.
Require Export MoreTacticals.

Module TermModule.
  Module EV   := EVarModule.
  Include TauModule.Base.
  Include PathModule.

Module Base.
Inductive I  : Type :=  
 | i_i       : Z -> I.                         (* An integer value in an expression or statement. *)

Inductive St : Type :=                        (* Terms for statements. *)
 | e_s       : E   -> St                      (* An expression in a statement. *)
 | retn      : E   -> St                      (* Returns are required in this syntax. *)
 | seq       : St  -> St -> St                (* Statement sequencing. *)
 | if_s      : E   -> St -> St   -> St        (* if expression in a statement. *)
 | while     : E   -> St -> St                (* A while statement. *)
 | letx      : EV.T -> E -> St   -> St        (* A let expression. *)
 | open      : E -> TV.T -> EV.T -> St -> St  (* open an existential package (elimination) to a value. *)
 | openstar  : E -> TV.T -> EV.T -> St -> St  (* open an existential package (elimination) with a pointer to the value. *)
with E : Type :=                              (* Terms for expressions. *)
 | i_e       : I -> E                         (* An integer value in an expression. *)
 | p_e       : EV.T -> list PE -> E           (* This is a term that derefences a path into the value of the variable. *)
 | f_e       : F -> E                         (* A function identifier in an expression or statement. *)
 | amp       : E -> E                         (* Take the address of an expression. *)
 | star      : E -> E                         (* Derefence an expression of a pointer type. *)
 | cpair     : E -> E -> E                    (* A pair in an expression. *)
 | dot       : E -> IPE -> E                  (* A deference of a pair. *)
 | assign    : E -> E -> E                    (* Assignment. *)
 | appl      : E -> E -> E                    (* Application expression. app is append. *)
 | call      : St -> E                        (* A call expression for the semantics use. *)
 | inst      : E -> Tau -> E                  (* Type instantiation, e[\tau]. *)
 | pack      : Tau -> E -> Tau -> E           (* Existential type introduction. *)
with F : Type :=
 | dfun      : Tau -> EV.T -> Tau -> St -> F  (* Function definition. *)
 | ufun      : TV.T -> Kappa -> F -> F        (* Univerally quantified polymorphic function definition.  *)
.

Scheme St_ind_mutual := Induction for St Sort Prop
with    E_ind_mutual := Induction for E Sort Prop
with    F_ind_mutual := Induction for F Sort Prop.
Combined Scheme Term_ind_mutual from St_ind_mutual, E_ind_mutual, F_ind_mutual.

Function beq_i (i i' : I) : bool :=
  match i, i' with
    | i_i i, i_i i' => Zeq_bool i i'
 end.
Hint Unfold  beq_i.
Hint Resolve beq_i.

Function beq_st (s s' : St) : bool := 
  match s, s' with
    | (e_s e), (e_s e') => beq_e e e'
    | retn e, retn e'   => beq_e e e'
    | seq s1 s2, seq s1' s2' => andb (beq_st s1 s1') (beq_st s2 s2')
    | if_s e s1 s2, if_s e' s1' s2' =>
      andb (andb (beq_e e e') (beq_st s1 s1'))
           (beq_st s2 s2')
    | while e s, while e' s' => andb (beq_e e e') (beq_st s s')
    | letx x e s, letx x' e' s' =>
       andb (andb (EV.beq_t x x') (beq_e e e')) (beq_st s s')
    | open e alpha x s, open e' beta x' s' =>
      andb (andb (beq_e e e')    (TV.beq_t alpha beta))
           (andb (EV.beq_t x x') (beq_st s s'))
    | openstar e alpha x s, openstar e' beta x' s' =>
      andb (andb (beq_e e e')    (TV.beq_t alpha beta))
           (andb (EV.beq_t x x') (beq_st s s'))
    | _, _ => false
  end
with beq_e (e e' : E) : bool := 
 match e, e' with 
 | i_e i, i_e i'                 => beq_i i i'
 | p_e x p, p_e x' p'            => andb (EV.beq_t x x') (beq_path p p')
 | f_e f, f_e f'                 => beq_f f f'
 | amp e, amp e'                 => beq_e e e'
 | star e, star e'               => beq_e e e'
 | cpair e0 e1, cpair e0' e1'    => andb (beq_e e0 e0') (beq_e e1 e1')
 | dot e ipe, dot e' ipe'        => andb (beq_e e e')   (beq_ipe ipe ipe')
 | assign e1 e2, assign e1' e2'  => andb (beq_e e1 e1') (beq_e e2 e2')
 | appl e1 e2, appl e1' e2'      => andb (beq_e e1 e1') (beq_e e2 e2')
 | call s, call s'               => beq_st s s'
 | inst e t, inst e' t'          => andb (beq_e e e') (beq_tau t t')
 | pack t0 e t1, pack t0' e' t1' => andb (andb (beq_tau t0 t0') (beq_e e e'))
                                         (beq_tau t1 t1')
 | _, _ => false
end
with beq_f (f f' : F) : bool :=
 match  f, f' with 
 | dfun t0 x t1 s, dfun t0' x' t1' s' => 
   (andb (andb (beq_tau t0 t0') (EV.beq_t x x'))
         (andb (beq_tau t1 t1') (beq_st s s')))
 | ufun a k f, ufun a' k' f'     => (andb (andb (TV.beq_t a a') (beq_kappa k k'))
                                          (beq_f f f'))
 | _, _ => false
end.

Hint Unfold  beq_st.
Hint Resolve beq_st.
Hint Unfold  beq_e.
Hint Resolve beq_e.
Hint Unfold  beq_f.
Hint Resolve beq_f.

(* Totally not working. 
Functional Scheme beq_st_ind := Induction for beq_st Sort Prop
with    beq_e_ind := Induction for beq_e Sort Prop
with    beq_f_ind := Induction for beq_f Sort Prop.
*)

Hint Resolve beq_i.
Hint Resolve beq_st.
Hint Resolve beq_e.
Hint Resolve beq_f.

Lemma beq_i_refl:
 forall i,
   beq_i i i = true.
Proof.
  intros.
  induction i; crush.
Qed.
Hint Resolve beq_i_refl.

(* not quite sure why I have to change the proof structure here at all. *)
Lemma beq_i_sym : forall i i', beq_i i i' = beq_i i' i.
Proof.
  induction i; induction i'; auto.
  unfold beq_i.
  apply Zeq_bool_sym.
Qed.
Hint Resolve beq_i_sym.

Lemma beq_i_eq:
  forall i i', beq_i i i' = true -> i = i'.
Proof.
  induction i; induction i'.
  unfold beq_i.
  intros.
  apply Zeq_bool_eq in H.
  subst.
  reflexivity.
Qed.
Hint Resolve beq_i_eq.

Lemma beq_i_neq:
  forall i i', beq_i i i' = false -> i <> i'.
Proof.
  induction i; induction i'; crush.
  rewrite Zeq_bool_refl in H.
  inversion H.
Qed.  
Hint Resolve beq_i_neq.

Lemma beq_i_trans: 
  forall i i0 i1,
    beq_i i i0 = true -> 
    beq_i i0 i1 = true -> 
    beq_i i i1 = true.
Proof.
  intros.
  pose proof H as H'.
  pose proof H0 as H0'.
  apply beq_i_eq in H.
  apply beq_i_eq in H0.
  subst.
  assumption.
Qed.
Hint Resolve beq_i_trans.

Lemma beq_st_refl:
  forall s, beq_st s s = true.
Proof.
  intros s.
  apply (St_ind_mutual 
           (fun s : St => beq_st s s = true)
           (fun e : E  => beq_e e e = true)
           (fun f : F  => beq_f f f = true));
    try solve[crush].
Qed.
Hint Resolve beq_st_refl.

Lemma beq_e_refl:
  forall e, beq_e e e = true.
Proof.
  intros s.
  apply (E_ind_mutual 
           (fun s : St => beq_st s s = true)
           (fun e : E  => beq_e e e = true)
           (fun f : F  => beq_f f f = true));
    try solve[crush].
Qed.
Hint Resolve beq_e_refl.

Lemma beq_f_refl:
  forall f, beq_f f f = true.
Proof.
  intros s.
  apply (F_ind_mutual 
           (fun s : St => beq_st s s = true)
           (fun e : E  => beq_e e e = true)
           (fun f : F  => beq_f f f = true));
    try solve[crush].
Qed.
Hint Resolve beq_f_refl.

(* The modules are causing name identity issues on fold/unfold. *)
Ltac refold_term := unfold beq_st; unfold beq_e; unfold beq_f; fold beq_st; fold beq_e; fold beq_f.
Ltac refold_term_in H := unfold beq_st in H; unfold beq_e in H; unfold beq_f in H; fold beq_st in H; fold beq_e in H; fold beq_f in H.

Lemma beq_st_sym:
  forall s s', beq_st s s' = beq_st s' s.
Proof.
  apply (St_ind_mutual 
           (fun s : St => forall s', beq_st s s' = beq_st s' s)
           (fun e : E  => forall e', beq_e e e' = beq_e e' e)
           (fun f : F  => forall f', beq_f f f' = beq_f f' f));
    try solve[intros; destruct s'; try solve[crush]];
    try solve[intros; destruct e'; try solve[crush]];
    try solve[intros; destruct f'; try solve[crush]];
    try solve [intros;
              try destruct s';
              try destruct e';
              try destruct f';
              try solve[crush];
              refold_term;
              try rewrite H;
              try rewrite H0;
              try rewrite EV.beq_t_sym;
              try rewrite TV.beq_t_sym;
              try rewrite beq_path_sym;
              try rewrite TV.beq_t_sym;
              try rewrite beq_kappa_sym;
              try rewrite beq_ipe_sym;
              try rewrite beq_tau_sym;
              try reflexivity;
              try setoid_rewrite beq_tau_sym at 2;
              try reflexivity].
Qed.
Hint Resolve beq_st_refl.

Lemma beq_e_sym:
  forall e e', beq_e e e' = beq_e e' e.
Proof.
  apply (E_ind_mutual 
           (fun s : St => forall s', beq_st s s' = beq_st s' s)
           (fun e : E  => forall e', beq_e e e' = beq_e e' e)
           (fun f : F  => forall f', beq_f f f' = beq_f f' f));
    try solve[intros; destruct s'; try solve[simpl]];
    try solve[intros; destruct e'; try solve[simpl]];
    try solve[intros; destruct f'; try solve[simpl]];
    try solve [intros;
              try destruct s';
              try destruct e';
              try destruct f';
              try solve[crush];
              refold_term;
              try rewrite H;
              try rewrite H0;
              try rewrite EV.beq_t_sym;
              try rewrite beq_tau_sym;
              try rewrite beq_path_sym;
              try rewrite TV.beq_t_sym;
              try rewrite beq_kappa_sym;
              try rewrite beq_ipe_sym;
              try rewrite beq_tau_sym;
              try reflexivity;
              try setoid_rewrite beq_tau_sym at 2;
              try reflexivity].
Qed.
Hint Resolve beq_e_refl.

Lemma beq_f_sym:
  forall f f', beq_f f f' = beq_f f' f.
Proof.
  intros s.
  apply (F_ind_mutual 
           (fun s : St => forall s', beq_st s s' = beq_st s' s)
           (fun e : E  => forall e', beq_e e e' = beq_e e' e)
           (fun f : F  => forall f', beq_f f f' = beq_f f' f));
    try solve[intros; destruct s'; try solve[simpl]];
    try solve[intros; destruct e'; try solve[simpl]];
    try solve[intros; destruct f'; try solve[simpl]];
    try solve [intros;
              try destruct s';
              try destruct e';
              try destruct f';
              try solve[crush];
              refold_term;
              try rewrite H;
              try rewrite H0;
              try rewrite EV.beq_t_sym;
              try rewrite beq_tau_sym;
              try rewrite beq_path_sym;
              try rewrite TV.beq_t_sym;
              try rewrite beq_kappa_sym;
              try rewrite beq_ipe_sym;
              try rewrite beq_tau_sym;
              try reflexivity;
              try setoid_rewrite beq_tau_sym at 2;
              try reflexivity].
Qed.
Hint Resolve beq_f_refl.

Ltac apply_beq_eqs_terms := 
  repeat match goal with
    | [ H : forall _ , beq_e _ _ = true -> _ = _ ,
        I : beq_e _ _ = true 
        |- _ ] => apply H in I; subst
    | [ H : forall _ , beq_st _ _ = true -> _ = _ ,
        I : beq_st _ _ = true 
        |- _ ] => apply H in I; subst
    | [ H : forall _ , beq_f _ _ = true -> _ = _ ,
        I : beq_f _ _ = true 
        |- _ ] => apply H in I; subst
    | [ I : EV.beq_t _ _ = true 
        |- _ ] => apply EV.beq_t_eq in I; subst
    | [ I : TV.beq_t _ _ = true 
        |- _ ] => apply TV.beq_t_eq in I; subst
    | [ I : beq_i _ _ = true 
        |- _ ] => apply beq_i_eq in I; subst
    | [ I : beq_ipe _ _ = true 
        |- _ ] => apply beq_ipe_eq in I; subst
    | [ I : beq_path _ _ = true 
        |- _ ] => apply beq_path_eq in I; subst
    | [ I : beq_tau _ _ = true 
        |- _ ] => apply beq_tau_eq in I; subst
    | [ I : beq_kappa _ _ = true 
        |- _ ] => apply beq_kappa_eq in I; subst
end.

Lemma beq_st_eq:
  forall s s', beq_st s s' = true -> s = s'.
Proof.
  intros s.
  apply (St_ind_mutual 
           (fun s : St => forall s', beq_st s s' = true -> s = s')
           (fun e : E  => forall e', beq_e e e'  = true -> e = e')
           (fun f : F  => forall f', beq_f f f'  = true -> f = f'));
    intros;
    try destruct s';
    try destruct e';
    try destruct f'; 
    try solve[inversion H0];
    try solve[inversion H1];
    try solve[simpl in H2; inversion H2];
    try solve[crush];
    try solve[
          try refold_term_in H;
          try refold_term_in H0;
          try refold_term_in H1;
          try refold_term_in H2;
          simplify_boolean_and_true;
          apply_beq_eqs_terms;
          reflexivity].
Qed.
Hint Resolve beq_st_eq.

Lemma beq_e_eq:
  forall e e', beq_e e e' = true -> e = e'.
Proof.
  intros s.
  apply (E_ind_mutual 
           (fun s : St => forall s', beq_st s s' = true -> s = s')
           (fun e : E  => forall e', beq_e e e'  = true -> e = e')
           (fun f : F  => forall f', beq_f f f'  = true -> f = f'));
    intros;
    try destruct s';
    try destruct e';
    try destruct f'; 
    try solve[inversion H0];
    try solve[inversion H1];
    try solve[crush];
    try solve[
          try refold_term_in H;
          try refold_term_in H0;
          try refold_term_in H1;
          try refold_term_in H2;
          simplify_boolean_and_true;
          apply_beq_eqs_terms;
          reflexivity].
Qed.
Hint Resolve beq_e_eq.

Lemma beq_f_eq:
  forall f f', beq_f f f' = true -> f = f'.
Proof.
  intros s.
  apply (F_ind_mutual 
           (fun s : St => forall s', beq_st s s' = true -> s = s')
           (fun e : E  => forall e', beq_e e e'  = true -> e = e')
           (fun f : F  => forall f', beq_f f f'  = true -> f = f'));
    intros;
    try destruct s';
    try destruct e';
    try destruct f'; 
    try solve[inversion H0];
    try solve[inversion H1];
    try solve[crush];
    try solve[
          try refold_term_in H;
          try refold_term_in H0;
          try refold_term_in H1;
          try refold_term_in H2;
          simplify_boolean_and_true;
          apply_beq_eqs_terms;
          reflexivity].
Qed.
Hint Resolve beq_f_eq.

Ltac apply_beq_neqs := 
  repeat match goal with
    | [ H : forall _ , beq_e _ _ = false -> _ <> _ ,
        I : beq_e _ _ = false 
        |- _ ] => apply H in I; subst
    | [ H : forall _ , beq_st _ _ = false -> _ <> _ ,
        I : beq_st _ _ = false 
        |- _ ] => apply H in I; subst
    | [ H : forall _ , beq_f _ _ = false -> _ <> _ ,
        I : beq_f _ _ = false 
        |- _ ] => apply H in I; subst
    | [ I : EV.beq_t _ _ = false 
        |- _ ] => apply EV.beq_t_neq in I; subst
    | [ I : beq_tau _ _ = false 
        |- _ ] => apply beq_tau_neq in I; subst
    | [ I : beq_i _ _ = false 
        |- _ ] => apply beq_i_neq in I; subst
    | [ I : beq_ipe _ _ = false 
        |- _ ] => apply beq_ipe_neq in I; subst
    | [ I : beq_path _ _ = false 
        |- _ ] => apply beq_path_neq in I; subst
    | [ I : TV.beq_t _ _ = false 
        |- _ ] => apply TV.beq_t_neq in I; subst
    | [ I : beq_kappa _ _ = false 
        |- _ ] => apply beq_kappa_neq in I; subst
end.

Lemma beq_st_neq:
  forall s s', beq_st s s' = false -> s <> s'.
Proof.
  intros s.
  apply (St_ind_mutual 
           (fun s : St => forall s', beq_st s s' = false -> s <> s')
           (fun e : E  => forall e', beq_e e e'  = false -> e <> e')
           (fun f : F  => forall f', beq_f f f'  = false -> f <> f'));
    intros;
    try destruct s';
    try destruct e';
    try destruct f'; 
    try solve[inversion H0];
    try solve[inversion H1];
    try solve[discriminate];
    try solve [
          try refold_term_in H;
          try refold_term_in H0;
          try refold_term_in H1;
          try refold_term_in H2;
          simplify_boolean_and_false;
          apply_beq_neqs;
          congruence].
Qed.
Hint Resolve beq_st_neq.

Lemma beq_e_neq:
  forall e e', beq_e e e' = false -> e <> e'.
Proof.
  intros s.
  apply (E_ind_mutual 
           (fun s : St => forall s', beq_st s s' = false -> s <> s')
           (fun e : E  => forall e', beq_e e e'  = false -> e <> e')
           (fun f : F  => forall f', beq_f f f'  = false -> f <> f'));
    intros;
    try destruct s';
    try destruct e';
    try destruct f'; 
    try solve[inversion H0];
    try solve[inversion H1];
    try solve[discriminate];
    try solve [
          try refold_term_in H;
          try refold_term_in H0;
          try refold_term_in H1;
          try refold_term_in H2;
          simplify_boolean_and_false;
          apply_beq_neqs;
          congruence].
Qed.
Hint Resolve beq_e_neq.

Lemma beq_f_neq:
  forall f f', beq_f f f' = false -> f <> f'.
Proof.
  intros s.
  apply (F_ind_mutual 
           (fun s : St => forall s', beq_st s s' = false -> s <> s')
           (fun e : E  => forall e', beq_e e e'  = false -> e <> e')
           (fun f : F  => forall f', beq_f f f'  = false -> f <> f'));
    intros;
    try destruct s';
    try destruct e';
    try destruct f'; 
    try solve[inversion H0];
    try solve[inversion H1];
    try solve[discriminate];
    try solve [
          try refold_term_in H;
          try refold_term_in H0;
          try refold_term_in H1;
          try refold_term_in H2;
          simplify_boolean_and_false;
          apply_beq_neqs;
          congruence].
Qed.
Hint Resolve beq_st_neq.

Lemma beq_st_trans:
  forall s s0 s1, 
    beq_st s s0 = true ->
    beq_st s0 s1 = true ->
    beq_st s s1 = true.
Proof.
  intros.
  pose proof H as H'.
  pose proof H0 as H0'.
  apply beq_st_eq in H.
  apply beq_st_eq in H0.
  subst.
  assumption.
Qed.
Hint Resolve beq_st_trans.

Lemma beq_e_trans:
  forall e e0 e1, 
    beq_e e e0 = true ->
    beq_e e0 e1 = true ->
    beq_e e e1 = true.
Proof.
  intros.
  pose proof H as H'.
  pose proof H0 as H0'.
  apply beq_e_eq in H.
  apply beq_e_eq in H0.
  subst.
  assumption.
Qed.
Hint Resolve beq_e_trans.

Lemma beq_f_trans:
  forall f f0 f1,
    beq_f f f0 = true ->
    beq_f f0 f1 = true ->
    beq_f f f1 = true.
Proof.
  intros.
  pose proof H as H'.
  pose proof H0 as H0'.
  apply beq_f_eq in H.
  apply beq_f_eq in H0.
  subst.
  assumption.
Qed.
Hint Resolve beq_f_trans.

Lemma beq_e_iff_eq:    forall a b, beq_e a b = true <-> a = b.
Proof.
  intros.
  split.
  apply beq_e_eq.
  intros.
  rewrite H.
  apply beq_e_refl.
Qed.
Hint Resolve beq_e_iff_eq.

Lemma beq_e_iff_neq:   forall a b, beq_e a b = false <-> a <> b.
Proof.
  intros.
  split.
  apply beq_e_neq.
Admitted.
Hint Resolve beq_e_iff_neq.

Inductive Value : E -> Prop :=
 | IIsAValue    : forall (i : I),              Value (i_e i)
                                                     
 | AmpIsAValue  : forall (x : EV.T) (p : Path),   Value (amp (p_e x p)) 

 | DfunIsAValue : forall (t1 t2 : Tau) (x : EV.T) (s : St), 
                        Value (f_e (dfun t1 x t2 s))
 | UfunIsAValue : 
     forall (t : TV.T) (k : Kappa) (f : F),
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
End Base.
Include Base.

Definition T := E.
Definition beq_t := beq_e.
Definition beq_t_refl := beq_e_refl.
Definition beq_t_sym := beq_e_sym.
Definition beq_t_trans := beq_e_trans.
Definition beq_t_eq := beq_e_eq.
Definition beq_t_neq := beq_e_neq.
Definition beq_t_iff_eq := beq_e_iff_eq.
Definition beq_t_iff_neq := beq_e_iff_neq.

End TermModule.
