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

Require Export BooleanEqualityDef.
Require Export TVarModuleDef.
Require Export EVarModuleDef.
Require Export KappaModuleDef.
Require Export PhiModuleDef.
Require Export PathModuleDef.
Require Export TauModuleDef.
Require Export CpdtTactics. 
Require Export Case.
Require Export MoreTacticals.

Module TermModule <: BooleanEquality.

Module Types.
  Module Path := PathModule.
  Include Path.Types.
  Module T := TauModule.
  Include TauModule.Types.
  Module EVS  := EVarModuleSet.
  Module EV   := EVarModuleSet.BE.
  Definition EVar := EVS.elt.
  Definition EVars := EVS.t.

Inductive I  : Type :=  
 | i_i       : nat -> I.                      (* An integer value in an expression or statement. *)

Inductive St : Type :=                        (* Terms for statements. *)
 | e_s       : E   -> St                      (* An expression in a statement. *)
 | retn      : E   -> St                      (* Returns are required in this syntax. *)
 | seq       : St  -> St -> St                (* Statement sequencing. *)
 | if_s      : E   -> St -> St   -> St        (* if expression in a statement. *)
 | while     : E   -> St -> St                (* A while statement. *)
 | letx      : E -> St   -> St        (* A let expression. *)
 | open      : E -> St -> St  (* open an existential package (elimination) to a value. *)
 | openstar  : E -> St -> St  (* open an existential package (elimination) with a pointer to the value. *)
with E : Type :=                              (* Terms for expressions. *)
 | bevar      : nat -> E                      (* A bound expression variable, a de Bruijn index. *)
 | fevar      : EVar -> E                     (* A free expression variable. *)
 | i_e        : I -> E                        (* An integer value in an expression. *)
 (*  TODO how do I handle this path? It should be only a fevar? *)
 | p_e       : EVar -> list PE -> E           (* This is a term that derefences a path into the value of the variable. *)
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
 | dfun      : Tau -> Tau -> St -> F          (* Function definition. *)
 | ufun      : Kappa -> F -> F.               (* Univerally quantified polymorphic function definition.  *)

Inductive  term : Type := 
  | term_st : St -> term 
  | term_e :  E -> term 
  | term_f :  F -> term.

End Types.
Include Types.

Scheme St_ind_mutual := Induction for St Sort Prop
with    E_ind_mutual := Induction for E Sort Prop
with    F_ind_mutual := Induction for F Sort Prop.
Combined Scheme Term_ind_mutual from St_ind_mutual, E_ind_mutual, F_ind_mutual.

Fixpoint open_rec_st  (k : nat) (u : E) (s : St)  {struct s}  : St :=
 match s with 
    | e_s  e        => e_s  (open_rec_e  k u e)
    | retn e        => retn (open_rec_e k u e)
    | seq s0 s1     => seq (open_rec_st k u s0) (open_rec_st k u s1)
    | if_s e s1 s2  => if_s (open_rec_e k u e) 
                           (open_rec_st k u s1) (open_rec_st k u s2)
    | while e s     => while (open_rec_e k u e) (open_rec_st k u s)
                            (* I don't increment down e. *)
    | letx e s      => letx (open_rec_e k u e) (open_rec_st (S k) u s)
    | open e s      => open (open_rec_e k u e) (open_rec_st (S k) u s)
    | openstar e s  => openstar (open_rec_e k u e) (open_rec_st (S k) u s)
  end 
with open_rec_e   (k : nat) (u : E) (e : E) {struct e}  : E :=
  match e with 
    | bevar i      => if (beq_nat k i) then u else (bevar i)
    | fevar i      => fevar i
    | i_e i        => i_e i
    | p_e x p      => p_e x p (* TODO *)
    | f_e f        => f_e  (open_rec_f (S k) u f)
    | amp e        => amp  (open_rec_e k u e)
    | star e       => star (open_rec_e k u e)
    | cpair e1 e2  => cpair (open_rec_e k u e1) (open_rec_e k u e2)
    | dot  e ipe   => dot  (open_rec_e k u e) ipe
    | assign e1 e2 => assign (open_rec_e k u e1) (open_rec_e k u e2)
    | appl e1 e2   => appl   (open_rec_e k u e1) (open_rec_e k u e2)
    | call s       => call (open_rec_st k u s)
    | inst e t     => inst (open_rec_e k u e) t (* TODO *)
    | pack t0 e t1 => pack t0 (open_rec_e k u e) t1  (* TODO *)
  end 
with open_rec_f   (k : nat) (u : E) (f : F) {struct f} : F :=
  match f with 
    | dfun tau1 tau2 s => dfun tau1 tau2 (open_rec_st (S k) u s)
    | ufun k' f         => ufun k' (open_rec_f k u f) (* TODO *)
  end.

Fixpoint open_rec_term (k : nat) (u : E) (t : term) {struct t} : term :=
  match t with 
    | term_st s    => term_st (open_rec_st k u s)
    | term_e  e    => term_e  (open_rec_e  k u e)
    | term_f  f    => term_f  (open_rec_f  k u f)
  end.

(* TODO is this complete? *)
Inductive lc_st : St -> Prop := 
 | lc_st_e_s  : forall e, lc_e e -> lc_st (e_s e)
 | lc_st_letx : forall e (s1 : St),
                  lc_e e ->
                  forall L' s1,
                  (forall x, EVS.mem x L' = false -> lc_st (open_rec_st 0 (fevar x) s1 )) ->
                  lc_st (letx e s1)
with      lc_e : E -> Prop :=
 | lc_e_fevar : forall x, lc_e (fevar x)
 | lc_f_e     : forall f, lc_f f -> lc_e (f_e f)
 | lc_assign  : forall e1 e2, lc_e e1 -> lc_e e2 -> lc_e (appl e1 e2) 
 | lc_appl    : forall e1 e2, lc_e e1 -> lc_e e2 -> lc_e (appl e1 e2)
with      lc_f : F -> Prop :=
 | lc_dfun : forall t1 t2 s L',
               (forall x, EVS.mem x L' = false -> lc_st (open_rec_st 0 (fevar x) s)) ->
               lc_f (dfun t1 t2 s).

Inductive lc_term : term -> Prop := 
  | lc_term_st : forall s, lc_st s -> lc_term (term_st s)
  | lc_term_e  : forall e, lc_e  e -> lc_term (term_e  e)
  | lc_term_f  : forall f, lc_f  f -> lc_term (term_f  f).

(* Restrict value. *)

Fixpoint fv_st (t : St) {struct t} : EVars :=
  match t with
    | e_s  e       => fv_e e
    | retn e       => fv_e e
    | seq s0 s1    => EVS.union (fv_st s0) (fv_st s1)
    | if_s e s0 s1 => EVS.union (fv_e e) (EVS.union (fv_st s0) (fv_st s1))
    | while e s0   => EVS.union (fv_e e) (fv_st s0)
    | letx e s     => EVS.union (fv_e e) (fv_st s)
    | open e s     => EVS.union (fv_e e) (fv_st s)
    | openstar e s => EVS.union (fv_e e) (fv_st s)
  end
with  fv_e (e : E) {struct e} : EVars := 
  match e with 
    | bevar i      => EVS.empty 
    | fevar x      => EVS.singleton x
    | i_e  i       => EVS.empty
    | p_e x p      => EVS.singleton x
    | f_e f        => fv_f f
    | amp e        => fv_e e
    | star e       => fv_e e
    | cpair e0 e1  => EVS.union (fv_e e0) (fv_e e1)
    | dot e ipe    => fv_e e
    | assign e1 e2 => EVS.union (fv_e e1) (fv_e e2)
    | appl e1 e2   => EVS.union (fv_e e1) (fv_e e2)
    | call s       => fv_st s 
    | inst e t     => fv_e e
    | pack t0 e t1 => fv_e e
  end
with  fv_f (f : F) {struct f} : EVars := 
  match f with
  | dfun t1 t2 s => (fv_st s)
  | ufun k f       => fv_f f
end.

Fixpoint fv_term (t : term) {struct t} : EVars :=
  match t with 
    | term_st s    => fv_st s
    | term_e  e    => fv_e e
    | term_f  f    => fv_f f 
 end.

Fixpoint subst_E (e : E) (tau : Tau) (alpha : TVar) {struct e} : E :=
 match e with 
   | bevar i      => e
   | fevar y      => e
   | i_e i        => i_e i    
   | p_e x p      => p_e x p  
   | f_e f        =>        (f_e (subst_F   f  tau alpha))
   | amp e'       => amp    (subst_E   e'     tau alpha)
   | star e'      => star   (subst_E   e'     tau alpha)
   | cpair e1 e2  => cpair  (subst_E   e1     tau alpha) (subst_E e2 tau alpha)
   | dot e' i     => dot    (subst_E   e'     tau alpha) i
   | assign e1 e2 => assign (subst_E   e1     tau alpha) (subst_E e2 tau alpha)
   | appl  e1 e2  => appl   (subst_E   e1     tau alpha) (subst_E e2 tau alpha)
   | call s       => call   (subst_St  s      tau alpha)
   | inst e' t    => inst   (subst_E   e'     tau alpha) (T.subst_Tau t tau alpha)
   | pack t e' t' => pack   (T.subst_Tau t tau alpha) (subst_E e' tau alpha) (T.subst_Tau t' tau alpha)
 end 
with subst_St (s: St) (tau : Tau) (alpha : TVar) {struct s} : St :=
  match s with
    | e_s e         => e_s      (subst_E e tau alpha)
    | retn e        => retn     (subst_E e tau alpha)
    | seq s1 s2     => seq      (subst_St s1 tau alpha) (subst_St s2 tau alpha)
    | if_s e s1 s2  => if_s     (subst_E e tau alpha)   (subst_St s1 tau alpha) (subst_St s2 tau alpha)
    | while e s     => while    (subst_E e tau alpha)   (subst_St s tau alpha)
    | letx e s      => letx     (subst_E e tau alpha)   (subst_St s tau alpha)
    | open     e s  => open     (subst_E e tau alpha)   (subst_St s tau alpha)
    | openstar e s  => openstar (subst_E e tau alpha)   (subst_St s tau alpha)
end
with subst_F (f : F) (tau : Tau) (alpha : TVar) {struct f} : F  := 
 match f with 
   | (dfun tau1 tau2 s) => 
     (dfun (T.subst_Tau tau1 tau alpha) (T.subst_Tau tau2 tau alpha) (subst_St s tau alpha))
   (* Bug 7 from test. *)
   | ufun k f => (ufun k (subst_F f tau alpha))
end.

Function beq_i (i i' : I) : bool :=
  match i, i' with
    | i_i i, i_i i' => beq_nat i i'
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
    | letx e s, letx e' s' =>
       andb  (beq_e e e') (beq_st s s')
    | open e s, open e' s' =>
      andb (beq_e e e')  (beq_st s s')
    | openstar e s, openstar e' s' =>
      andb (beq_e e e') (beq_st s s')
    | _, _ => false
  end
with beq_e (e e' : E) : bool := 
 match e, e' with 
 | fevar i, fevar j              => (EVS.BE.eqb i j)
 | bevar i, bevar j              => beq_nat i j
 | i_e i, i_e i'                 => beq_i i i'
 | p_e x p, p_e x' p'            => andb (EVS.BE.eqb x x') (Path.beq_path p p')
 | f_e f, f_e f'                 => beq_f f f'
 | amp e, amp e'                 => beq_e e e'
 | star e, star e'               => beq_e e e'
 | cpair e0 e1, cpair e0' e1'    => andb (beq_e e0 e0') (beq_e e1 e1')
 | dot e ipe, dot e' ipe'        => andb (beq_e e e')   (Path.beq_ipe ipe ipe')
 | assign e1 e2, assign e1' e2'  => andb (beq_e e1 e1') (beq_e e2 e2')
 | appl e1 e2, appl e1' e2'      => andb (beq_e e1 e1') (beq_e e2 e2')
 | call s, call s'               => beq_st s s'
 | inst e t, inst e' t'          => andb (beq_e e e') (T.eqb t t')
 | pack t0 e t1, pack t0' e' t1' => andb (andb (T.eqb t0 t0') (beq_e e e'))
                                         (T.eqb t1 t1')
 | _, _ => false
end
with beq_f (f f' : F) : bool :=
 match  f, f' with 
 | dfun t0 t1 s, dfun t0' t1' s' => 
   (andb (T.eqb t0 t0') (andb (T.eqb t1 t1') (beq_st s s')))
 | ufun k f, ufun k' f'     => 
   (andb (K.eqb k k') (beq_f f f'))
 | _, _ => false
end.

Hint Unfold  beq_st.
Hint Resolve beq_st.
Hint Unfold  beq_e.
Hint Resolve beq_e.
Hint Unfold  beq_f.
Hint Resolve beq_f.

Hint Resolve beq_i.
Hint Resolve beq_st.
Hint Resolve beq_e.
Hint Resolve beq_f.

Fixpoint eq (a b : E) : Prop :=
    match beq_e a b with
     | false => False
     | true => True
    end.

Hint Resolve beq_nat_refl.
Lemma beq_i_refl:
 forall i,
   beq_i i i = true.
Proof.
  intros.
  induction i; crush. 
Qed.
Hint Resolve beq_i_refl.

Lemma beq_i_sym : forall i i', beq_i i i' = beq_i i' i.
Proof.
  induction i; induction i'; auto.
  unfold beq_i.
  apply beq_nat_sym.
Qed.
Hint Resolve beq_i_sym.

Lemma beq_i_to_eq:
  forall i i', beq_i i i' = true -> i = i'.
Proof.
  induction i; induction i'.
  unfold beq_i.
  intros.
  symmetry in H.
  apply beq_nat_eq in H.
  subst.
  reflexivity.
Qed.
Hint Resolve beq_i_to_eq.

Lemma beq_i_to_neq:
  forall i i', beq_i i i' = false -> i <> i'.
Proof.
  induction i; induction i'; crush.
  rewrite <- beq_nat_refl in H.
  inversion H.
Qed.  
Hint Resolve beq_i_to_neq.

Lemma beq_i_trans: 
  forall i i0 i1,
    beq_i i i0 = true -> 
    beq_i i0 i1 = true -> 
    beq_i i i1 = true.
Proof.
  intros.
  pose proof H as H'.
  pose proof H0 as H0'.
  apply beq_i_to_eq in H.
  apply beq_i_to_eq in H0.
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
    try solve [intros;
               try destruct s';
               try destruct e';
               try destruct f';
              refold_term;
              try rewrite H;
              try rewrite H0;
              try rewrite beq_nat_sym;
              try rewrite EVS.BE.eqb_sym;
              try rewrite TVS.BE.eqb_sym;
              try rewrite Path.eqb_sym;
              try rewrite TVS.BE.eqb_sym;
              try rewrite K.eqb_sym;
              try rewrite Path.beq_ipe_sym;
              try rewrite T.eqb_sym;
              try reflexivity;
              try setoid_rewrite T.eqb_sym at 2;
              try reflexivity;
              try solve[crush]].
Qed.
Hint Resolve beq_st_refl.

Lemma beq_e_sym:
  forall e e', beq_e e e' = beq_e e' e.
Proof.
  apply (E_ind_mutual 
           (fun s : St => forall s', beq_st s s' = beq_st s' s)
           (fun e : E  => forall e', beq_e e e' = beq_e e' e)
           (fun f : F  => forall f', beq_f f f' = beq_f f' f));
    try solve [intros;
              try destruct s';
              try destruct e';
              try destruct f';
              try simpl;
              try reflexivity;
              refold_term;
              try rewrite H;
              try rewrite H0;
              try rewrite H1;
              try rewrite EVS.BE.eqb_sym;
              try rewrite T.eqb_sym;
              try rewrite Path.eqb_sym;
              try rewrite TVS.BE.eqb_sym;
              try rewrite K.eqb_sym;
              try rewrite Path.beq_ipe_sym;
              try rewrite T.eqb_sym;
              try rewrite beq_nat_sym;
              try rewrite beq_i_sym;
              try reflexivity;
              try setoid_rewrite T.eqb_sym at 2;
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
    try solve [intros;
              try destruct s';
              try destruct e';
              try destruct f';
              try simpl;
              try reflexivity;
              refold_term;
              try rewrite H;
              try rewrite H0;
              try rewrite H1;
              try rewrite EVS.BE.eqb_sym;
              try rewrite T.eqb_sym;
              try rewrite Path.eqb_sym;
              try rewrite TVS.BE.eqb_sym;
              try rewrite K.eqb_sym;
              try rewrite Path.beq_ipe_sym;
              try rewrite T.eqb_sym;
              try rewrite beq_nat_sym;
              try rewrite beq_i_sym;
              try reflexivity;
              try setoid_rewrite T.eqb_sym at 2;
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
    | [ I : EVS.BE.eqb _ _ = true 
        |- _ ] => apply EVS.BE.eqb_to_eq in I; subst
    | [ I : TVS.BE.eqb _ _ = true 
        |- _ ] => apply TVS.BE.eqb_to_eq in I; subst
    | [ I : beq_i _ _ = true 
        |- _ ] => apply beq_i_to_eq in I; subst
    | [ I : beq_nat _ _ = true 
        |- _ ] => symmetry in I; apply beq_nat_eq in I; subst
    | [ I : Path.beq_ipe _ _ = true 
        |- _ ] => apply Path.beq_ipe_to_eq in I; subst
    | [ I : Path.eqb  _ _ = true 
        |- _ ] => apply Path.eqb_to_eq in I; subst
    | [ I : Path.beq_path  _ _ = true 
        |- _ ] => apply Path.eqb_to_eq in I; subst
    | [ I : T.eqb _ _ = true 
        |- _ ] => apply T.eqb_to_eq in I; subst
    | [ I : K.eqb _ _ = true 
        |- _ ] => apply K.eqb_to_eq in I; subst
end.

Lemma beq_st_to_eq:
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
    try solve[inversion H];
    try solve[inversion H0];
    try solve[inversion H1];
    try solve[simpl in H2; inversion H2];
    try solve[
          try refold_term_in H;
          try refold_term_in H0;
          try refold_term_in H1;
          try refold_term_in H2;
          simplify_boolean_and_true;
          apply_beq_eqs_terms;
          reflexivity].
Qed.

Hint Resolve beq_st_to_eq.

Lemma beq_e_to_eq:
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
    try solve[inversion H];
    try solve[inversion H0];
    try solve[inversion H1];
    try solve[inversion H2];
    try solve[
          try refold_term_in H;
          try refold_term_in H0;
          try refold_term_in H1;
          try refold_term_in H2;
          simplify_boolean_and_true;
          apply_beq_eqs_terms;
          reflexivity].
Qed.
Hint Resolve beq_e_to_eq.

Lemma beq_f_to_eq:
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
    try solve[inversion H];
    try solve[inversion H0];
    try solve[inversion H1];
    try solve[inversion H2];
    try solve[
          try refold_term_in H;
          try refold_term_in H0;
          try refold_term_in H1;
          try refold_term_in H2;
          simplify_boolean_and_true;
          apply_beq_eqs_terms;
          reflexivity].
Qed.
Hint Resolve beq_f_to_eq.

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
    | [ I : EVS.BE.eqb _ _ = false 
        |- _ ] => apply EVS.BE.eqb_to_neq in I; subst
    | [ I : T.eqb _ _ = false 
        |- _ ] => apply T.eqb_to_neq in I; subst
    | [ I : beq_i _ _ = false 
        |- _ ] => apply beq_i_to_neq in I; subst
    | [ I : beq_nat _ _ = false
        |- _ ] => apply beq_nat_false in I; subst
    | [ I : Path.beq_ipe _ _ = false 
        |- _ ] => apply Path.beq_ipe_to_neq in I; subst
    | [ I : Path.eqb _ _ = false 
        |- _ ] => apply Path.eqb_to_neq in I; subst
    | [ I : Path.beq_path _ _ = false 
        |- _ ] => apply Path.eqb_to_neq in I; subst
    | [ I : TVS.BE.eqb _ _ = false 
        |- _ ] => apply TVS.BE.eqb_to_neq in I; subst
    | [ I : K.eqb _ _ = false 
        |- _ ] => apply K.eqb_to_neq in I; subst
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
    try solve[inversion H2];
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

Lemma beq_e_to_neq:
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
Hint Resolve beq_e_to_neq.

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
  apply beq_st_to_eq in H.
  apply beq_st_to_eq in H0.
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
  apply beq_e_to_eq in H.
  apply beq_e_to_eq in H0.
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
  apply beq_f_to_eq in H.
  apply beq_f_to_eq in H0.
  subst.
  assumption.
Qed.
Hint Resolve beq_f_trans.

Lemma beq_e_iff_eq:    forall a b, beq_e a b = true <-> a = b.
Proof.
  intros.
  split.
  apply beq_e_to_eq.
  intros.
  rewrite H.
  apply beq_e_refl.
Qed.
Hint Resolve beq_e_iff_eq.

Lemma beq_e_iff_neq:   forall a b, beq_e a b = false <-> a <> b.
Proof.
  intros.
  split.
  apply beq_e_to_neq.
  intros.
  destruct a; destruct b; simpl; try reflexivity.
  admit.
Admitted.  

Hint Resolve beq_e_iff_neq.

Inductive Value : E -> Prop :=
 | IIsAValue    : forall (i : I),              Value (i_e i)
                                                     
 | AmpIsAValue  : forall (x : EVar) (p : Path),   Value (amp (p_e x p)) 

 | DfunIsAValue : forall (t1 t2 : Tau) (s : St), 
                        Value (f_e (dfun t1 t2 s))
 | UfunIsAValue : 
     forall (k : Kappa) (f : F),
       Value (f_e (ufun k f))

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

Definition t := E.
Definition eqb := beq_e.
Definition eqb_refl := beq_e_refl.
Definition eqb_sym := beq_e_sym.
Definition eqb_trans := beq_e_trans.
Definition eqb_to_eq := beq_e_to_eq.
Definition eqb_to_neq := beq_e_to_neq.
Definition eqb_iff_eq := beq_e_iff_eq.
Definition eqb_iff_neq := beq_e_iff_neq.


Ltac destruct_away := 
  repeat match goal with
    | [ |- ?X = true <-> _ ] => destruct X; try solve[crush]
         end.

Lemma eqb_eq : forall x y : t, eqb x y = true <-> eq x y.
Proof.
  induction x; induction y;
  try solve[
        unfold eq;
        unfold eqb;
        destruct_away;
        crush].
Qed.

Lemma eq_refl:
 forall (a : t),
   eq a a.
Proof.
  intros.
  rewrite <- eqb_eq.
  apply beq_e_refl.
Qed.

Lemma eq_sym : forall x y : t, eq x y -> eq y x.
Proof.
  intros.
  rewrite <- eqb_eq.
  rewrite <- eqb_eq in H.
  rewrite beq_e_sym.
  assumption.
Qed.

Lemma eq_trans : 
  forall x y z,
    eq x y -> eq y z -> eq x z.
Proof.
  intros.
  rewrite <- eqb_eq.
  rewrite <- eqb_eq in H.
  rewrite <- eqb_eq in H0.
  apply beq_e_trans with (e:= x) (e0:= y) (e1:= z); try assumption.
Qed.

Instance eq_equiv : Equivalence eq.
Proof. 
  split.
  exact eq_refl.
  exact eq_sym.
  exact eq_trans.
Defined.

Ltac destruct_evidence := 
  repeat match goal with
    | [ |- {(if ?X then True else False)} + { _ } ] => 
      destruct X; try solve[simpl; right; congruence];
      try solve[simpl; left; trivial]
 end.

Lemma eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
Proof.   
  intros.
  destruct x; destruct y;  unfold eq; unfold eqb; destruct_evidence; crush.
Qed.

End TermModule.
