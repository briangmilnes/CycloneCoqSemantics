Set Implicit Arguments.
Require Import LibLN.
Require Import List.

(* This is as close of an equivalent to the STLC Core Light that I can
   get and still have the mutually inductive character I need to 
   understand how to handle the changes in induction and proof.
 Will my introduction of a heap cause problems here? 
   Should I start without let and change application to a substitution
   base? *)

Inductive Tau : Type :=
 | arrow  : Tau -> Tau -> Tau.     

Inductive St : Type :=                        
 | e_s       : E   -> St
 | letx      : E -> St   -> St        
with E : Type :=                              
 | bevar     : nat -> E
 | fevar     : var -> E
 | f_e       : F -> E
 | assign    : E -> E -> E
 | appl      : E -> E -> E
with F : Type :=
 | dfun      : Tau -> Tau -> St -> F.

Inductive  term : Type := 
  | term_st : St -> term 
  | term_e :  E -> term 
  | term_f :  F -> term.

Fixpoint open_rec_st  (k : nat) (u : E) (s : St)  {struct s}  : St :=
 match s with 
    | e_s  e      => e_s  (open_rec_e  k u e)
    | letx e s1   => letx (open_rec_e (S k) u e) (open_rec_st (S k) u s1)
  end 
with open_rec_e   (k : nat) (u : E) (e : E) {struct e}  : E :=
  match e with 
    | bevar i      => If k = i then u else (bevar i)
    | fevar i      => fevar i
    | f_e f        => f_e  (open_rec_f (S k) u f)
    | assign e1 e2 => assign (open_rec_e k u e1) (open_rec_e k u e2)
    | appl e1 e2   => appl   (open_rec_e k u e1) (open_rec_e k u e2)
  end 
with open_rec_f   (k : nat) (u : E) (f : F) {struct f} : F :=
  match f with 
    | dfun tau1 tau2 s => dfun tau1 tau2 (open_rec_st (S k) u s)
  end.

Fixpoint open_rec_term (k : nat) (u : E) (t : term) {struct t} : term :=
  match t with 
    | term_st s    => term_st (open_rec_st k u s)
    | term_e  e    => term_e  (open_rec_e  k u e)
    | term_f  f    => term_f  (open_rec_f  k u f)
  end.

Definition open t u := open_rec_term 0 u t.


(* TLC uses term for valid term, we're using a locally closed predicate
  which is what it means. *)
Inductive lc_st : St -> Prop := 
 | lc_st_e_s  : forall e, lc_e e -> lc_st (e_s e)
 | lc_st_letx : forall e (s1 : St),
                  lc_e e ->
                  forall L s1,
                  (forall x, x \notin L -> lc_st (open_rec_st 0 (fevar x) s1 )) ->
                  lc_st (letx e s1)
with      lc_e : E -> Prop :=
 | lc_e_fevar : forall x, lc_e (fevar x)
 | lc_f_e     : forall f, lc_f f -> lc_e (f_e f)
 | lc_assign  : forall e1 e2, lc_e e1 -> lc_e e2 -> lc_e (appl e1 e2) 
 | lc_appl    : forall e1 e2, lc_e e1 -> lc_e e2 -> lc_e (appl e1 e2)
with      lc_f : F -> Prop :=
 | lc_dfun : forall t1 t2 s L,
               (forall x, x \notin L -> lc_st (open_rec_st 0 (fevar x) s)) ->
               lc_f (dfun t1 t2 s).

Inductive lc_term : term -> Prop := 
  | lc_term_st : forall s, lc_st s -> lc_term (term_st s)
  | lc_term_e  : forall e, lc_e  e -> lc_term (term_e  e)
  | lc_term_f  : forall f, lc_f  f -> lc_term (term_f  f).

(** Environment is an associative list mapping variables to types. *)
Definition Gamma := LibEnv.env Tau.
Definition Heap := LibEnv.env E.

(* Restrict value. *)

(* Do I need value on Terms instead of E? *)
Inductive Value : E -> Prop :=
 | DfunIsAValue : forall (t1 t2 : Tau) (s : St), Value (f_e (dfun t1 t2 s)).

(* Restrict S, R and L to our subset and in this case L goes away. *)

Inductive S : Heap -> St -> Heap -> St -> Prop :=
 | S_let_3_1 : forall (x : var) (v : E) (h : Heap) (s: St),
                 Value v ->
                 get x h = None -> 
                 S h (letx v s) ((x,v) :: h) s

 | S_let_3_1' : forall (x : var) (v v' : E) (h : Heap) (s: St),
                 Value v ->
                 get x h = Some v' -> 
                 S h (letx v s) (concat (single x v) h) s

 | S_letx_3_9_4: forall (h h' : Heap) (e e' : E) (s : St) (x : var),
                   R h (e_s e) h' (e_s e') ->
                   S h (letx e s) h' (letx e' s)

with R : Heap -> St -> Heap -> St -> Prop :=
 | R_get_3_1 : forall (h  : Heap) (x : var) (v v' : E),
                    get x h = Some v' -> 
                    Value v' ->
                    R h (e_s (fevar x)) h (e_s v)

 | R_assign_3_2:
     forall (h' h : Heap) (v : E) (x : var),
       get x h  = Some v ->
       Value v   ->
       R h                      (e_s (assign (fevar x) v))
        (concat (single x v) h) (e_s v)

 | R_initial_assign_3_2:
     forall (h' h : Heap) (v : E) (x : var),
       get x h = None ->
       Value v   ->
       R h  (e_s (assign (fevar x) v))
         ((x,v) :: h) (e_s v)


 | R_appl_3_5:   forall (h : Heap) (x : var) (tau tau' : Tau) (v : E) (s : St),
                    Value v ->
                    R h (e_s (appl (f_e (dfun tau tau' s)) v))
                      h (letx v s)

 | R_assign_3_9_2: forall (h h' : Heap) (e e' e2: E),
                   L h (e_s e)             h' (e_s e') ->
                   R h (e_s (assign e e2)) h' (e_s (assign e' e2))

 | R_assign_3_10_3: forall (h h' : Heap) (e e' : E) (x : var),
                    R h (e_s e) h' (e_s e') ->
                    R h  (e_s (assign (fevar x) e))
                      h' (e_s (assign (fevar  x) e'))

 | R_appl_3_10_9:  forall (h h' : Heap) (e e' e2 : E),
                    R h  (e_s e) h' (e_s e') ->
                    R h  (e_s (appl e e2))
                      h' (e_s (appl e' e2))

 | R_appl_3_10_10: forall (h h' : Heap) (v e e': E),
                     Value v ->
                     R h  (e_s e) h' (e_s e') ->
                     R h  (e_s (appl v e))
                       h' (e_s (appl v e'))
with L : Heap -> St -> Heap -> St -> Prop :=
  (* eval on the LHS using RHS rules, added just for this *)
   | L_eval: forall (h h' : Heap) (e e': E),
                 R h (e_s e)        h' (e_s e') ->
                 L h (e_s e) h' (e_s e').


(* Define free variables. *)

Fixpoint fv_st (t : St) {struct t} : vars :=
  match t with
    | e_s  e    => fv_e e
    | letx e s  => (fv_e e) \u (fv_st s)
  end
with  fv_e (e : E) {struct e} : vars := 
  match e with 
    | bevar i      => \{}
    | fevar x      => \{x}
    | f_e f        => fv_f f
    | assign e1 e2 => (fv_e e1) \u (fv_e e2)
    | appl e1 e2   => (fv_e e1) \u (fv_e e2)
  end
with  fv_f (f : F) {struct f} : vars := 
  match f with
  | dfun t1 t2 s => (fv_st s)
end.

Fixpoint fv_term (t : term) {struct t} : vars :=
  match t with 
    | term_st s    => fv_st s
    | term_e  e    => fv_e e
    | term_f  f    => fv_f f 
 end.

(* Define subst. *)

Fixpoint subst_st (z : var) (u : E) (s : St) {struct s} : St := 
 match s with 
   | e_s  e      => e_s  (subst_e z u e)
   | letx e s    => letx (subst_e z u e) (subst_st z u s)
 end
with  subst_e  (z : var) (u : E) (e : E) {struct e} : E :=
 match e with
   | bevar i       => bevar i
   | fevar x       => If x = z then u else (fevar x)
   | f_e f         => f_e (subst_f z u f)
   | assign e1 e2  => assign (subst_e z u e1) (subst_e z u e2)
   | appl   e1 e2  => appl (subst_e z u e1) (subst_e z u e2)
 end
with subst_f  (z : var) (u : E) (f : F) {struct f} : F :=
 match f with 
   | dfun t1 t2 s => dfun t1 t2 (subst_st z u s)
end.

Fixpoint subst_term (z : var) (u : E) (t : term) {struct t} : term :=
  match t with 
    | term_st s    => term_st (subst_st z u s)
    | term_e  e    => term_e (subst_e z u e)
    | term_f  f    => term_f (subst_f z u f)
 end.

(* Restrict styp, ltyp and rtyp while dropping K and AK. *)
(* Restricted, translated but definitely needs testing. *)

Notation "[ z ~> u ] t" := (subst_st z u t) (at level 68).
Notation "{ k ~> u } t" := (open_rec_st k u t) (at level 67).
Notation "t ^^ u"       := (open_rec_st 0 u t) (at level 67).
Notation "t ^ x"        := (open_rec_st 0 (fevar x) t).

Inductive styp : Gamma -> Tau -> St   -> Prop :=
  | styp_e_3_1    : forall (G : Gamma) (tau : Tau) (e : E),      
                      rtyp G e  tau -> 
                      styp G tau (e_s e)

  | styp_let_3_6    :  forall L' (G : Gamma) (tau tau' : Tau) (s : St) (e : E),
                         (forall x, x \notin L' -> 
                          styp (G & x ~ tau') tau (s ^ x)) ->
                          rtyp G e    tau' ->
                          styp G tau  (letx e s)

with      ltyp :   Gamma -> E -> Tau -> Prop := 

  | SL_3_1     : forall (G : Gamma) (x : var) (tau: Tau),
                      get x G = Some tau ->
                      ltyp G (fevar x) tau

with      rtyp :  Gamma -> E   -> Tau -> Prop := 
  | SR_3_1  : forall (G : Gamma) (x  : var) (tau: Tau),
                   get x G = Some tau -> 
                   rtyp G (fevar x) tau

  | SR_3_9  : forall (G : Gamma) (e1 e2 : E) (tau tau' : Tau),
                   rtyp G e1 (arrow tau' tau) ->
                   rtyp G e2 tau' ->
                   rtyp G (appl e1 e2) tau

  | SR_3_13 : forall L' (G : Gamma) (tau tau': Tau) (s : St) (x : var),
                   get x G = None ->
                   (forall x, x \notin L' -> 
                      styp (G & x ~ tau) tau' (s ^ x)) -> 
                   rtyp G (f_e (dfun tau tau' s)) (arrow tau tau').

Scheme styp_ind_mutual := Induction for styp Sort Prop
with   ltyp_ind_mutual := Induction for ltyp Sort Prop
with   rtyp_ind_mutual := Induction for rtyp Sort Prop.

(* TODO why can't I get ltyp to work in here with one clause ? *)
(* But I don't use it anyway. *)
Combined Scheme typ_ind_mutual from styp_ind_mutual, rtyp_ind_mutual.

Notation "G |s= s ~: tau" := (styp G tau s) (at level 69).
Notation "G |r= e ~: tau" := (rtyp G e tau) (at level 69).
Notation "G |l= e ~: tau" := (ltyp G e tau) (at level 69).


Axiom subst_open_var : forall x y u t, y <> x -> lc_e u ->
  ([x ~> u]t) ^ y = [x ~> u] (t ^ y).

Axiom subst_intro : forall x t u, 
  x \notin (fv_st t) -> lc_e u ->
  t ^^ u = [x ~> u](t ^ x).

Definition body t :=
  exists L', forall x, x \notin L' -> lc_st (t ^ x).

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let C := gather_vars_with (fun x : (env Tau) => dom x) in
  let D := gather_vars_with (fun x : term => (fv_term x)) in
  let E' := gather_vars_with (fun x : St => (fv_st x)) in
  let F' := gather_vars_with (fun x : E => (fv_e x)) in
  let G := gather_vars_with (fun x : F => fv_f x) in
  constr:(A \u B \u C \u D \u E' \u F' \u G).

Ltac pick_fresh Y :=
  let L' := gather_vars in (pick_fresh_gen L' Y).

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; auto*.

Hint Constructors St E F term Value S R L.

(* Whoa! really sketchy. *)
(** Assume well-formedness always holds. The purpose of these tactics is 
    to save the user from fixing the details when he first wants
    to set up the basic architecture of the proof. These assumptions 
    can be exploited to prove "False" and thus proof any proposition to be
    true, but this has to be done on purpose. Completing a proof of 
    subject reduction without an explicit hack of these assumption is
    likely to be a very good starting point towards a complete formalization. *)

(* Well his STLC Light proofs run without this.  *)
(*
Hint Extern 1 (term _) => skip.
Hint Extern 1 (body _) => skip.
Hint Extern 1 (ok _) => skip. *)

(* Type weakening. *)

(* This looks like it can prove my theorems in the LN style. *)
Lemma styp_weaken : 
  forall (A B C : Gamma) (tau : Tau) (s : St),
   (A & C) |s= s ~: tau ->
   ok (A & B & C) ->
   (A & B & C) |s= s ~: tau.
Proof.
  introv Typ. 
  gen_eq H: (A & C). 
  gen C.
  induction Typ;intros g EQ Ok; subst.
  apply styp_e_3_1 with (tau := tau). (* need the mutual induction. *)
  admit.

  rewrite <- concat_assoc.
  (* How to use apply fresh here? *)
  apply styp_let_3_6  with (L':= L') (tau':= tau'); try assumption.
  intros.
  specialize (H0 x H2 (g & x ~ tau')).
  rewrite concat_assoc.
  rewrite <- concat_assoc.
  apply H0.
  rewrite concat_assoc.
  eauto.
  eauto.
Admitted.

(* Okay this is going to work. *)
Lemma styp_weaken_mutual: 
  forall (A B C : Gamma) (tau : Tau) (s : St),
   (A & C) |s= s ~: tau ->
   ok (A & B & C) ->
   (A & B & C) |s= s ~: tau.
Proof.
  introv Typ. 
  gen_eq H: (A & C). 
  gen C.
  apply (styp_ind_mutual 
           (fun (H0 : Gamma) (tau0 : Tau) (s0 : St)
                (Z : H0 |s= s0 ~: tau0)  =>
              forall C : Gamma, 
                H0 = A & C ->
                ok (A & B & C) -> 
                A & B & C |s= s0 ~: tau0)
           (fun (H0 : Gamma) (e0 : E) (tau0 : Tau) 
                (Z : H0 |l= e0 ~: tau0)  =>
              forall C : Gamma, 
                H0 = A & C ->
                ok (A & B & C) -> 
                A & B & C |l= e0 ~: tau0)
           (fun (H0 : Gamma) (e0 : E) (tau0 : Tau)
                (Z : H0 |r= e0 ~: tau0)  =>
              forall C : Gamma, 
                H0 = A & C ->
                ok (A & B & C) -> 
                A & B & C |r= e0 ~: tau0)); try assumption.
  intros.
  constructor.
  apply H0 in H1; try assumption.

  (* Binding case 1 let works. *)
  intros.
  subst.
  apply_fresh* styp_let_3_6 as y; try assumption; intros.
  assert (Z: y \notin L').
  admit.
  rewrite <- concat_assoc.
  apply H0 with (C0:= C & y ~ tau').
  admit.
  rewrite concat_assoc.
  reflexivity.
  admit. (* y not in dom a b c. *)

  constructor.
  admit. (* map extension agreement *)
  constructor.
  admit. (* again *)
  
  admit. (* application should be good. *)
  intros.
  subst.
  apply_fresh* SR_3_13 as y; try assumption; intros.
  (* get stuck with an existential *)
  skip.
  rewrite <- concat_assoc.
  apply H0 with (C0:= C & y ~ tau0).
  admit.
  rewrite concat_assoc.
  reflexivity.
  admit.
Admitted.

(* Type subst *)

Lemma typing_subst :
  forall A C x tau tau' e s,
    A & x ~ tau & C |s= s ~: tau' ->
    A |s= e_s e ~: tau ->
    A & C |s= [x ~> e]s ~: tau'.
Proof.
  introv Typt Typu. 
  gen_eq G: (A & x ~ tau & C). 
  gen C.
  induction Typt; intros Z Y; subst.
  simpl subst_st.
  simpl subst_e.



  intros.
Admitted.


(* Type preservation. *)
(* Type progress. *)