Set Implicit Arguments.
Require Import LibLN.
Require Import List.

(* A minimal representative set of Cyclone to work with in LN. *)
(* This is too much, I should duplicate the STLC so I have the 
  simplest model for discovering how to handle the complications
  of mutually recursive definitions and induction. *)

Inductive Tau : Type :=
 | btvar  : nat -> Tau                            (* bound type variable. *)
 | ftvar  : var -> Tau                            (* free type variable. *)
 | cint   : Tau                 
 | arrow  : Tau -> Tau -> Tau.     

Inductive I  : Type :=  
 | i_i       : nat -> I.                       

Inductive St : Type :=                        
 | e_s       : E   -> St                      
 | retn      : E   -> St                      
 | seq       : St  -> St -> St                
 | letx      : E -> St   -> St        
with E : Type :=                              
 | i_e       : I -> E                        
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
    | retn e      => retn (open_rec_e  k u e)
    | seq s1 s2   => seq  (open_rec_st k u s1)   (open_rec_st k u s2)
    | letx e s1   => letx (open_rec_e (S k) u e) (open_rec_st (S k) u s1)
  end 
with open_rec_e   (k : nat) (u : E) (e : E) {struct e}  : E :=
  match e with 
    | bevar i      => If k = i then u else (bevar i)
    | fevar i      => fevar i
    | i_e n        => i_e n
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
(* I need three versions of this. *)
Notation "{ k ~> u } t" := (open_rec_term k u t) (at level 67).
Notation "t ^^ u" := (open_rec_term 0 u t) (at level 67).
Notation "t ^ x" := (open_rec_term 0 (fevar x) t).

(* TLC uses term for valid term, we're using a locally closed predicate
  which is what it means. *)
Inductive lc_st : St -> Prop := 
 | lc_st_e_s  : forall e, lc_e e -> lc_st (e_s e)
 | lc_st_retn : forall e, lc_e e -> lc_st (retn e)
 | lc_st_seq  : forall s1 s2, lc_st s1 -> lc_st s2 -> lc_st (seq s1 s2)
 | lc_st_letx : forall e (s1 : St),
                  lc_e e ->
                  forall L s1,
                  (forall x, x \notin L -> lc_st (open_rec_st 0 (fevar x) s1 )) ->
                  lc_st (letx e s1)
with      lc_e : E -> Prop :=
 | lc_e_fevar : forall x, lc_e (fevar x)
 | lc_f_e     : forall f, lc_f f -> lc_e (f_e f)
 | lc_e_i_e   : forall n, lc_e (i_e n)
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
(* Can't define upsilon using these as they expect var * argument. *)

Definition Gamma := LibEnv.env Tau.
Definition Heap := LibEnv.env E.

(* Restrict value. *)

Inductive Value : E -> Prop :=
 | IIsAValue    : forall (i : I), Value (i_e i)
 | DfunIsAValue : forall (t1 t2 : Tau) (s : St), Value (f_e (dfun t1 t2 s)).

(* Restrict S, R and L and allow assignment to a variable.  *)
(* TODO this is wrong in so many ways. *)

Inductive S : Heap -> St -> Heap -> St -> Prop :=
 | S_let_3_1 : forall (x : var) (v : E) (h : Heap) (s: St),
                 Value v ->
                 get x h = None -> 
                 S h (letx v s) ((x,v) :: h) s

 | S_seq_3_2 : forall (v : E) (h : Heap) (s: St),
                  Value v ->
                  S h (seq (e_s v) s) h s

 | S_return_3_3: forall (v : E) (h : Heap) (s: St),
                    Value v ->
                    S h (seq (retn v) s) h (retn v)

| S_exp_3_9_1: forall (h h' : Heap) (e e' : E),
                   R h (e_s e) h' (e_s e') ->
                   S h (e_s e) h' (e_s e')

| S_ret_3_9_2: forall (h h' : Heap) (e e' : E),
                   R h (e_s e) h' (e_s e') ->
                   S h (retn e) h' (retn e')

| S_letx_3_9_4: forall (h h' : Heap) (e e' : E) (s : St) (x : var),
                   R h (e_s e) h' (e_s e') ->
                   S h (letx e s) h' (letx e' s)
| S_seq_3_10:  forall (h h' : Heap) (s s' s2: St),
                    S h s h' s' ->
                    S h  (seq s  s2) h' (seq s' s2)
with R : Heap -> St -> Heap -> St -> Prop :=
 | R_get_3_1 : forall (h  : Heap) (x : var) (v v' : E),
                    get x h = Some v' -> 
                    Value v' ->
                    R h (e_s (fevar x))
                      h (e_s v')
 | R_assign_3_2:
     forall (h' h : Heap) (v v' v'' : E) (x : var) ,
       get x h = Some v' ->
       (* H.add h x v'' = h' ->   TODO how do I assign ? *)
       Value v   ->
       Value v'  ->
       R h  (e_s (assign (fevar x) v))
         h' (e_s v)

 | R_initial_assign_3_2:
     forall (h' h : Heap) (v : E) (x : var),
       get x h = None ->
       (* H.add h x v = h' ->  TODO *)
       Value v   ->
       R h  (e_s (assign (fevar x) v))
         h' (e_s v)

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
                      h' (e_s (assign (fevar x) e'))

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
 | L_xpi_3_1: forall (h : Heap) (x : var),
                L h (e_s (fevar x))
                  h (e_s (fevar x))  (* TODO, this can't be right. *)
.

(* Define free variables. *)

Fixpoint fv_st (t : St) {struct t} : vars :=
  match t with
    | e_s  e    => fv_e e
    | retn e    => fv_e e
    | seq s1 s2 => (fv_st s1) \u (fv_st s2)
    | letx e s  => (fv_e e) \u (fv_st s)
  end
with  fv_e (e : E) {struct e} : vars := 
  match e with 
    | bevar i      => \{}
    | fevar x      => \{x}
    | i_e  i       => \{}
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
   | retn e      => retn (subst_e z u e)
   | seq  s1 s2  => seq  (subst_st z u s1) (subst_st z u s2)
   | letx e s    => letx (subst_e z u e) (subst_st z u s)
 end
with  subst_e  (z : var) (u : E) (e : E) {struct e} : E :=
 match e with
   | bevar i       => bevar i
   | fevar x       => If x = z then u else (fevar x)
   | i_e n         => i_e n
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

Notation "[ z ~> u ] t" := (subst_term z u t) (at level 68).

(* Restrict styp, ltyp and rtyp while dropping K and AK. *)
(* Restricted, translated but definitely needs testing. *)

Inductive styp : Gamma -> Tau -> St   -> Prop :=
  | styp_e_3_1    : forall (g : Gamma) 
                           (tau tau': Tau) (e : E),      
                      rtyp g e  tau' -> 
                      styp g tau (e_s e)

  | styp_return_3_2 : forall (g : Gamma)
                             (tau : Tau) (e : E),
                         rtyp g e tau ->
                         styp g tau (retn e)

  | styp_seq_3_3    : forall (g : Gamma)
                             (tau : Tau) (s1 s2 : St),
                         styp g tau s1 ->
                         styp g tau s2 ->
                         styp g tau (seq s1 s2)

  | styp_let_3_6    :  forall (g : Gamma)
                               (x : var)  (tau tau' : Tau) 
                               (s : St) (e : E),
                          get x g = None ->
                          styp ((x,tau') :: g) tau s ->
                          rtyp g e    tau' ->
                          styp g tau  (letx e s)

with      ltyp : Gamma -> E -> Tau -> Prop := 

  | SL_3_1     : forall (g : Gamma) (x : var) (tau tau': Tau),
                      get x g = Some tau' ->
                      (* gettype u x nil tau' p tau -> What do I do with gettype? *)
                      (* WFC d g ->
                      K d tau' A -> *) 
                      ltyp g (fevar x) tau  (* Can I just put x here? I don't think so. *)

with      rtyp :  Gamma -> E   -> Tau -> Prop := 
  | SR_3_1  : forall (g : Gamma) (x  : var) (tau tau': Tau),
                   get x g = Some tau' -> 
                   (* gettype u x nil tau' p tau ->
                   K d tau' A ->
                   WFC d g -> *)
                   rtyp g (fevar x) tau

  | SR_3_5  : forall (g : Gamma) (z : nat),
                (* WFC d g -> *)
                   rtyp g (i_e (i_i z)) cint

  | SR_3_8  : forall (g : Gamma) (e1 e2 : E) (tau : Tau),
                   ltyp g e1 tau ->
                   rtyp g e2 tau ->
                   (* ASGN d tau    -> *)
                   rtyp g (assign e1 e2) tau

  | SR_3_9  : forall (g : Gamma) (e1 e2 : E) (tau tau' : Tau),
                   rtyp g e1 (arrow tau' tau) ->
                   rtyp g e2 tau' ->
                   rtyp g (appl e1 e2) tau.

(* How do I make a single typing judgement? *)
(* I guess really I want to prove this three times with mutual induction. *)
(*
Reserved Notation "E |= t ~: T" (at level 69).
Inductive typing : env -> trm -> typ -> Prop :=
where "E |= t ~: T" := (typing E t T).
*)

(** Definition of the body of an abstraction *)

Definition body t :=
  exists L, forall x, x \notin L -> lc_term (t ^ x).

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let C := gather_vars_with (fun x : env => dom x) in
  let D := gather_vars_with (fun x : term => fv_term x) in
  let E := gather_vars_with (fun x : St => fv_st x) in
  let F := gather_vars_with (fun x : E => fv_e x) in
  let G := gather_vars_with (fun x : F => fv_f x) in
  constr:(A \u B \u C \u D \u E \u F \u G).

Ltac pick_fresh Y :=
  let L := gather_vars in (pick_fresh_gen L Y).

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; auto*.

(* How do I make this work?
 Hint Constructors term Value ? *)

(*
Axiom subst_open_var : forall x y u t, y <> x -> lc_term u ->
  ([x ~> u]t) ^ y = [x ~> u] (t ^ y).

Axiom subst_intro : forall x t u, 
  x \notin (fv t) -> term u ->
  t ^^ u = [x ~> u](t ^ x).
*)

(* Whoa! really sketchy. *)
(** Assume well-formedness always holds. The purpose of these tactics is 
    to save the user from fixing the details when he first wants
    to set up the basic architecture of the proof. These assumptions 
    can be exploited to prove "False" and thus proof any proposition to be
    true, but this has to be done on purpose. Completing a proof of 
    subject reduction without an explicit hack of these assumption is
    likely to be a very good starting point towards a complete formalization. *)

(* Well his STLC Light proofs run without this. 
Hint Extern 1 (term _) => skip.
Hint Extern 1 (body _) => skip.
Hint Extern 1 (ok _) => skip.
*)

(* Type weakening. *)

Lemma typing_weaken : 
  forall (A B C : Gamma) (T : Tau) (t : St),
   styp (A & C) T t->
   ok (A & B & C) ->
   styp (A & B & C) T t.
Proof.
  introv Typ. gen_eq H: (A & C). gen C.
  induction Typ; intros G EQ Ok; subst.
(* Need to translate these to four application rules. 
 | e_s       : E   -> St                      
 | retn      : E   -> St                      
 | seq       : St  -> St -> St                
 | letx      : E -> St   -> St        
*)

  apply* SL_3_1.
  apply* binds_weaken.
  apply_fresh* typing_abs as y. 
  apply_ih_bind* H0.
  apply* typing_app.
Qed.

(* Type subst *)
(* Type preservation. *)
(* Type progress. *)