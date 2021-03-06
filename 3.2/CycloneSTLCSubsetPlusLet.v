Set Implicit Arguments.
Require Import LibLN.
Require Import List.

(* This is as close of an equivalent to the STLC Core Light that I can
   get and still have the mutually inductive character I need to 
   understand how to handle the changes in induction and proof.
 Will my introduction of a heap cause problems here? 
   Should I start without let and change application to a substitution
   base? *)

Inductive Kappa : Type :=
 | B                         (* 'boxed' kind. *)
 | A.                        (* 'any'   kind. *)

Inductive Tau : Type :=
 | btvar     : nat -> Tau
 | ftvar     : var -> Tau
 | arrow     : Tau -> Tau -> Tau    
 | utype     : Kappa -> Tau -> Tau.

Fixpoint fv_tau (tau : Tau) {struct tau} : vars :=
  match tau with
    | btvar i     => \{}
    | ftvar x     => \{x}
    | arrow t0 t1 => (fv_tau t0) \u (fv_tau t1)
    | utype k t   => (fv_tau t)
end.

Fixpoint open_rec_tau  (k : nat) (tau' : Tau) (tau : Tau)  {struct tau}  : Tau :=
 match tau with 
   | btvar i      => If k = i then tau' else (btvar i)
   | ftvar i      => ftvar i
   | arrow t0 t1 => arrow (open_rec_tau k tau' t0) (open_rec_tau k tau' t1)
   | utype kp t  => utype kp (open_rec_tau (S k) tau' t)
  end.

Inductive lc_tau : Tau -> Prop := 
 | lc_tau_ftvar : forall x, lc_tau (ftvar x)
 | lc_tau_arrow  : forall t0 t1, lc_tau t0 -> lc_tau t1 -> lc_tau (arrow t0 t1)
 | lc_tau_utype : forall L' k t,
                  (forall alpha, alpha \notin L' -> lc_tau (open_rec_tau 0 (ftvar alpha) t )) ->
                  lc_tau (utype k t).

Definition Delta := LibEnv.env Kappa.

(* TODO Oy, he's right oriented. *)
Inductive WFD : Delta -> Prop :=
  | WFD_nil    : WFD empty
  | WFD_xtau   : forall (d : Delta) (alpha : var) (k : Kappa),
                 get alpha d = None ->
                 WFD d ->
                 WFD (d & alpha ~ k).

(* Hmm, free vs bound tvars? *)
Inductive K : Delta -> Tau -> Kappa -> Prop :=
 | K_B     : forall (d : Delta) (alpha : var),
               get alpha  d = Some B ->
               K d (ftvar alpha) B

 | K_B_A     : forall (d : Delta) (tau : Tau),
                  K  d tau B ->
                  K  d tau A

 | K_arrow   : forall (d : Delta) (t0 t1 : Tau),
                    K d t0 A ->
                    K d t1 A ->
                    K d (arrow t0 t1) A

 | K_utype  : forall L' (d : Delta) (k : Kappa) (tau : Tau),
                (* Open the body. *)
                 (forall alpha, alpha \notin L' -> 
                   WFD (d & alpha ~ k) ->
                   get alpha d = None ->
                   K (d & alpha ~ k) (open_rec_tau 0 (ftvar alpha) tau) A) ->
                   K d (utype k tau) A.

(* Looks good, recheck with utype in there. *)
Lemma inductiononKA:
  forall d tau,
    K d tau B ->
    K d tau A.
Proof.
  intros.
  induction H; try intros.
  admit.
  admit.
  admit. (* Good but duplicated. *)
  admit. (* good. *)
Qed.

Lemma inductiononKd:
  forall d e alpha tau,
    K (d & alpha ~ B & e) tau B ->
    K d tau A.
Proof.
  intros.
  induction H; try intros.
  admit. (* Disconnected. *)
  admit. (* Connected and disconnected. Weird. *)
  admit. (* Disconnected. *)
  admit.
Qed.

(* This seems to work! Yeah. *)
Lemma inductiononKd1:
  forall d e alpha tau,
    K (d & alpha ~ B & e) tau B ->
    K d tau A.
Proof.
  intros.
  gen_eq G: (d & alpha ~ B  & e).
  Unset Ltac Debug.
  gen e.
  induction H; try intros.
  admit. (* Connected. *)
  admit. (* Connected. *)
  admit. (* Connected! *)
  admit.
Qed.

(* Okay try a real lemma! *)
(* Will this form work or do I need d & alpha ~ k & d' ? *)

(* Introduced too early so not recursing terms for type variables. *)
Ltac gather_tvars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let C := gather_vars_with (fun x : (env Tau) => dom x) in
  let H := gather_vars_with (fun x : Tau => fv_tau x) in
  constr:(A \u B \u C \u H).

Ltac pick_tfresh Y :=
  let L' := gather_tvars in (pick_fresh_gen L' Y).

Tactic Notation "apply_tfresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_tvars x.

Tactic Notation "apply_tfresh" "*" constr(T) "as" ident(x) :=
  apply_tfresh T as x; auto*.

(* This might be good also! *)
Lemma K_strengthening_add_right:
  forall (d : Delta) (tau : Tau) (k : Kappa),
      WFD d ->
      K d tau k -> 
      forall (alpha : var) (k' : Kappa),
        WFD (d & alpha ~ k') ->
        K (d & alpha ~ k') tau k.
Proof.
  introv WFDder Kder.
  induction Kder; intros.
  inversion H0.
  (* What's his tactic ? *)
  skip.
  constructor.
  (* invert H1 to get d = d0 and alpha1 = alpha0 and k = k'. *)
  (* then alpha is in d from H and so H0 is false. *)
  admit.
  constructor.
  apply IHKder; try assumption.

  apply K_arrow.
  apply IHKder1; try assumption.
  apply IHKder2; try assumption.

  apply_tfresh K_utype as y.  
  intros.
  (* have to swap alpha ~ k' & y ~ k for y ~ k & alpha ~ k'. *)
  assert (Z: (d & alpha ~ k' & y ~ k) = (d & y ~ k & alpha ~ k')).
  admit.
  rewrite Z in *.
  apply H0.
  auto.
  skip.
  admit. (* y new, fresh missing domain of d. *)
  admit. (* y fresh. *)
  admit. (* y = alpha, H2 inversion. *)
         (* y <> alpha, y fresh OK. *)
Admitted.

(* This looks great! *)
Lemma K_strengthening_concat:
  forall (d : Delta) (tau : Tau) (k : Kappa),
      WFD d ->
      K d tau k -> 
      forall (d' : Delta),
        WFD (d & d')  ->
        K (d & d') tau k.
Proof.
  introv WFDder Kder.
  induction Kder; intros.
  constructor.
  admit. (* get weakening. *)
  
  constructor.
  apply IHKder; try assumption.

  assert (Z: WFD d).
  admit. (* WFD str *)
  apply K_arrow; try assumption.
  apply IHKder1; try assumption.
  apply IHKder2; try assumption.

  apply_tfresh K_utype as y.  
  intros.
  assert (Z: d & d' & y ~ k = d & y ~ k & d').
  admit.
  rewrite Z in *.
  apply H0; try assumption.
  auto.
  admit. (* WFD str *)
  admit. (* Y fresh. *)
  admit. (* Y fresh. *)
Admitted.

Lemma K_strengthening_extends:
  forall (d : Delta) (tau : Tau) (k : Kappa),
      WFD d ->
      K d tau k -> 
      forall (d' : Delta),
        WFD d' ->
        extends d d' -> 
        K d' tau k.
Proof.
  introv WFDder Kder.
  induction Kder; intros.
  constructor.
  admit. (* get extends agreement *)
  
  constructor.
  apply IHKder; try assumption.

  apply K_arrow; try assumption.
  apply IHKder1; try assumption.
  apply IHKder2; try assumption.

  apply_tfresh K_utype as y.  
  intros.
  apply H0; try assumption.
  auto.
  admit. (* WFD str *)
  admit. (* Y fresh. *)
  admit. (* Y fresh. *)
  admit. (* extends extension agreement. *)
Admitted.

(* Good! *)
Lemma K_strengthening_add_right_B:
  forall (d : Delta) (tau : Tau),
      WFD d ->
      K d tau B -> 
      forall (alpha : var) (k' : Kappa),
        WFD (d & alpha ~ k') ->
        K (d & alpha ~ k') tau B.
Proof.
  introv WFDder Kder.
  induction Kder; intros.
  admit. 
  admit.
  admit.
  admit.
Admitted.

Lemma K_strengthening_add_middle:
  forall (d d' : Delta) (tau : Tau) (k : Kappa),
      WFD (d & d') ->
      K d tau k -> 
      forall (alpha : var) (k' : Kappa),
        WFD (d & alpha ~ k' & d')  ->
        K (d & alpha ~ k' & d') tau k.
Proof.
  introv WFDder Kder.
  induction Kder; intros.
  admit.
  admit.
  admit.
  admit.
Admitted.
  
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
                  forall L' s1,
                  (forall x, x \notin L' -> lc_st (open_rec_st 0 (fevar x) s1 )) ->
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
with subst_e  (z : var) (u : E) (e : E) {struct e} : E :=
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


(* Restrict S, R and L to our subset and in this case L goes away. *)

Inductive S : Heap -> St -> Heap -> St -> Prop :=
 (* let execution rules are wrong, there is no x. *)
 | S_let_3_1 : forall (x : var) (v : E) (h : Heap) (s: St),
                 Value v ->
                 S h (letx v s) ((x,v) :: h) (s ^ x)

 | S_let_3_1' : forall (x : var) (v v' : E) (h : Heap) (s: St),
                 Value v ->
                 binds x v' h ->
  (* not overwriting, taking the first binding. *)
                 S h (letx v s) ((x,v) :: h) (s ^ x)   

| S_exp_3_9_1: forall (h h' : Heap) (e e' : E),
                   R h (e_s e) h' (e_s e') ->
                   S h (e_s e) h' (e_s e')

 | S_letx_3_9_4: forall (h h' : Heap) (e e' : E) (s : St) (x : var),
                   R h (e_s e) h' (e_s e') ->
                   S h (letx e s) h' (letx e' s)

with R : Heap -> St -> Heap -> St -> Prop :=
 | R_get_3_1 : forall (h  : Heap) (x : var) (v v' : E),
                    binds x v' h ->
                    Value v' ->
                    R h (e_s (fevar x)) h (e_s v)

 | R_assign_3_2:
     forall (h' h : Heap) (v : E) (x : var),
       binds x v h ->
       Value v   ->
(* not overwriting, taking the first binding. *)
       R h (e_s (assign (fevar x) v))
         ((x,v) :: h) (e_s v)

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
                      binds x tau G ->
                      ltyp G (fevar x) tau

with      rtyp :  Gamma -> E   -> Tau -> Prop := 
  | SR_3_1  : forall (G : Gamma) (x  : var) (tau: Tau),
                   binds x tau G ->
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
  gen_eq H: (A0 & C). 
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
  forall (a b c : Gamma) (tau : Tau) (s : St),
   (a & c) |s= s ~: tau ->
   ok (a & b & c) ->
   (a & b & c) |s= s ~: tau.
Proof.
  introv Typ. 
  gen_eq H: (a & c). 
  gen c.
  apply (styp_ind_mutual 
           (fun (H0 : Gamma) (tau0 : Tau) (s0 : St)
                (Z : H0 |s= s0 ~: tau0)  =>
              forall c : Gamma, 
                H0 = a & c ->
                ok (a & b & c) -> 
                a & b & c |s= s0 ~: tau0)
           (fun (H0 : Gamma) (e0 : E) (tau0 : Tau) 
                (Z : H0 |l= e0 ~: tau0)  =>
              forall c : Gamma, 
                H0 = a & c ->
                ok (a & b & c) -> 
                a & b & c |l= e0 ~: tau0)
           (fun (H0 : Gamma) (e0 : E) (tau0 : Tau)
                (Z : H0 |r= e0 ~: tau0)  =>
              forall c : Gamma, 
                H0 = a & c ->
                ok (a & b & c) -> 
                a & b & c |r= e0 ~: tau0)); try assumption.
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
  induction Typt. 

  intros.
  subst.
  simpl subst_st.
  induction e0; simpl subst_e; constructor.
  inversion H.
  inversion H; subst.
  case_var.
  binds_get H2.
  admit.
  admit.
  constructor.
  admit.
  destruct f.
  simpl.
  (* Just not sure what I'm doing here yet. *)
  admit.
  
  

Admitted.

Lemma typing_subst_mutual :
  forall A C x tau tau' e s,
    A & x ~ tau & C |s= s ~: tau' ->
    A |s= e_s e ~: tau ->
    A & C |s= [x ~> e]s ~: tau'.
Proof.
  introv Typt Typu. 
  gen_eq G: (A & x ~ tau & C). 
  gen C.

  apply (styp_ind_mutual 
           (fun (H0 : Gamma) (tau0 : Tau) (s0 : St) (Z : H0 |s= s0 ~: tau0) =>
              forall C : env Tau, 
                H0 = A & x ~ tau & C -> 
                A & C |s= (subst_st x e s0) ~: tau0)
           (fun (H0 : Gamma) (e0 : E) (tau0 : Tau)  (Z : H0 |l= e0 ~: tau0) =>
              forall C : env Tau, 
                H0 = A & x ~ tau & C -> 
                A & C |l= (subst_e x e e0) ~: tau0)
           (fun (H0 : Gamma) (e0 : E) (tau0 : Tau)  (Z : H0 |r= e0 ~: tau0)  =>
              forall C : env Tau, 
                H0 = A & x ~ tau & C -> 
                A & C |r= (subst_e x e e0) ~: tau0)); try assumption; intros; subst.
  try specialize (H C).
  simpl.
  constructor.
  apply H.
  reflexivity.

  admit.

  simpl.
  case_var.
  admit.
  admit. (* doable. *)

  simpl.
  case_var.
  inversion Typu; subst.
  binds_get b.
  admit.
  admit. (* r weakening. *)
  admit. (* binds weakening. *)

(* a clean case for app *)
  specialize (H C).
  specialize (H0 C).
  simpl.
  apply SR_3_9 with (tau':= tau'0).
  apply H.
  reflexivity.
  apply H0.
  reflexivity.

  (* don't really now what I'm doing here yet. *)
  (* x, x0, y too confusing. *)
  simpl.
  apply_fresh SR_3_13 as y.
  skip.
  specialize (s1 ).
  specialize (H y).
  skip Z: (y \notin L').
(*
  specialize (s1 Z).
  specialize (H Z).
  *)
  

Admitted.
  
(* Type preservation. *)

Lemma preservation_result : forall G s h s' h' tau,
  G |s= s ~: tau ->
  S h s h' s' ->
  G |s= s' ~: tau.
Proof.
  introv Typ. 
  gen s'.
  induction Typ; intros.
  
  inversion H0; subst.
  constructor.
  admit. (* not nearly strong enough induction hypothesis. *)
  
  inversion H2; subst.   
  admit.
  admit.
  (* not sure either here. *)


Admitted.

Print styp_ind_mutual.

Lemma foo:
  forall n n' : nat,
    (If n = n' then True else False).
Proof.
  intros.
  case_if_eq_nat.
  skip.
  skip.
Qed.

(* Definitely need heap typing agreement for variables. *)
Lemma preservation_result_mutual_ind : forall G s h s' h' tau,
  G |s= s ~: tau ->
  S h s h' s' ->
  G |s= s' ~: tau.
Proof.
  introv Typ. 
  gen s'.
  apply (styp_ind_mutual 
           (fun (G : Gamma) (tau : Tau) (s : St) (Z : G |s= s ~: tau) =>
                 forall s' : St, 
                   S h s h' s' -> 
                   G |s= s' ~: tau)
           (fun (G : Gamma) (e : E) (tau : Tau)  (Z : G |l= e ~: tau) =>
                 forall e' : E,
                   L h (e_s e) h' (e_s e') -> 
                   G |l= e' ~: tau)
           (fun (G : Gamma) (e : E) (tau : Tau)  (Z : G |r= e ~: tau)  =>
                 forall e' : E,
                   R h (e_s e) h' (e_s e') -> 
                   G |r= e' ~: tau)); try assumption; intros.
  (* Perhaps this is strong enough but I'm not sure I'm getting the right inductive
    hypotheses when I cross from S -> R. *)
  admit. (* Looks good. *)
  admit. (* Looks good. *)
  inversion H; subst.
  inversion H4; subst.
  admit. (* no inductive hyp, but do I need one? *)
  inversion H; subst.
  (* need heap well formedness to make this go. *)
  admit.
  admit.
  admit.
Admitted.

(* Type progress. *)

Lemma progress_result : forall s tau,
  empty |s= s ~: tau ->
     (exists e, s = (e_s e) /\ Value e)
  \/ exists h h' s', S h s h' s'.
Proof. 
 introv Typ. gen_eq E: (empty : env Tau). 
 lets Typ': Typ.
 induction Typ; intros; subst.
 destruct e. 
 inversion H.
 inversion H.
 false* binds_empty_inv. 

 left.
 apply ex_intro with (x:= (f_e f)).
 split.
 reflexivity.
 destruct f.
 constructor.

 right.
 admit. (* steps. *)

 right. 
 admit. (* steps. *)

 right.
 admit. (* steps. *)

Qed.


