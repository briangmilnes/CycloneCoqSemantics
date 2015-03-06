Set Implicit Arguments.
Require Import List.
Export ListNotations.
Require Import Init.Datatypes.
Require Import Coq.Init.Logic.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.EqNat.
Require Import Coq.Structures.Equalities.

Require Export Coq.MSets.MSets.
Require Export Coq.MSets.MSetInterface.
Require Export Coq.MSets.MSetWeakList.

Require Export EVarModuleDef.
Require Export VariablesSetFunDef.
Require Export TVarModuleDef.
Require Export ContextFunDef.

(*
Require Import DeltaModuleDef.
Require Import GammaModuleDef.
Require Import HeapModuleDef.
Require Import UpsilonModuleDef.
*)

(* Try this again with my style contexts. *)

Module TVM   := TVarModule.
Definition TVar := TVM.Var.
Module TVSM := VariablesSetFun(TVM).
Definition TVars := TVSM.t.

Module EVM   := EVarModule.
Definition EVar := EVM.Var.
Module EVSM := VariablesSetFun(EVM).
Definition EVars := TVSM.t.

Notation "\{}_e" := (EVSM.empty).
Notation "\{ x }_e" := (EVSM.singleton x).
Notation "E \u_e F" := (EVSM.union E F)
  (at level 37, right associativity).
Notation "E \n_e F" := (EVSM.inter E F)
  (at level 36, right associativity).
Notation "E \-_e F" := (EVSM.remove E F)
  (at level 35).
Notation "x \in_e E" := ((EVSM.mem x E) = true) (at level 39).
Notation "x \notin_e E" := ((EVSM.mem x E) = false) (at level 39).
Notation "E \c_e F" := (EVSM.subset E F)
  (at level 38).

(* This is as close of an equivalent to the STLC Core Light that I can
   get and still have the mutually inductive character I need to 
   understand how to handle the changes in induction and proof.
 Will my introduction of a heap cause problems here? 
   Should I start without let and change application to a substitution
   base? *)

Require Export KappaModuleDef.
Module K := KappaModule.
Include KappaModule.Types.

Module D := ContextFun TVM KappaModule.
Definition Delta    := (D.Context  TVar Kappa).
Definition ddot     := (D.cdot     TVar Kappa).
Definition dctxt    := (D.ctxt     TVar Kappa).
Print D.

Notation "x '~d' a" := (D.ctxt x a ddot)
  (at level 27, left associativity).
Notation "E '&d' F" := (D.concat E F) 
  (at level 28, left associativity).

Module T <: BoolEqualitySig.

Module Types.

Inductive Tau : Type :=
 | btvar     : nat -> Tau
 | ftvar     : TVar -> Tau
 | arrow     : Tau -> Tau -> Tau    
 | utype     : Kappa -> Tau -> Tau.
End Types.
Include Types. 

Function eqb (t t' : Tau) : bool :=
 match t, t' with
   | btvar i, btvar j => beq_nat i j
   | ftvar i, ftvar j => TVM.eqb i j
   | (arrow t0 t1), (arrow t0' t1') => andb (eqb t0 t0') (eqb t1 t1')
   | utype kappa tau, utype kappa' tau' =>
     andb (K.eqb kappa kappa')
          (eqb tau tau')
   | _ , _ => false
end.

Fixpoint eq (a b : Tau) : Prop :=
    match eqb a b with
     | false => False
     | true => True
    end.

Ltac destruct_away := 
  repeat match goal with
    | [ |-  false = true <-> _ ] => crush
    | [ |- ?X = true <-> _ ] => destruct X; crush
         end.

Lemma eqb_eq : forall x y : Tau, eqb x y = true <-> eq x y.
Proof.
  induction x; destruct y; simpl; try solve[destruct_away].
Qed.

  Definition t     := Tau.

  Lemma eqb_refl:  forall a,     eqb a a = true. Proof. Admitted.
  Hint Resolve eqb_refl.
  Hint Rewrite eqb_refl.
  
  Lemma eqb_sym:   forall x y,   eqb x y = eqb y x. Proof. Admitted.
  Hint Immediate eqb_sym.
  
  Lemma eqb_trans: forall x y z, eqb x y = true -> eqb y z = true -> eqb x z = true. Proof. Admitted.
  Hint Resolve eqb_trans.
  
  Lemma eqb_to_eq:    forall a b, eqb a b = true -> a = b. Proof. Admitted.
  Hint Resolve eqb_to_eq.

  Lemma eqb_to_neq:   forall a b, eqb a b = false -> a <> b. Proof. Admitted.
  Hint Resolve eqb_to_neq.

  Lemma eqb_iff_eq:    forall a b, eqb a b = true <-> a = b. Proof. Admitted.
  Hint Resolve eqb_iff_eq.

  Lemma eqb_iff_neq:   forall a b, eqb a b = false <-> a <> b. Proof. Admitted.
  Hint Resolve eqb_iff_neq.

Lemma eq_refl: forall (a : Tau),  eq a a.
Proof.
  intros.
  apply eqb_eq.
  apply eqb_refl.
Qed.

Lemma eq_sym : forall x y : Tau, eq x y -> eq y x.
Proof.
  intros.
  apply eqb_eq.
  apply eqb_eq in H.
  rewrite eqb_sym.
  assumption.
Qed.

Lemma eq_trans : 
  forall x y z,
    eq x y -> eq y z -> eq x z.
Proof.
  intros.
  apply eqb_eq in H.
  apply eqb_eq in H0.
  apply eqb_eq.
  apply eqb_trans with (x:= x) (y:= y) (z:= z); try assumption.
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

Lemma eq_dec : forall x y : Tau, {eq x y} + {~ eq x y}.
Proof.   
  intros.
  induction x; induction y; unfold eq; destruct_evidence.
Qed.

Fixpoint fv_tau (tau : Tau) {struct tau} : TVars :=
  match tau with
    | btvar i     => TVSM.empty
    | ftvar x     => TVSM.singleton x
    | arrow t0 t1 => TVSM.union (fv_tau t0) (fv_tau t1)
    | utype k t0   => (fv_tau t0)
end.

Fixpoint open_rec_tau  (k : nat) (tau' : Tau) (tau : Tau)  {struct tau}  : Tau :=
 match tau with 
   | btvar i      => if (beq_nat k i) then tau' else (btvar i)
   | ftvar i      => ftvar i
   | arrow t0 t1 => arrow (open_rec_tau k tau' t0) (open_rec_tau k tau' t1)
   | utype kp t0  => utype kp (open_rec_tau (S k) tau' t0)
  end.

Inductive lc_tau : Tau -> Prop := 
 | lc_tau_ftvar : forall x, lc_tau (ftvar x)
 | lc_tau_arrow  : forall t0 t1, lc_tau t0 -> lc_tau t1 -> lc_tau (arrow t0 t1)
 | lc_tau_utype : forall L' k t,
                  (forall alpha, (TVSM.mem alpha L') = false
                                 -> lc_tau (open_rec_tau 0 (ftvar alpha) t )) ->
                  lc_tau (utype k t).
End T.
Include T.Types.

Module G := ContextFun EVM T.
Definition Gamma    := (G.Context EVar Tau).
Definition gdot     := (G.cdot    EVar Tau).
Definition gctxt    := (G.ctxt    EVar Tau).

Notation "x '~g' a" := (G.ctxt x a gdot)
  (at level 27, left associativity).
Notation "E '&g' F" := (G.concat E F)
  (at level 28, left associativity).



(* TODO Oy, he's right oriented. *)
Inductive WFD : Delta -> Prop :=
  | WFD_nil    : WFD D.empty
  | WFD_xtau   : forall (d : Delta) (alpha : TVar) (k : Kappa),
                 D.map d alpha = None ->
                 WFD d ->
                 WFD (D.concat d  (D.ctxt alpha k ddot)).

Inductive K : Delta -> Tau -> Kappa -> Prop :=
 | K_B     : forall (d : Delta) (alpha : TVar),
               D.map d alpha = Some B ->
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
                 (forall alpha, 
                    (TVSM.mem alpha L') = false -> 
                   WFD (D.concat d (D.ctxt alpha k ddot)) ->
                   D.map d alpha = None ->
                   K (D.concat d (D.ctxt alpha k ddot))
                     (T.open_rec_tau 0 (ftvar alpha) tau) A) ->
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
    K (D.concat d (D.concat (D.ctxt alpha B ddot) e)) tau B ->
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
    K (D.concat d (D.concat (D.ctxt alpha B ddot) e)) tau B ->
    K d tau A.
Proof.
  intros.
  set (G := (D.concat d (D.concat (D.ctxt alpha B ddot) e))) in *. 
  assert (G = (D.concat d (D.concat (D.ctxt alpha B ddot) e))).
  reflexivity.
  clearbody G.
  revert H0.
  generalize dependent e.
  induction H; intros; subst.
  admit. (* Connected. *)
  admit. (* Connected. *)
  admit. (* Connected! *)
  admit.
Qed.

(* Okay try a real lemma! *)
(* Will this form work or do I need d & alpha ~ k & d' ? *)

(* Introduced too early so not recursing terms for type variables. *)
(* 
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

*)
(* This might be good also! *)

Lemma K_strengthening_add_right:
  forall (d : Delta) (tau : Tau) (k : Kappa),
      WFD d ->
      K d tau k -> 
      forall (alpha : TVar) (k' : Kappa),
        WFD (d &d alpha ~d k') ->
        K (d &d (alpha ~d k')) tau k.
Proof.
  intros d tau k WFDder Kder.
  induction Kder; intros.
  inversion H0.
  (* What's his tactic ? *)
  admit.
  constructor.
  (* invert H1 to get d = d0 and alpha1 = alpha0 and k = k'. *)
  (* then alpha is in d from H and so H0 is false. *)
  admit.
  constructor.

  apply IHKder; try assumption.

  apply K_arrow.
  apply IHKder1; try assumption.
  apply IHKder2; try assumption.

  (* 
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
*)
Admitted.

(* This looks great! *)
Lemma K_strengthening_concat:
  forall (d : Delta) (tau : Tau) (k : Kappa),
      WFD d ->
      K d tau k -> 
      forall (d' : Delta),
        WFD (d &d d')  ->
        K (d &d d') tau k.
Proof.
  intros d tau k WFDder Kder.
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

(*
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
*)
Admitted.

Lemma K_strengthening_extends:
  forall (d : Delta) (tau : Tau) (k : Kappa),
      WFD d ->
      K d tau k -> 
      forall (d' : Delta),
        WFD d' ->
        D.extends d d' = true -> 
        K d' tau k.
Proof.
  intros d tau k WFDder Kder.
  induction Kder; intros.
  constructor.
  admit. (* get extends agreement *)
  
  constructor.
  apply IHKder; try assumption.

  apply K_arrow; try assumption.
  apply IHKder1; try assumption.
  apply IHKder2; try assumption.

(*
  apply_tfresh K_utype as y.  
  intros.
  apply H0; try assumption.
  auto.
  admit. (* WFD str *)
  admit. (* Y fresh. *)
  admit. (* Y fresh. *)
  admit. (* extends extension agreement. *)
*)
Admitted.

(* Good! *)
Lemma K_strengthening_add_right_B:
  forall (d : Delta) (tau : Tau),
      WFD d ->
      K d tau B -> 
      forall (alpha : TVar) (k' : Kappa),
        WFD (d &d alpha ~d k') ->
        K (d &d alpha ~d k') tau B.
Proof.
  intros d tau WFDder Kder.
  induction Kder; intros.
  admit. 
  admit.
  admit.
  admit.
Admitted.

Lemma K_strengthening_add_middle:
  forall (d d' : Delta) (tau : Tau) (k : Kappa),
      WFD (d &d d') ->
      K d tau k -> 
      forall (alpha : TVar) (k' : Kappa),
        WFD (d &d alpha ~d k' &d d')  ->
        K (d &d alpha ~d k' &d d') tau k.
Proof.
  intros d d' tau k WFDder Kder.
  induction Kder; intros.
  admit.
  admit.
  admit.
  admit.
Admitted.
  
Module MiniTerm <: BoolEqualitySig.
Inductive St : Type :=                        
 | e_s       : E   -> St
 | letx      : E -> St   -> St        
with E : Type :=                              
 | bevar     : nat -> E
 | fevar     : EVar -> E
 | f_e       : F -> E
 | assign    : E -> E -> E
 | appl      : E -> E -> E
with F : Type :=
 | dfun      : Tau -> Tau -> St -> F.

Scheme St_ind_mutual := Induction for St Sort Prop
with    E_ind_mutual := Induction for E Sort Prop
with    F_ind_mutual := Induction for F Sort Prop.
Combined Scheme Term_ind_mutual from St_ind_mutual, E_ind_mutual, F_ind_mutual.

Function beq_st (s s' : St) : bool := 
  match s, s' with
    | (e_s e), (e_s e') => beq_e e e'
    | letx e s, letx e' s' =>
       andb (beq_e e e') (beq_st s s')
    | _, _ => false
  end
with beq_e (e e' : E) : bool := 
 match e, e' with 
 | f_e f, f_e f'                 => beq_f f f'
 | assign e1 e2, assign e1' e2'  => andb (beq_e e1 e1') (beq_e e2 e2')
 | appl e1 e2, appl e1' e2'      => andb (beq_e e1 e1') (beq_e e2 e2')
 | _, _ => false
end
with beq_f (f f' : F) : bool :=
 match  f, f' with 
 | dfun t0 t1 s, dfun t0' t1' s' => 
   (andb (eqbau t0 t0') 
         (andb (eqbau t1 t1') (beq_st s s')))
end.
Hint Unfold beq_st.
Hint Resolve beq_st.
Hint Unfold beq_e.
Hint Resolve beq_e.
Hint Unfold beq_f.
Hint Resolve beq_f.
Lemma beq_e_refl:
  forall e, beq_e e e = true.
Proof.
Admitted.
Hint Resolve beq_e_refl.
Lemma beq_e_sym:
  forall e e', beq_e e e' = beq_e e' e.
Proof.
Admitted.
Lemma beq_e_neq:
  forall e e', beq_e e e' = false -> e <> e'.
Proof.
Admitted.
Hint Resolve beq_e_neq.

Lemma beq_e_trans:
  forall e e0 e1, 
    beq_e e e0 = true ->
    beq_e e0 e1 = true ->
    beq_e e e1 = true.
Proof.
Admitted.
Hint Resolve beq_e_trans.

Lemma beq_e_iff_neq:   forall a b, beq_e a b = false <-> a <> b.
Proof.
Admitted.
Hint Resolve beq_e_iff_neq.

Lemma beq_e_iff_eq:    forall a b, beq_e a b = true <-> a = b.
Proof.
Admitted.
Lemma beq_e_eq:
  forall e e', beq_e e e' = true -> e = e'.
Proof.
Admitted.

Definition T := E.
Definition beq_t := beq_e.
Definition beq_t_refl := beq_e_refl.
Definition beq_t_sym := beq_e_sym.
Definition beq_t_trans := beq_e_trans.
Definition beq_t_eq := beq_e_eq.
Definition beq_t_neq := beq_e_neq.
Definition beq_t_iff_eq := beq_e_iff_eq.
Definition beq_t_iff_neq := beq_e_iff_neq.
End MiniTerm.
Include MiniTerm.

Inductive  term : Type := 
  | term_st : St -> term 
  | term_e :  E -> term 
  | term_f :  F -> term.

Module H := ContextFun E MiniTerm.
Definition Heap     := (H.Context EVar E).
Definition hdot     := (H.cdot    EVar E).
Definition hctxt    := (H.ctxt    EVar E).

Notation "x '~h' a" := (H.ctxt x a hdot)
  (at level 27, left associativity).
Notation "E '&h' F" := (H.concat E F) 
  (at level 28, left associativity).

Fixpoint open_rec_st  (k : nat) (u : E) (s : St)  {struct s}  : St :=
 match s with 
    | e_s  e      => e_s  (open_rec_e  k u e)
    | letx e s1   => letx (open_rec_e (S k) u e) (open_rec_st (S k) u s1)
  end 
with open_rec_e   (k : nat) (u : E) (e : E) {struct e}  : E :=
  match e with 
    | bevar i      => if (beq_nat k i) then u else (bevar i)
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
                  (forall x, EVSM.mem x L' = false -> lc_st (open_rec_st 0 (fevar x) s1 )) ->
                  lc_st (letx e s1)
with      lc_e : E -> Prop :=
 | lc_e_fevar : forall x, lc_e (fevar x)
 | lc_f_e     : forall f, lc_f f -> lc_e (f_e f)
 | lc_assign  : forall e1 e2, lc_e e1 -> lc_e e2 -> lc_e (appl e1 e2) 
 | lc_appl    : forall e1 e2, lc_e e1 -> lc_e e2 -> lc_e (appl e1 e2)
with      lc_f : F -> Prop :=
 | lc_dfun : forall t1 t2 s L',
               (forall x, EVSM.mem x L' = false -> lc_st (open_rec_st 0 (fevar x) s)) ->
               lc_f (dfun t1 t2 s).

Inductive lc_term : term -> Prop := 
  | lc_term_st : forall s, lc_st s -> lc_term (term_st s)
  | lc_term_e  : forall e, lc_e  e -> lc_term (term_e  e)
  | lc_term_f  : forall f, lc_f  f -> lc_term (term_f  f).

(* Restrict value. *)

(* Do I need value on Terms instead of E? *)
Inductive Value : E -> Prop :=
 | DfunIsAValue : forall (t1 t2 : Tau) (s : St), Value (f_e (dfun t1 t2 s)).

(* Define free variables. *)

Fixpoint fv_st (t : St) {struct t} : EVars :=
  match t with
    | e_s  e    => fv_e e
    | letx e s  => EVSM.union (fv_e e) (fv_st s)
  end
with  fv_e (e : E) {struct e} : EVars := 
  match e with 
    | bevar i      => EVSM.empty 
    | fevar x      => EVSM.singleton x
    | f_e f        => fv_f f
    | assign e1 e2 => EVSM.union (fv_e e1) (fv_e e2)
    | appl e1 e2   => EVSM.union (fv_e e1) (fv_e e2)
  end
with  fv_f (f : F) {struct f} : EVars := 
  match f with
  | dfun t1 t2 s => (fv_st s)
end.

Fixpoint fv_term (t : term) {struct t} : EVars :=
  match t with 
    | term_st s    => fv_st s
    | term_e  e    => fv_e e
    | term_f  f    => fv_f f 
 end.

(* Define subst. *)

Fixpoint subst_st (z : EVar) (u : E) (s : St) {struct s} : St := 
 match s with 
   | e_s  e      => e_s  (subst_e z u e)
   | letx e s    => letx (subst_e z u e) (subst_st z u s)
 end
with subst_e  (z : EVar) (u : E) (e : E) {struct e} : E :=
 match e with
   | bevar i       => bevar i
   | fevar x       => if (E.eqb x z) then u else (fevar x)
   | f_e f         => f_e (subst_f z u f)
   | assign e1 e2  => assign (subst_e z u e1) (subst_e z u e2)
   | appl   e1 e2  => appl (subst_e z u e1) (subst_e z u e2)
 end
with subst_f  (z : EVar) (u : E) (f : F) {struct f} : F :=
 match f with 
   | dfun t1 t2 s => dfun t1 t2 (subst_st z u s)
end.

Fixpoint subst_term (z : EVar) (u : E) (t : term) {struct t} : term :=
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
 | S_let_3_1 : forall (x : EVar) (v : E) (h : Heap) (s: St),
                 Value v ->
                 S h (letx v s) (x ~h v &h h) (s ^ x)

 | S_let_3_1' : forall (x : EVar) (v v' : E) (h : Heap) (s: St),
                 Value v ->
                 H.map h x = Some v' ->
  (* not overwriting, taking the first binding. *)
                 S h (letx v s) (H.ctxt x v h) (s ^ x)   

| S_exp_3_9_1: forall (h h' : Heap) (e e' : E),
                   R h (e_s e) h' (e_s e') ->
                   S h (e_s e) h' (e_s e')

 | S_letx_3_9_4: forall (h h' : Heap) (e e' : E) (s : St) (x : EVar),
                   R h (e_s e) h' (e_s e') ->
                   S h (letx e s) h' (letx e' s)

with R : Heap -> St -> Heap -> St -> Prop :=
 | R_get_3_1 : forall (h  : Heap) (x : EVar) (v v' : E),
                    H.map h x = Some v' ->
                    Value v' ->
                    R h (e_s (fevar x)) h (e_s v)

 | R_assign_3_2:
     forall (h' h : Heap) (v : E) (x : EVar),
       H.map h x = Some v ->
       Value v   ->
(* not overwriting, taking the first binding. *)
       R h (e_s (assign (fevar x) v))
         (H.ctxt x v h) (e_s v)

 | R_initial_assign_3_2:
     forall (h' h : Heap) (v : E) (x : EVar),
       H.map h x = None ->
       Value v   ->
       R h  (e_s (assign (fevar x) v))
         (H.ctxt x v h) (e_s v)


 | R_appl_3_5:   forall (h : Heap) (x : EVar) (tau tau' : Tau) (v : E) (s : St),
                    Value v ->
                    R h (e_s (appl (f_e (dfun tau tau' s)) v))
                      h (letx v s)

 | R_assign_3_9_2: forall (h h' : Heap) (e e' e2: E),
                   L h (e_s e)             h' (e_s e') ->
                   R h (e_s (assign e e2)) h' (e_s (assign e' e2))

 | R_assign_3_10_3: forall (h h' : Heap) (e e' : E) (x : EVar),
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
                         (forall x, EVSM.mem x L' = false -> 
                          styp (G &g x ~g tau') tau (s ^ x)) ->
                          rtyp G e    tau' ->
                          styp G tau  (letx e s)

with      ltyp :   Gamma -> E -> Tau -> Prop := 

  | SL_3_1     : forall (G : Gamma) (x : EVar) (tau: Tau),
                      G.map G x = Some tau ->
                      ltyp G (fevar x) tau

with      rtyp :  Gamma -> E   -> Tau -> Prop := 
  | SR_3_1  : forall (G : Gamma) (x  : EVar) (tau: Tau),
                G.map G x = Some tau ->
                rtyp G (fevar x) tau

  | SR_3_9  : forall (G : Gamma) (e1 e2 : E) (tau tau' : Tau),
                   rtyp G e1 (arrow tau' tau) ->
                   rtyp G e2 tau' ->
                   rtyp G (appl e1 e2) tau

  | SR_3_13 : forall L' (G : Gamma) (tau tau': Tau) (s : St) (x : EVar),
                   G.map G x = None ->
                   (forall x, EVSM.mem x L' = false -> 
                      styp (G &g x ~g tau) tau' (s ^ x)) -> 
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

Definition body t :=
  exists L', forall x, EVSM.mem x L' = false -> lc_st (t ^ x).

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
   (A &g C) |s= s ~: tau ->
   G.nodup (A &g B &g C) = true ->
   (A &g B &g C) |s= s ~: tau.
Proof.
  (* broken, had to reorder and such. *)
  intros a b c tau s Typ. 
  set (G := (a &g c)).
  assert (G = (a &g c)).
  reflexivity.
  revert H.
  clearbody G.
  intros.
  rewrite <- H in Typ.
  generalize dependent c.
  induction Typ; intros; subst.
  
  apply styp_e_3_1 with (tau := tau). (* need the mutual induction. *)
  admit. (* rtyp weakening *)

(*
  apply styp_let_3_6  with (L':= L') (tau':= tau'); try assumption.
  intros.
  specialize (H0 x H2 (g &g x ~g tau')).
  rewrite concat_assoc.
  rewrite <- concat_assoc.
  apply H0.
  rewrite concat_assoc.
  eauto.
  eauto.
*)
Admitted.

Ltac gather_vars_with F :=
  let rec gather V :=
    match goal with
    | H: ?S |- _ =>
      let FH := constr:(F H) in
      match V with
      | \{}_e => gather FH
      | context [FH] => fail 1
      | _ => gather (FH \u_e V)
      end
    | _ => V
    end in
  let L := gather (\{}_e: EVars) in eval simpl in L.

Ltac gather_vars_e :=
  let A :=  gather_vars_with (fun x : EVars => x) in
  let B :=  gather_vars_with (fun x : EVar => \{x}_e) in
  (* let C :=  gather_vars_with (fun x : Delta => dom x) in *)
  let D :=  gather_vars_with (fun x : term => (fv_term x)) in
  let E' := gather_vars_with (fun x : St => (fv_st x)) in
  let F' := gather_vars_with (fun x : E => (fv_e x)) in
  let G :=  gather_vars_with (fun x : F => fv_f x) in
  constr:(A \u_e B (* \u_e C *) \u_e D \u_e E' \u_e F' \u_e G).

Ltac beautify_fset_e V :=
  let rec go Acc E' :=
     match E' with
     | ?E1 \u_e ?E2 => let Acc1 := go Acc E1 in
                     go Acc1 E2
     | \{}_e  => Acc
     | ?E1 => match Acc with
              | \{}_e => E1
              | _ => constr:(Acc \u_e E1)
              end
     end
  in go (\{}_e: EVars) V.

Ltac apply_fresh_e lemma gather :=
  let L0 := gather_vars_e in let L := beautify_fset_e L0 in
  first [apply (@lemma L) | eapply (@lemma L)].

(* Okay this is going to work. *)
Lemma styp_weaken_mutual: 
  forall (A B C : Gamma) (tau : Tau) (s : St),
   (A &g C) |s= s ~: tau ->
   G.nodup (A &g B &g C) = true ->
   (A &g B &g C) |s= s ~: tau.
Proof.
  intros A B C tau s Typ. 
  set (G := (A &g C)).
  assert (G = (A &g C)).
  reflexivity.
  revert H.
  clearbody G.
  intros.
  rewrite <- H in Typ.
  generalize dependent C.
  apply (styp_ind_mutual 
           (fun (G : Gamma) (tau0 : Tau) (s0 : St)
                (Z : G |s= s0 ~: tau0)  =>
              forall C : Gamma, 
                G = A &g C ->
                G.nodup (A &g B &g C) = true -> 
                A &g B &g C |s= s0 ~: tau0)
           (fun (G : Gamma) (e0 : E) (tau0 : Tau) 
                (Z : G |l= e0 ~: tau0)  =>
              forall C : Gamma, 
                G = A &g C ->
                G.nodup (A &g B &g C) = true -> 
                A &g B &g C |l= e0 ~: tau0)
           (fun (G : Gamma) (e0 : E) (tau0 : Tau)
                (Z : G|r= e0 ~: tau0)  =>
              forall C : Gamma, 
                G = A &g C ->
                G.nodup (A &g B &g C) = true -> 
                A &g B &g C |r= e0 ~: tau0)); try assumption.
  intros.
  constructor.
  apply H in H0; try assumption.

  (* Binding case 1 let works. *)
  intros.
  subst.
  specialize (styp_let_3_6 \{}_e).
  apply_fresh_e styp_let_3_6 gather_vars.
  intros.

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


