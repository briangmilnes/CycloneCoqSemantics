(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  The typing module.

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.
Require Import Coq.Init.Logic.
Require Import Coq.Bool.Bool.
Require Import Coq.Structures.Equalities.

Require Export BooleanEqualityDef.
Require Export TVarModuleDef.
Require Export KappaModuleDef.
Require Export PhiModuleDef.
Require Export CpdtTactics.
Require Export Case.
Require Export MoreTacticals.

Module TauModule <: BooleanEquality.

Module Types.
 Module K := KappaModule.
 Include K.Types.
 Module P := PhiModule.
 Include P.Types.
 Module TVS  := TVarModuleSet.
 Module TV  := TVarModuleSet.BE.
 Definition TVar := TVS.elt.
 Definition TVars := TVS.t.

Inductive Tau : Type :=
 | btvar  : nat -> Tau                               (* A bound type variable, a de Bruijn index. *)
 | ftvar  : TVar -> Tau                              (* A free type variable. *)
 | cint   : Tau                                      (* Cyclone's Integers. *)
 | cross  : Tau -> Tau -> Tau                        (* Pairs. *)
 | arrow  : Tau -> Tau -> Tau                        (* Function    type. *)
 | ptype  : Tau -> Tau                               (* Pointer     type. *)
 | utype  : Kappa -> Tau -> Tau                    (* Universal   type. *)
 | etype  : Phi -> Kappa -> Tau -> Tau.          (* Existential type. *)
 
Fixpoint fv_tau (tau : Tau) {struct tau} : TVS.t :=
  match tau with
    | btvar i     => TVS.empty
    | ftvar x     => TVS.singleton x
    | cint        => TVS.empty
    | cross t0 t1 => TVS.union (fv_tau t0) (fv_tau t1)
    | arrow t0 t1 => TVS.union (fv_tau t0) (fv_tau t1)
    | ptype t0    => (fv_tau t0)
    | utype k t0   => (fv_tau t0)
    | etype _ _ t0   => (fv_tau t0)
end.

Fixpoint open_rec_tau  (k : nat) (tau' : Tau) (tau : Tau)  {struct tau}  : Tau :=
 match tau with 
   | btvar i       => if (beq_nat k i) then tau' else (btvar i)
   | ftvar i       => ftvar i
   | cint          => cint
   | cross t0 t1   => cross (open_rec_tau k tau' t0) (open_rec_tau k tau' t1)
   | arrow t0 t1   => arrow (open_rec_tau k tau' t0) (open_rec_tau k tau' t1)
   | ptype  t0     => ptype (open_rec_tau k tau' t0)
   | utype kp t0   => utype kp (open_rec_tau (S k) tau' t0)
   | etype p kp t0 => etype p kp (open_rec_tau (S k) tau' t0)
  end.

Inductive lc_tau : Tau -> Prop := 
 | lc_tau_ftvar : forall x, lc_tau (ftvar x)
 | lc_tau_cint  : lc_tau cint
 | lc_tau_cross : forall t0 t1, lc_tau t0 -> lc_tau t1 -> lc_tau (cross t0 t1)
 | lc_tau_arrow : forall t0 t1, lc_tau t0 -> lc_tau t1 -> lc_tau (arrow t0 t1)
 | lc_tau_ptype : forall t0, lc_tau t0 -> lc_tau (ptype t0)
 | lc_tau_utype : forall L' k t0,
                  (forall alpha, (TVS.mem alpha L') = false
                                 -> lc_tau (open_rec_tau 0 (ftvar alpha) t0)) ->
                  lc_tau (utype k t0)
 | lc_tau_etype : forall L' p k t0,
                  (forall alpha, (TVS.mem alpha L') = false
                                 -> lc_tau (open_rec_tau 0 (ftvar alpha) t0)) ->
                  lc_tau (etype p k t0).

Fixpoint subst_Tau  (t : Tau) (tau : Tau) (alpha : TVar) {struct t} : Tau := 
  match t with 
    | btvar i      => btvar i
    | ftvar beta   => if (TVS.BE.eqb alpha beta) then tau else (ftvar beta)
    | cint         => cint
    | cross t0 t1  => cross (subst_Tau t0 tau alpha) (subst_Tau t1 tau alpha)
    | arrow t0 t1  => arrow (subst_Tau t0 tau alpha) (subst_Tau t1 tau alpha)
    | ptype t0     => ptype (subst_Tau t0 tau alpha)
    | utype k t0   => utype k (subst_Tau t0 tau alpha)
    | etype p k t0 => etype p k (subst_Tau t0 tau alpha)
end.

End Types.
Include Types.

Function eqb (t t' : Tau) : bool :=
 match t, t' with
 | btvar i, btvar j => beq_nat i j
 | ftvar alpha, ftvar beta => TVS.eqb alpha beta
 | cint, cint => true
 | (cross t0 t1), (cross t0' t1') => andb (eqb t0 t0') (eqb t1 t1')
 | (arrow t0 t1), (arrow t0' t1') => andb (eqb t0 t0') (eqb t1 t1')
 | ptype t, ptype t' => (eqb t t')
 | utype kappa tau, utype kappa' tau' =>
   andb (K.eqb kappa kappa') (eqb tau tau')
 | etype p kappa tau, etype p' kappa' tau' =>
   andb (andb (P.eqb p p')  (K.eqb kappa kappa'))
        (eqb tau tau')
 | _ , _ => false
end.
Hint Unfold eqb.
Hint Resolve eqb.

Fixpoint eq (a b : Tau) : Prop :=
    match eqb a b with
     | false => False
     | true => True
    end.
Hint Unfold eq.

Ltac destruct_away := 
  repeat match goal with
    | [ |- ?X = true ] => destruct X; try solve[inversion H]; try reflexivity
         end.

Lemma eqb_eq : forall x y : Tau, eqb x y = true <-> eq x y.
Proof.
  induction x; induction y;  unfold iff; split; intros;
  try solve[unfold eq;
             rewrite H;
             reflexivity];
  unfold eq in H;
  repeat match goal with
    | [ |- ?X = true ] => destruct X; try solve[inversion H]; try reflexivity
  end.
Qed.

Lemma eqb_to_eq:
  forall t0 t1, eqb t0 t1 = true -> t0 = t1.
Proof.
  induction t0; induction t1; intros; try solve [inversion H]; try reflexivity.

  unfold eqb in H.
  symmetry in H.
  apply beq_nat_eq in H.
  subst.
  reflexivity.

  unfold eqb in H.
  apply TVS.eqb_to_eq in H.
  subst.
  reflexivity.

  unfold eqb in H.
  fold eqb in H.
  apply andb_true_iff in H.
  inversion H.
  apply IHt0_1 in H0.
  apply IHt0_2 in H1.
  subst.
  reflexivity.

  unfold eqb in H.
  fold eqb in H.
  apply andb_true_iff in H.
  inversion H.
  apply IHt0_1 in H0.
  apply IHt0_2 in H1.
  subst.
  reflexivity.

  unfold eqb in H.
  fold eqb in H.
  apply IHt0 in H.
  rewrite H.
  reflexivity.

  unfold eqb in H.
  fold eqb in H.
  apply andb_true_iff in H.
  inversion H.
  apply IHt0 in H1.
  apply K.eqb_to_eq in H0.
  subst.
  reflexivity.

  unfold eqb in H.
  fold eqb in H.
  apply andb_true_iff in H.
  inversion H.
  apply andb_true_iff in H0.
  inversion H0.
  apply IHt0 in H1.
  apply P.eqb_to_eq in H2.
  apply K.eqb_to_eq in H3.
  subst.
  reflexivity.
Qed.
Hint Resolve eqb_eq.

Lemma eqb_refl:
 forall (t : Tau),
   eqb t t = true.
Proof.
  intros.
  induction t; crush.
  symmetry.
  apply beq_nat_refl.
Qed.
Hint Resolve eqb_refl.

Lemma eq_refl:
 forall (a : Tau),
   eq a a.
Proof.
  intros.
  apply eqb_eq.
  apply eqb_refl.
Qed.

Ltac apply_beq_eqs := 
  repeat match goal with
    | [ I : eqb _ _ = true 
        |- _ ] => apply eqb_to_eq in I; subst; try reflexivity; try assumption
    | [ I : P.eqb _ _ = true 
        |- _ ] => apply P.eqb_to_eq in I; subst; try reflexivity; try assumption
    | [ I : K.eqb _ _ = true 
        |- _ ] => apply K.eqb_to_eq in I; subst; try reflexivity; try assumption
    | [ I : TVS.eqb _ _ = true 
        |- _ ] => apply TVS.eqb_to_eq in I; subst; try reflexivity; try assumption
end.

Lemma eqb_iff_eq:    forall a b, eqb a b = true <-> a = b.
Proof.
  induction a; induction b;
  unfold iff;
  split; 
  intros;
  try reflexivity;
  try solve [inversion H];
  try solve [inversion H;
             subst;
             apply eqb_refl;
             reflexivity];
  apply_beq_eqs.
Qed.
Hint Resolve eqb_iff_eq.

Ltac apply_eqs_sym := 
  repeat match goal with
    | [ |- beq_nat ?n ?n' = beq_nat ?n' ?n ] => 
      apply beq_nat_sym
    | [ |- TVS.eqb ?n ?n' = TVS.eqb ?n' ?n ] => 
      apply TVS.eqb_sym
end.

Lemma eqb_sym : forall x y, eqb x y = eqb y x.
Proof.
  induction x; induction y; auto;
  try solve[
        unfold eqb;
        fold eqb;
        apply_eqs_sym];
  try solve[refold eqb;
             apply IHx];
  try solve[refold eqb;
             congruence];
  try solve[
        refold eqb;
        try rewrite K.eqb_sym;
        try rewrite P.eqb_sym;
        try rewrite IHx;
        congruence].
Qed.
Hint Immediate eqb_sym.

Lemma eq_sym : forall x y : Tau, eq x y -> eq y x.
Proof.
  intros.
  apply eqb_eq.
  apply eqb_eq in H.
  rewrite eqb_sym.
  assumption.
Qed.

Lemma eqb_to_neq:
  forall t0 t1, eqb t0 t1 = false -> t0 <> t1.
Proof.
  induction t0; induction t1; intros; try solve [inversion H]; try solve [discriminate];
  try solve[refold_in eqb H;
            try apply beq_nat_false_iff in H;
            try apply TVS.eqb_to_neq in H;
            congruence];
  try solve[inversion H;
             try apply andb_false_iff in H1;
             try apply IHt0 in H;
             inversion H1;
             try apply IHt0_1 in H0;
             try apply IHt0_2 in H0;
             congruence];
  try solve[refold_in eqb H;
             simplify_boolean_and_false;
             try apply K.eqb_to_neq in H0;
             try apply P.eqb_to_neq in H0;
             try apply IHt0 in H0;
             try apply K.eqb_to_neq in H;
             try apply P.eqb_to_neq in H;
             try apply IHt0 in H0;
             congruence].
Qed.  
Hint Resolve eqb_to_neq.

Ltac fold_n_neq :=
  repeat match goal with
    | [ I : eqb ?x ?y = false |- ?x <> ?y  ] => 
      fold eqb in I; unfold eqb in I; simplify_boolean_and_false
    | [ I : eqb ?x _ = false,
        IH: forall _, eqb ?x _ = false <-> ?x <> _
       |- _ <> _  ] => 
       apply IH in I; congruence
    | [ H : TVS.eqb _ _ = false |- _ ] =>
      apply TVS.eqb_to_neq in H; try congruence
    | [ H : K.eqb _ _ = false |- _ ] =>
      apply K.eqb_to_neq in H; try congruence
    | [ H : P.eqb _ _ = false |- _ ] =>
      apply P.eqb_to_neq in H; try congruence
end.

Lemma eqb_iff_neq:   forall a b, eqb a b = false <-> a <> b.
Proof.
  induction a; induction b; try split; try intros;
  try solve[congruence];
  try solve[simpl; reflexivity];  try solve[simpl in H; inversion H];
  try solve [unfold eqb in H;
             fold eqb in H;
             simplify_boolean_and_false;
             try apply eqb_to_neq in H;
             try apply eqb_to_neq in H0;
             congruence];
  try solve[unfold eqb in H;
            fold eqb in H;
            simplify_boolean_and_false;
            fold_n_neq;
            congruence].
Admitted.
Hint Resolve eqb_iff_neq.

Lemma eqb_trans: 
  forall x y z, 
    eqb x y = true -> eqb y z = true -> eqb x z = true.
Proof.
  intros.
  pose proof H as H'.
  pose proof H0 as H0'.
  apply eqb_to_eq in H.
  apply eqb_to_eq in H0.
  subst.
  assumption.
Qed.
Hint Resolve eqb_trans.

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

Definition t:= Tau.

End TauModule.
