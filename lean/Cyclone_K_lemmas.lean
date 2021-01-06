/-
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

   Some K Lemmas.
-/
/- These are missing utype and etype. -/

import .Cyclone_Static_Semantics_Kinding_And_Context_Well_Formedness

lemma K_weakening (t : Tau) (d : Delta) :
 K d t A →
 WFD d →
 ∀ (d' : Delta),
  extendedby d d' →
  K d' t A :=
begin
 intros kdta wfdd d extdd',
 induction kdta,
/- This would be nicer if I had disjunctive cases.
 try {solve1{constructor}};
 try {constructor,
      apply binds_extendedby,
      repeat {assumption}, };
 try {constructor,
     apply kdta_ih_a,
     repeat {assumption,},
     apply kdta_ih_a_1,
     repeat {assumption,},};
 try {constructor,
     apply kdta_ih,
     repeat{ assumption, },},
-/
 case K.cint {
   constructor,
 },
 case K.B { 
   constructor,
   apply binds_extendedby; assumption,
},
 case K.star_A {
   constructor,
   apply binds_extendedby; assumption},
 case K.cross {
    constructor,
    apply kdta_ih_a; assumption,
    apply kdta_ih_a_1; assumption, 
 },
 case K.arrow {
    constructor,
    apply kdta_ih_a; assumption,
    apply kdta_ih_a_1; assumption,
 },
 case K.ptype    { 
   constructor,
   apply kdta_ih; assumption,
},
 case K.B_A {
  constructor,
  apply kdta_ih; assumption,
},
end

lemma K_weakening_var (d : Delta) (t : Tau) (k : Kappa) :
 ok d →
 K d t k →
 ∀ (v : Var) (k' : Kappa),
   ok ((v,k') :: d) →
   K  ((v,k') :: d) t k :=
begin
  intros okd kdtk,
  induction' kdtk; 
  intros v k' okvk';
  try {solve1 {constructor} };
  try {
   constructor,
   apply binds_weakening; 
   assumption};
  try{
   constructor;
   try {apply ih; assumption},
   try {apply ih_kdtk; assumption},
   try {apply ih_kdtk_1; assumption},
 },
end

/- WTF? it's not putting the A of A -> false in the context. -/
lemma bug :
   ¬ false :=
begin
   intros v,
   assumption,
end

lemma K_empty_var (v : Var) (k : Kappa) :
   ¬ K [] (ftvar v) k :=
begin
  intros k,
  cases k; cases k_a,
  apply binds_nil_not_some v B; assumption,
end

/-

lemma open_var_fv_eq : ∀ t n x,
    T.fv (T.open_rec n (ftvar x) t) = (T.fv t \u \{x}) \/
    T.fv (T.open_rec n (ftvar x) t) = (T.fv t).
Proof.
  intros t.
  induction t; intros; simpl; try case_nat; auto with fset;
  try solve[
        simpl;
        left;
        rewrite union_empty_l;
        auto with fset].
(* Bug ugly won't ltac. *)

  specialize(IHt1 n x);
  specialize(IHt2 n x);
  inversion IHt1; inversion IHt2;
  rewrite H; rewrite H0.
  left.
  rewrite <- union_assoc.
  rewrite <- union_assoc.
  rewrite* union_middle_shuffle.
  left.
  rewrite <- union_assoc.
  rewrite <- union_assoc.
  rewrite* union_middle_r.
  left.
  rewrite* <- union_assoc.  
  right*.

  specialize(IHt1 n x);
  specialize(IHt2 n x);
  inversion IHt1; inversion IHt2;
  rewrite H; rewrite H0.
  left.
  rewrite <- union_assoc.
  rewrite <- union_assoc.
  rewrite* union_middle_shuffle.
  left.
  rewrite <- union_assoc.
  rewrite <- union_assoc.
  rewrite* union_middle_r.
  left.
  rewrite* <- union_assoc.  
  right*.  
Qed.  

lemma fv_var:
  ∀ A alpha tau (d : env A), 
    alpha \notin T.fv tau →
    T.fv tau \c \{ alpha} \u dom d →
    T.fv tau \c dom d.
Proof.
  intros.
  induction tau; simpl; simpl in H; simpl in H0; auto with fset.
  assert(alpha <> v); auto.
  lets: subset_remove_r (fset Tau).
  apply subset_remove_r with (b:= alpha); auto.
  assert(alpha \notin T.fv tau1); auto.
  assert(alpha \notin T.fv tau2); auto.
  specialize (IHtau1 H1).
  specialize (IHtau2 H2).
  assert(H3 : (T.fv tau1 \u T.fv tau2 \c \{ alpha} \u dom d)); auto.
  apply subset_remove_l_r in H0.  
  apply subset_remove_l_l in H3.
  auto with fset.

  assert(H3 : (T.fv tau1 \u T.fv tau2 \c \{ alpha} \u dom d)); auto.
  apply subset_remove_l_r in H0.  
  apply subset_remove_l_l in H3.
  auto with fset.  
Qed.  

lemma fv_var_2:
  ∀ A alpha tau (d : env A), 
    alpha \notin T.fv tau →
    T.fv tau \u \{ alpha} \c \{ alpha} \u dom d →
    T.fv tau \c dom d.
Proof.
  intros.
  apply subset_remove_l_r in H0.
  apply fv_var with (alpha:= alpha); auto.
Qed.

lemma K_fv:
  ∀ tau d k,
    WFD d →
    K d tau k →
    T.fv tau \c fv_delta d.
Proof.
(* BUG ugly, repetition, will not ltac *)
  introv WFDd Kd.
  induction Kd; assert(ok d); auto; try solve[simpl; auto with fset].

  pick_fresh alpha.
  assert(NI: alpha \notin L); auto.
  assert(OKda: ok(d & alpha ~ k)); auto.
  assert(WFDda: WFD(d & alpha ~k)); auto.
  specialize (H0 alpha NI OKda WFDda).
  lets: open_var_fv_eq tau 0 alpha.
  inversion H2.
  rewrite H3 in H0.
  unfold fv_delta.
  unfold fv_delta in H0.
  rewrite dom_push in H0.
  apply fv_var_2 with (alpha:=alpha); auto.
  rewrite H3 in H0.
  unfold fv_delta in H0.
  unfold fv_delta.
  apply fv_var with (alpha:= alpha); auto.
  unfold fv_delta in H0.
  unfold fv_delta.
  rewrite dom_push in H0.
  auto.  

  pick_fresh alpha.
  assert(NI: alpha \notin L); auto.
  assert(OKda: ok(d & alpha ~ k)); auto.
  assert(WFDda: WFD(d & alpha ~k)); auto.
  specialize (H0 alpha NI OKda WFDda).
  lets: open_var_fv_eq tau 0 alpha.
  inversion H2.
  rewrite H3 in H0.
  unfold fv_delta.
  unfold fv_delta in H0.
  rewrite dom_push in H0.
  apply fv_var_2 with (alpha:=alpha); auto.
  rewrite H3 in H0.
  unfold fv_delta in H0.
  unfold fv_delta.
  apply fv_var with (alpha:= alpha); auto.
  unfold fv_delta in H0.
  unfold fv_delta.
  rewrite dom_push in H0.
  auto.  
Qed.

lemma K_empty_closed:
  ∀ tau k,
    K empty tau k →
    T.fv tau = \{}.
Proof.
  intros.
  lets: K_fv tau (@empty Kappa).
  apply H0 in H.
  unfold fv_delta in H.
  rewrite dom_empty in H.
  apply contained_in_empty in H; auto.
  auto.
Qed.

lemma K__lc:
  ∀ d t k,
    ok d →
    K d t k →
    T.lc t.
Proof.
  introv okd Kd.
  induction Kd; auto.
  apply_fresh T.lc_utype.
  assert(NI: y \notin L); auto.
  apply_fresh T.lc_etype.
  assert(NI: y \notin L); auto.
Qed.

lemma AK_weakening_k:
  ∀ tau d k,
    AK d tau k →
    ∀ d',
      WFD d →
      extends d d' →
      AK d' tau k.
Proof.
  introv AKd.
  induction AKd; try solve[auto].
  intros.
  constructor.
  apply K_weakening_k with (d:=d); auto.
Qed.  

lemma AK_weakening_var:
  ∀ d t k,
    ok d →
    AK d t k →
    ∀ alpha k',
      ok (d & alpha ~ k') →
      AK (d & alpha ~ k') t k.
Proof.
  intros.
  apply AK_weakening_k with (d:= d); auto.
Qed.
-/
