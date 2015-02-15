(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  See if I can correctly hand craft the inductive hypothesis that I
 need. 

*)

Set Implicit Arguments.
Require Export LanguageModuleDef.

Require Export DynamicSemanticsTypeSubstitution.
Require Export DynamicSemanticsHeapObjects.
Require Export DynamicSemantics.
Require Export DynamicSemanticsTypeSubstitution.
Require Export StaticSemanticsKindingAndContextWellFormedness.
Require Export StaticSemantics.
Require Export TypeSafety.
Require Export CpdtTactics.
Require Export Case.
Require Export TacticNotations.
Require Export MoreTacticals.

Require Export AlphaConversion.

(* A mini K to work out context destructing induction. *)

Inductive K : Delta -> Tau -> Kappa -> Prop :=
 | K_int   : forall (d : Delta),
                  K d cint B

 | K_B     : forall (d : Delta) (alpha : TV.T),
               D.map d alpha = Some B ->
               K d (tv_t alpha) B

 | K_cross   : forall (d : Delta) (t0 t1 : Tau),
                    K d t0 A ->
                    K d t1 A ->
                    K d (cross t0 t1) A

 | K_utype  : forall (d : Delta) (alpha : TV.T) (k : Kappa) (tau : Tau),
                   D.map d alpha = None -> 
                   K  (dctxt alpha k d) tau A ->
                   K d (utype alpha k tau) A.

(* Put in the context destructuring dependent term and drop AK so I use
  the mini K. *)
Lemma A_6_Substitution_1:
  forall (d : Delta) (tau : Tau) (k : Kappa),
      D.nodup d = true ->
      K d tau k ->
      forall (alpha : TV.T) (k' : Kappa) (tau' : Tau), 
        D.nodup (dctxt alpha k d) = true ->
        K (dctxt alpha k d) tau' k' ->
        K d (subst_Tau tau' tau alpha) k'.
Proof.
  intros d tau k nodupd Kderd alpha k' tau' nodupd' Kderctxt.
  induction Kderctxt; intros.
  Case "K_int".
   assert (Z: d0 = (dctxt alpha k d)).
   admit.
   subst.
   (* K d (subst_Tau cint tau alpha) B *)

   simpl.
   apply K_int.
  Case "K_B".
   assert (Z: d0 = (dctxt alpha k d)).
   admit.
   subst.
   (* 
      D.map (dctxt alpha k d) alpha0 = Some B
      K d (subst_Tau (tv_t alpha0) tau alpha) B
   *)
   unfold dctxt in H.
   unfold D.map in H.
   fold D.map in H.
   case_eq(D.K_eq alpha0 alpha); intros; rewrite H0 in H; inversion H; subst.
   unfold D.K_eq in H0.
   apply D.K.beq_t_eq in H0.
   subst.
   simpl.
   rewrite TV.beq_t_refl.
   assumption.
   unfold subst_Tau.
   autounfold in H0.
   rewrite D.K.beq_t_sym in H0.
   rewrite H0.
   constructor; try assumption.
  Case "K_cross".
   assert (Z: d0 = (dctxt alpha k d)).
   admit.
   subst.
   (* IH D.nodup d0 = true -> K d (subst_Tau t0 tau alpha) A *)
   (* 
      K (dctxt alpha k d) t0 A -> 
      K d (subst_Tau (cross t0 t1) tau alpha) A 
    *)
   unfold subst_Tau.
   fold subst_Tau.
   pose proof nodupd' as nodupd''.
   apply IHKderctxt1 in nodupd''; try assumption.
   apply IHKderctxt2 in nodupd'; try assumption.
   apply K_cross; try assumption.   
  Case "K_utype".
   assert (Z: d0 = (dctxt alpha k d)).
   admit.
   subst.
   unfold subst_Tau.
   fold subst_Tau.
   case_eq(TV.beq_t alpha alpha0); intros.
   apply TV.beq_t_eq in H0.
   subst.
   inversion H.
   unfold D.K_eq in H1.
   rewrite D.K.beq_t_refl in H1.
   inversion H1.
   assert (Z: D.nodup (dctxt alpha0 k0 (dctxt alpha k d)) = true).
   apply D.nodup_r_str; try assumption.
   apply IHKderctxt in Z.
   constructor; try assumption.
   admit. (* apply D.map_none_r_weak. *)
   admit. (* K_r_weakening, which won't apply due to smaller K. *)
Qed.


Definition K_ind2 := 
fun (P : Delta -> Tau -> Kappa -> Prop) (f : forall d : Delta, P d cint B)
  (f0 : forall (d : Delta) (alpha : TV.T),
        D.map d alpha = Some B -> P d (tv_t alpha) B)
  (f1 : forall (d : Delta) (t0 t1 : Tau),
        K d t0 A -> P d t0 A -> K d t1 A -> P d t1 A -> P d (cross t0 t1) A)
  (f2 : forall (d : Delta) (alpha : TV.T) (k : Kappa) (tau : Tau),
        D.map d alpha = None ->
        K (dctxt alpha k d) tau A ->
        P (dctxt alpha k d) tau A -> P d (utype alpha k tau) A) =>
fix F (d : Delta) (t : Tau) (k : Kappa) (k0 : K d t k) {struct k0} :
  P d t k :=
  match k0 in (K d0 t0 k1) return (P d0 t0 k1) with
  | K_int d0 => f d0
  | K_B d0 alpha e => f0 d0 alpha e
  | K_cross d0 t0 t1 k1 k2 => f1 d0 t0 t1 k1 (F d0 t0 A k1) k2 (F d0 t1 A k2)
  | K_utype d0 alpha k1 tau e k2 =>
      f2 d0 alpha k1 tau e k2 (F (dctxt alpha k1 d0) tau A k2)
  end.

Check K_ind2
     : forall P : Delta -> Tau -> Kappa -> Prop,
       (forall d : Delta, P d cint B) ->
       (forall (d : Delta) (alpha : TV.T),
        D.map d alpha = Some B -> P d (tv_t alpha) B) ->
       (forall (d : Delta) (t0 t1 : Tau),
        K d t0 A -> P d t0 A -> K d t1 A -> P d t1 A -> P d (cross t0 t1) A) ->
       (forall (d : Delta) (alpha : TV.T) (k : Kappa) (tau : Tau),
        D.map d alpha = None ->
        K (dctxt alpha k d) tau A ->
        P (dctxt alpha k d) tau A -> P d (utype alpha k tau) A) ->
       forall (d : Delta) (t : Tau) (k : Kappa), K d t k -> P d t k.

Definition K_ind_dep := 
fun (P : TV.T -> Kappa -> Delta -> Tau -> Kappa -> Prop) 
  (f : forall d : Delta, 
       forall alpha0 : TV.T,
         forall k': Kappa, 
         P alpha0 k' d cint B)
  (f0 : forall (d : Delta) (alpha : TV.T), 
        forall alpha0 : TV.T,
        forall k' : Kappa, 
          D.map d alpha = Some B -> P alpha0 k' d (tv_t alpha) B)
  (f1 : forall (d : Delta) (t0 t1 : Tau),
        forall alpha0 : TV.T,
        forall k' : Kappa, 
          K d t0 A -> 
          P alpha0 k' d t0 A -> 
          K d t1 A -> 
          P alpha0 k' d t1 A -> 
          P alpha0 k' d (cross t0 t1) A)
  (f2 : forall (d : Delta) (alpha : TV.T) (k : Kappa) (tau : Tau),
        D.map d alpha = None ->
        forall alpha0 : TV.T,
        forall k' : Kappa, 
          K (dctxt alpha k d) tau A ->
          P alpha0 k' (dctxt alpha k d) tau A -> 
          P alpha0 k' d (utype alpha k tau) A) =>
fix F (alpha0 : TV.T) (k' : Kappa)
    (d : Delta) (t : Tau) (k : Kappa) 
    (k0 : K d t k) {struct k0} :
  P alpha0 k' d t k :=
  match k0 in (K d0 t0 k1) return (P alpha0 k' d0 t0 k1) with
  | K_int d0 => f d0 alpha0 k'
  | K_B d0 alpha e => f0 d0 alpha alpha0 k' e
  | K_cross d0 t0 t1 k1 k2 => 
    f1 d0 t0 t1 alpha0 k' k1 (F alpha0 k' d0 t0 A k1) k2 (F alpha0 k' d0 t1 A k2)
  | K_utype d0 alpha k1 tau e k2 =>
      f2 d0 alpha k1 tau e alpha0 k' k2 
         (F alpha0 k' (dctxt alpha k1 d0) tau A k2)
  end.

Check K_ind_dep 
     : forall P : TV.T -> Kappa -> Delta -> Tau -> Kappa -> Prop,
       (forall (d : Delta) (alpha0 : TV.T) (k' : Kappa), P alpha0 k' d cint B) ->
       (forall (d : Delta) (alpha alpha0 : TV.T) (k' : Kappa),
        D.map d alpha = Some B -> P alpha0 k' d (tv_t alpha) B) ->
       (forall (d : Delta) (t0 t1 : Tau) (alpha0 : TV.T) (k' : Kappa),
        K d t0 A ->
        P alpha0 k' d t0 A ->
        K d t1 A -> P alpha0 k' d t1 A -> P alpha0 k' d (cross t0 t1) A) ->
       (forall (d : Delta) (alpha : TV.T) (k : Kappa) (tau : Tau),
        D.map d alpha = None ->
        forall (alpha0 : TV.T) (k' : Kappa),
        K (dctxt alpha k d) tau A ->
        P alpha0 k' (dctxt alpha k d) tau A ->
        P alpha0 k' d (utype alpha k tau) A) ->
       forall (alpha0 : TV.T) (k' : Kappa) (d : Delta) (t : Tau) (k : Kappa),
       K d t k -> P alpha0 k' d t k.

Lemma A_6_Substitution_1_apply_no_dep_ind:
  forall (d : Delta) (tau : Tau) (k : Kappa),
      D.nodup d = true ->
      K d tau k ->
      forall (alpha : TV.T) (k' : Kappa) (tau' : Tau), 
        K (dctxt alpha k d) tau' k' ->
        D.nodup (dctxt alpha k d) = true ->
        K d (subst_Tau tau' tau alpha) k'.
Proof.
  intros d tau k nodupd Kderd alpha k' tau' nodupd' Kderctxt.
  apply (K_ind
           (fun (d : Delta) (tau : Tau) (k : Kappa) =>
              K (dctxt alpha k d) tau' k' ->
              D.nodup (dctxt alpha k d) = true ->
              K d (subst_Tau tau' tau alpha) k'))
        with (k:= k); intros.
  admit.
  (* broken. *)
Admitted.

Lemma A_6_Substitution_1_apply_dep_ind:
  forall (d : Delta) (tau : Tau) (k : Kappa),
      K d tau k ->
      forall (alpha : TV.T) (k' : Kappa) (tau' : Tau), 
        K (dctxt alpha k d) tau' k' ->
        K d (subst_Tau tau' tau alpha) k'.
Proof.
  intros d tau k Kderd alpha k' tau' Kderctxt.
  apply (K_ind_dep
           (fun (alpha0 : TV.T) (k' : Kappa) (d0 : Delta) (tau : Tau) (k : Kappa) =>
              K (dctxt alpha0 k' d) tau' k' ->
              K d (subst_Tau tau' tau alpha) k'))
        with (k:= k) (alpha0:=alpha) (d0:=d).
  intros.
  admit.  (* Might be right but it's ugly. *)
  intros. (* Wrong. *)
Admitted.

Inductive K1 : Delta -> Tau -> Kappa -> Prop :=
 | K1_int   : forall (d : Delta), K1 d cint B.

Print K1_ind.

Definition K1_ind2 :=
fun (P : Delta -> Tau -> Kappa -> Prop) 
    (f : forall d : Delta, P d cint B)
    (d : Delta) (t : Tau) (k : Kappa) (k0 : K1 d t k) =>
match k0 in (K1 d0 t0 k1) return (P d0 t0 k1) with
| K1_int x => f x
end.

Definition K1_ind_dep :=
fun (P : Tau -> Kappa -> Prop) 
    (f : P cint B)
    (d : Delta) (t : Tau) (k : Kappa) (k0 : K1 d t k) =>
match k0 in (K1 d0 t0 k1) return (P t0 k1) with
| K1_int x => f 
end.

Lemma A_6_Substitution_1_K1_dep:
  forall (d : Delta) (tau : Tau) (k : Kappa),
      K1 d tau k ->
      forall (alpha : TV.T) (k' : Kappa) (tau' : Tau), 
        K1 (dctxt alpha k d) tau' k' ->
        K1 d (subst_Tau tau' tau alpha) k'.
Proof.
  intros d tau k Kderd alpha k' tau' Kderctxt.
  apply (K1_ind_dep
           (fun (tau : Tau) (k : Kappa) =>
              K1 (dctxt alpha k d) tau' k' ->
              K1 d (subst_Tau tau' tau alpha) k'))
        with (d0:= d) (k:= k); intros.
  admit. (* Looks OK, can't really tell. *)
  assumption.
  assumption.
Qed.
(* Perhaps. *)

Inductive K2 : Delta -> Tau -> Kappa -> Prop :=
 | K2_int   : forall (d : Delta),
                  K2 d cint B

 | K2_B     : forall (d : Delta) (alpha : TV.T),
               D.map d alpha = Some B ->
               K2 d (tv_t alpha) B.
Print K2_ind.

(*
Definition K2_ind_dep :=
fun (P : Tau -> Kappa -> Prop)
    (d : Delta) (t : Tau) (k : Kappa) (k0 : K2 d t k)
    (f : P cint B)
    (f0 : forall (alpha : TV.T),
             D.map (D.ctxt alpha k d) alpha = Some B -> P (tv_t alpha) B) 
=>
  match k0 in (K2 d0 t0 k1) return (P t0 k1) with
    | K2_int x => f
    | K2_B x x0 x1 => f0 x0 x1
  end.
*)

(*
Lemma A_6_Substitution_1_K2_dep:
  forall (d : Delta) (tau : Tau) (k : Kappa),
      K2 d tau k ->
      forall (alpha : TV.T) (k' : Kappa) (tau' : Tau), 
        K2 (dctxt alpha k d) tau' k' ->
        K2 d (subst_Tau tau' tau alpha) k'.
Proof.
  intros d tau k Kderd alpha k' tau' Kderctxt.
  apply (K2_ind_dep
           (fun (tau : Tau) (k : Kappa) =>
              K2 (dctxt alpha k d) tau' k' ->
              K2 d (subst_Tau tau' tau alpha) k'))
        with (d0:= d) (k:= k); intros.
  admit. (* Looks OK, can't really tell. *)
  assumption.
  assumption.
Qed.
*)

(* Try and write d0 = (dctxt alpha k d)) through. *)
Definition J := (fun a0 k2 x x0 => D.map (dctxt a0 k2 x) x0 = Some B).
Lemma transform:
  forall c k a0,
    D.map c k = Some B ->
    D.map (dctxt a0 B c) k = Some B.
Proof.
  induction c; crush.
  case_eq(D.K_eq k0 k); intros; rewrite H0 in *.
  admit.
Admitted.

Check K2_B.
(*

Definition K2_ind_dep2 := 
fun 
  (P : TV.T -> Kappa -> Delta -> Tau -> Kappa -> Prop) 
  (f : forall a0 k2 d, P a0 k2 d cint B)
  (f0 : forall a0 k2 (d : Delta) (alpha : TV.T),
        D.map (dctxt a0 k2 d) alpha = Some B -> P a0 k2 d (tv_t alpha) B) 
  (a0 : TV.T) (k2 : Kappa) (d : Delta) (t : Tau) (k : Kappa) (k0 : K2 d t k) =>
match k0 in (K2 d0 t0 k1) return (P a0 k2 d0 t0 k1) with
| K2_int x => f a0 k2 x
(* | K2_B x x0 (= d0 (dctxt a0 k2 d)) => f0 a0 k2 x x0 (dctxt a0 k2 d) *)
| K2_B x x0 x2 => f0 a0 k2 x x0 x2
end.

(* (D.map (dctxt a0 k2 x) x0 = Some B) *)

Check (fun (x1 : (forall a0 k2 x x0, D.map (dctxt a0 k2 x) x0 = Some B))
       => x1).

(* map x1 to the right type. *)

Lemma A_6_Substitution_1_apply_dep_ind2:
  forall (d : Delta) (tau : Tau) (k : Kappa),
      K2 d tau k ->
      forall (alpha : TV.T) (k' : Kappa) (tau' : Tau), 
        K2 (dctxt alpha k d) tau' k' ->
        K2 d (subst_Tau tau' tau alpha) k'.
Proof.
  intros d tau k Kderd alpha k' tau' Kderctxt.
  apply (K2_ind_dep2
           (fun (alpha : TV.T) (k' : Kappa) (d : Delta) (tau : Tau) (k : Kappa) =>
              K2 (dctxt alpha k d) tau' k' ->
              K2 d (subst_Tau tau' tau alpha) k'))
        with (k:= k); intros.
  admit. (* right *)
  admit. (* Wrong. *)
  admit. (* Unsolvable. *)
  assumption.
Admitted.
*)

(* Quit attempting to fix their induction and just write the right induction 
hypothesis case by case. *)

Check K2.
Check K2_ind.

(* Can't unify. Why ? 
Lemma K2_induction_dependent:
  forall P : Delta -> Tau -> Kappa -> Prop,
    (forall alpha k d, P (D.ctxt alpha k d) cint B) ->
    (forall (alpha : TV.T) (k : Kappa) (d : Delta) (tau : Tau) (k' : Kappa),
        D.map (D.ctxt alpha k d) alpha = Some B -> 
        P (D.ctxt alpha k d) (tv_t alpha) B) -> 
    (forall (alpha : TV.T) (k : Kappa) (d : Delta) (tau : Tau) (k' : Kappa),
      P (D.ctxt alpha k d) tau k').
Admitted.

Lemma A_6_Substitution_1_apply_K2_induction_dependent:
  forall (d : Delta) (tau : Tau) (k : Kappa),
      K2 d tau k ->
      forall (alpha : TV.T) (k' : Kappa) (tau' : Tau), 
        K2 (dctxt alpha k d) tau' k' ->
        K2 d (subst_Tau tau' tau alpha) k'.
Proof.
  intros d tau k Kderd alpha k' tau' Kderctxt.
  apply (K2_induction_dependent
           (fun (d : Delta) (tau : Tau) (k : Kappa) =>
              K2 (dctxt alpha k d) tau' k' ->
              K2 d (subst_Tau tau' tau alpha) k')).

  admit. (* right *)
  admit. (* Wrong. *)
  admit. (* Unsolvable. *)
  assumption.
Admitted.
*)

Lemma K2_induction_dependent_2:
  forall P : TV.T -> Kappa -> Delta -> Tau -> Kappa -> Prop,
    (forall alpha k d, P alpha k d cint B) ->
    (forall (alpha a': TV.T) (k k': Kappa) (d : Delta) (tau : Tau),
        D.map (D.ctxt alpha k d) a' = Some B -> 
        P alpha k d (tv_t a') B) ->
    (forall (alpha : TV.T) (k : Kappa) (d : Delta) (tau : Tau) (k' : Kappa),
      P alpha k d tau k').
Proof.
  intros.
Admitted.

Lemma A_6_Substitution_1_apply_K2_induction_dependent_2:
  forall (d : Delta) (tau : Tau) (k : Kappa),
      K2 d tau k ->
      forall (alpha : TV.T) (k' : Kappa) (tau' : Tau), 
        K2 (dctxt alpha k d) tau' k' ->
        K2 d (subst_Tau tau' tau alpha) k'.
Proof.
  intros d tau k Kderd alpha k' tau' Kderctxt.
(* tau' vs tau ? yep breaking the first case. *)
  apply (K2_induction_dependent_2
           (fun (alpha : TV.T) (k : Kappa) (d : Delta) (tau' : Tau) (k' : Kappa) =>
              K2 d tau k ->
              K2 (dctxt alpha k d) tau' k' ->
              K2 d (subst_Tau tau' tau alpha) k'))
        with (k:= k).
  intros.
  simpl.
  apply K2_int.

  intros.
(* Want.
  Kderd : K d tau k
  H : D.map (dctxt alpha k d) alpha0 = Some B
  ============================
   K d (subst_Tau (tv_t alpha0) tau alpha) B
*)
  (* Have it by lifting the K2 d tau K into the induction hypothesis. *)
(*
  H : D.map (D.ctxt alpha0 k0 d0) a' = Some B
  H0 : K2 d0 tau k0
  H1 : K2 (dctxt alpha0 k0 d0) (tv_t a') B
 And they are disconntexted from extra d terms so they can't be used to
 foul the proof.
*)
  admit. (* Looks OK. *)
  assumption.
  assumption.
(* May work. *)
Admitted.

(* Now with a binding type constructor. *)

Inductive K3 : Delta -> Tau -> Kappa -> Prop :=
 | K3_int   : forall (d : Delta),
                  K3 d cint B

 | K3_B     : forall (d : Delta) (alpha : TV.T),
               D.map d alpha = Some B ->
               K3 d (tv_t alpha) B

 | K3_utype  : forall (d : Delta) (alpha : TV.T) (k : Kappa) (tau : Tau),
                   D.map d alpha = None -> 
                   K3  (dctxt alpha k d) tau A ->
                   K3 d (utype alpha k tau) A.

Print K3_ind.
Definition K3_ind_7 :=
fun (P : Delta -> Tau -> Kappa -> Prop) (f : forall d : Delta, P d cint B)
  (f0 : forall (d : Delta) (alpha : TV.T),
        D.map d alpha = Some B -> 
        P d (tv_t alpha) B)
  (f1 : forall (d : Delta) (alpha : TV.T) (k : Kappa) (tau : Tau),
        D.map d alpha = None ->
        K3 (dctxt alpha k d) tau A ->
        P (dctxt alpha k d) tau A -> P d (utype alpha k tau) A) =>
fix F (d : Delta) (t : Tau) (k : Kappa) (k0 : K3 d t k) {struct k0} :
  P d t k :=
  match k0 in (K3 d0 t0 k1) return (P d0 t0 k1) with
  | K3_int d0 => f d0
  | K3_B d0 alpha e => f0 d0 alpha e
  | K3_utype d0 alpha k1 tau e k2 =>
      f1 d0 alpha k1 tau e k2 (F (dctxt alpha k1 d0) tau A k2)
end.

Lemma K3_induction_dependent:
  forall P : TV.T -> Kappa -> Delta -> Tau -> Kappa -> Prop,
    (forall alpha k d, P alpha k d cint B) ->
    (forall (alpha a': TV.T) (k k': Kappa) (d : Delta) (tau : Tau),
        D.map (D.ctxt alpha k d) a' = Some B -> 
        P alpha k d (tv_t a') B) ->
    (forall (d : Delta) (alpha a' : TV.T) (k k': Kappa) (tau : Tau),
        D.map d alpha = None ->
        K3 (dctxt alpha k d) tau A ->
        P alpha k d tau A -> 
        P alpha k d (utype a' k tau) A) ->
    (forall (alpha : TV.T) (k : Kappa) (d : Delta) (tau : Tau) (k' : Kappa),
      P alpha k d tau k').
Proof.
  intros.
Admitted.

Lemma A_6_Substitution_1_apply_K3_induction_dependent:
  forall (d : Delta) (tau : Tau) (k : Kappa),
      K3 d tau k ->
      forall (alpha : TV.T) (k' : Kappa) (tau' : Tau), 
        K3 (dctxt alpha k d) tau' k' ->
        K3 d (subst_Tau tau' tau alpha) k'.
Proof.
  intros d tau k Kderd alpha k' tau' Kderctxt.
(* tau' vs tau ? yep breaking the first case. *)
  apply (K3_induction_dependent
           (fun (alpha : TV.T) (k : Kappa) (d : Delta) (tau' : Tau) (k' : Kappa) =>
              K3 d tau k ->
              K3 (dctxt alpha k d) tau' k' ->
              K3 d (subst_Tau tau' tau alpha) k'))
        with (k:= k); try assumption.
  intros.
  simpl.
  apply K3_int.

  intros.
(* Want.
  Kderd : K d tau k
  H : D.map (dctxt alpha k d) alpha0 = Some B
  ============================
   K d (subst_Tau (tv_t alpha0) tau alpha) B
*)
  (* Have it by lifting the K3 d tau K into the induction hypothesis. *)
(*
  H : D.map (D.ctxt alpha0 k0 d0) a' = Some B
  H0 : K3 d0 tau k0
  H1 : K3 (dctxt alpha0 k0 d0) (tv_t a') B
 And they are disconntexted from extra d terms so they can't be used to
 foul the proof.
*)
  admit. (* Looks OK. *)
 (* Want. 
  Kderctxt1 : K d0 t0 A
  Kderctxt2 : K d0 t1 A
  IHKderctxt1 : D.nodup d0 = true -> K d (subst_Tau t0 tau alpha) A
  IHKderctxt2 : D.nodup d0 = true -> K d (subst_Tau t1 tau alpha) A
  Z : d0 = dctxt alpha k d
  ============================
   K d (subst_Tau (cross t0 t1) tau alpha) A
*)
  intros.
(*  Want and I have it!!!!!
  nodupd' : D.nodup (dctxt alpha k d) = true
  H : D.map (dctxt alpha k d) alpha0 = None
  Kderctxt : K (dctxt alpha0 k0 (dctxt alpha k d)) tau0 A
  IHKderctxt : D.nodup (dctxt alpha0 k0 (dctxt alpha k d)) = true ->
               K d (subst_Tau tau0 tau alpha) A
  ============================
   K d (subst_Tau (utype alpha0 k0 tau0) tau alpha) A
*)

  admit.
(* May work. *)
Admitted.


Inductive K4 : Delta -> Tau -> Kappa -> Prop :=
 | K4_int   : forall (d : Delta),
                  K4 d cint B

 | K4_B     : forall (d : Delta) (alpha : TV.T),
               D.map d alpha = Some B ->
               K4 d (tv_t alpha) B

 | K4_cross   : forall (d : Delta) (t0 t1 : Tau),
                    K4 d t0 A ->
                    K4 d t1 A ->
                    K4 d (cross t0 t1) A

 | K4_utype  : forall (d : Delta) (alpha : TV.T) (k : Kappa) (tau : Tau),
                   D.map d alpha = None -> 
                   K4  (dctxt alpha k d) tau A ->
                   K4 d (utype alpha k tau) A.

Print K4_ind.
Definition K4_ind_7 :=
fun (P : Delta -> Tau -> Kappa -> Prop) (f : forall d : Delta, P d cint B)
  (f0 : forall (d : Delta) (alpha : TV.T),
        D.map d alpha = Some B -> P d (tv_t alpha) B)
  (f1 : forall (d : Delta) (t0 t1 : Tau),
        K4 d t0 A -> P d t0 A -> K4 d t1 A -> P d t1 A -> P d (cross t0 t1) A)
  (f2 : forall (d : Delta) (alpha : TV.T) (k : Kappa) (tau : Tau),
        D.map d alpha = None ->
        K4 (dctxt alpha k d) tau A ->
        P (dctxt alpha k d) tau A -> P d (utype alpha k tau) A) =>
fix F (d : Delta) (t : Tau) (k : Kappa) (k0 : K4 d t k) {struct k0} :
  P d t k :=
  match k0 in (K4 d0 t0 k1) return (P d0 t0 k1) with
  | K4_int d0 => f d0
  | K4_B d0 alpha e => f0 d0 alpha e
  | K4_cross d0 t0 t1 k1 k2 =>
      f1 d0 t0 t1 k1 (F d0 t0 A k1) k2 (F d0 t1 A k2)
  | K4_utype d0 alpha k1 tau e k2 =>
      f2 d0 alpha k1 tau e k2 (F (dctxt alpha k1 d0) tau A k2)
  end.

Lemma K4_induction_dependent:
  forall P : TV.T -> Kappa -> Delta -> Tau -> Kappa -> Prop,
    (forall alpha k d, P alpha k d cint B) ->
    (forall (alpha a': TV.T) (k k': Kappa) (d : Delta) (tau : Tau),
        D.map (D.ctxt alpha k d) a' = Some B -> 
        P alpha k d (tv_t a') B) ->
  (forall (alpha : TV.T) (k : Kappa) (d : Delta) (t0 t1 : Tau),
        K4 (dctxt alpha k d) t0 A -> 
        P alpha k d t0 A -> 
        K4 (dctxt alpha k d) t1 A -> 
        P alpha k d t1 A -> 
        P alpha k d (cross t0 t1) A) -> 
    (forall (d : Delta) (alpha a' : TV.T) (k k': Kappa) (tau : Tau),
        D.map d alpha = None ->
        K4 (dctxt alpha k d) tau A ->
        P alpha k d tau A -> 
        P alpha k d (utype a' k tau) A) ->
    (forall (alpha : TV.T) (k : Kappa) (d : Delta) (tau : Tau) (k' : Kappa),
      P alpha k d tau k').
Proof.
  intros.
Admitted.

Lemma A_6_Substitution_1_apply_K4_induction_dependent:
  forall (d : Delta) (tau : Tau) (k : Kappa),
      K4 d tau k ->
      forall (alpha : TV.T) (k' : Kappa) (tau' : Tau), 
        K4 (dctxt alpha k d) tau' k' ->
        K4 d (subst_Tau tau' tau alpha) k'.
Proof.
  intros d tau k Kderd alpha k' tau' Kderctxt.
(* tau' vs tau ? yep breaking the first case. *)
  apply (K4_induction_dependent
           (fun (alpha : TV.T) (k : Kappa) (d : Delta) (tau' : Tau) (k' : Kappa) =>
              K4 d tau k ->
              K4 (dctxt alpha k d) tau' k' ->
              K4 d (subst_Tau tau' tau alpha) k'))
        with (k:= k); try assumption.
  intros.
  simpl.
  apply K4_int.

  intros.
(* Want.
  Kderd : K d tau k
  H : D.map (dctxt alpha k d) alpha0 = Some B
  ============================
   K d (subst_Tau (tv_t alpha0) tau alpha) B
*)
  (* Have it by lifting the K4 d tau K into the induction hypothesis. *)
(*
  H : D.map (D.ctxt alpha0 k0 d0) a' = Some B
  H0 : K4 d0 tau k0
  H1 : K4 (dctxt alpha0 k0 d0) (tv_t a') B
 And they are disconntexted from extra d terms so they can't be used to
 foul the proof.
*)
  admit. (* Looks OK. *)
(* Want
  nodupd : D.nodup d = true
  Kderd : K d tau k
  nodupd' : D.nodup (dctxt alpha k d) = true
  Kderctxt1 : K (dctxt alpha k d) t0 A
  Kderctxt2 : K (dctxt alpha k d) t1 A
  IHKderctxt1 : D.nodup (dctxt alpha k d) = true ->
                K d (subst_Tau t0 tau alpha) A
  IHKderctxt2 : D.nodup (dctxt alpha k d) = true ->
                K d (subst_Tau t1 tau alpha) A
  ============================
   K d (subst_Tau (cross t0 t1) tau alpha) A
*)
  intros.

  admit.
 (* Want. 
  Kderctxt1 : K d0 t0 A
  Kderctxt2 : K d0 t1 A
  IHKderctxt1 : D.nodup d0 = true -> K d (subst_Tau t0 tau alpha) A
  IHKderctxt2 : D.nodup d0 = true -> K d (subst_Tau t1 tau alpha) A
  Z : d0 = dctxt alpha k d
  ============================
   K d (subst_Tau (cross t0 t1) tau alpha) A
*)
  Looks good!

  intros.
(*  Want and I have it!!!!!
  nodupd' : D.nodup (dctxt alpha k d) = true
  H : D.map (dctxt alpha k d) alpha0 = None
  Kderctxt : K (dctxt alpha0 k0 (dctxt alpha k d)) tau0 A
  IHKderctxt : D.nodup (dctxt alpha0 k0 (dctxt alpha k d)) = true ->
               K d (subst_Tau tau0 tau alpha) A
  ============================
   K d (subst_Tau (utype alpha0 k0 tau0) tau alpha) A
*)

  admit.
(* May work. *)
Admitted.