(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Defining type safety, page 67.

*)

Require Export CpdtTactics.
Require Export TacticNotations.
Require Export LanguageModuleDef.
Require Export ListLemmas.

Lemma A_10_Path_Extension_1_A_good_get:
  forall (v v' v0 v1 : E) (p : Path),
    Value v  ->
    Value v' ->
    get v p v' ->
    v' = (cpair v0 v1) ->
    (get v (p ++ [i_pe zero_pe]) v0 /\ 
     get v (p ++ [i_pe one_pe]) v1).
Proof.
  intros v v' v0 v1 p Valuev Valuev' getder.
  get_ind_cases (induction getder) Case.
  Case "v [] v".
   intros.
   split.
   SCase "zero_pe".
    rewrite app_nil_l.
    rewrite <- app_nil_r with (l:= [i_pe zero_pe]).
    rewrite H0.
    rewrite H0 in Valuev.
    inversion Valuev.
    apply get_l; try assumption.
    constructor; try assumption.
   SCase "one_pe".
    rewrite app_nil_l.
    rewrite <- app_nil_r with (l:= [i_pe one_pe]).
    rewrite H0.
    rewrite H0 in Valuev.
    inversion Valuev.
    apply get_r; try assumption.
    constructor; try assumption.
  Case "(cpair v0 v1) (i_pe zero_pe :: p) v".
   intros.
   pose proof H0 as Valuev2.
   apply IHgetder in H0; try assumption.
   inversion H0.
   rewrite H2 in Valuev'.
   inversion Valuev'.
   split.
   SCase "zero_pe".
    constructor; try assumption.
   SCase "one_pe".
    constructor; try assumption.
  Case "(cpair v0 v1) (i_pe one_pe :: p) v".
   intros.
   pose proof H1 as Valuev3.
   apply IHgetder in H1; try assumption.
   inversion H1.
   rewrite H2 in Valuev'.
   inversion Valuev'.
   split.
   SCase "zero_pe".
    constructor; try assumption.
   SCase "one_pe".
    constructor; try assumption.
  Case "(pack tau' v1 (etype aliases alpha k tau)) (u_pe :: p)v".
   intros.
   pose proof H0 as Valuev2'.
   apply IHgetder in H0; try assumption.
   inversion H0.
   rewrite H1 in Valuev'.
   inversion Valuev'.
   split.
   SCase "zero_pe".
    constructor; try assumption.
   SCase "one_pe".
    constructor; try assumption.
Qed.

Lemma A_10_Path_Extension_1_A_bad_get_almost:
  forall (v v' : E) (p : Path),
    Value v  ->
    Value v' ->
    get v p v' ->
    ~(exists v0 : E, exists v1 : E, v=(cpair v0 v1)) -> 
    forall (p' : Path) (v'' : E),
      ~(get v (p ++ [i_pe one_pe] ++ p') v'') /\
      ~(get v (p ++ [i_pe zero_pe] ++ p') v'').
Proof.
  intros v v' p Valuev Valuev'  getder.
  get_ind_cases (induction getder) Case.  

  Case "v [] v".
   intros.
   split.

   unfold not.
   intros.

   rewrite app_nil_l in H1.
   rewrite <- cons_is_append_singleton in H1.

   inversion H1.
   unfold not in H0.
   destruct H0.
   apply ex_intro with (x:= v1).
   apply ex_intro with (x:= v2).
   symmetry.
   assumption.

   unfold not.
   intros.
   rewrite app_nil_l in H1.
   rewrite <- cons_is_append_singleton in H1.
   inversion H1.
   unfold not in H0.
   destruct H0.
   apply ex_intro with (x:= v1).
   apply ex_intro with (x:= v2).
   symmetry.
   assumption.

  Case "(cpair v0 v1) (i_pe zero_pe :: p) v".
   intros.
   destruct H2.
   apply ex_intro with (A:= E) (x:= v0).
   apply ex_intro with (A:= E) (x:= v1).
   reflexivity.

  Case "(cpair v0 v1) (i_pe one_pe :: p) v".
   intros.
   destruct H2.
   apply ex_intro with (A:= E) (x:= v0).
   apply ex_intro with (A:= E) (x:= v1).
   reflexivity.

  Case "(pack tau' v1 (etype aliases alpha k tau)) (u_pe :: p)v".
   intros.
   unfold not in H1.
   rewrite cons_is_append_singleton.
   rewrite <- app_assoc with (l:= [u_pe]).
   apply IHgetder with (p':= p') (v'':= v'') in H0; try assumption.
   inversion H0.
   unfold not in H2.
   unfold not in H3.

   split.

   unfold not.
   intros.
   inversion H4.
   apply H2 in H14.
   inversion H14.

   unfold not.
   intros.
   inversion H4.
   apply H3 in H14.
   inversion H14.

   SCase "~ (exists v3 v4 : E, v2 = cpair v3 v4)".
    unfold not.
    intros.
    destruct v1; try solve [inversion H2; inversion H3; inversion H4].
    (* now I need a contradiction. *)
    inversion H2.
    inversion H3.
    admit.
Admitted.

Lemma A_10_Path_Extension_1_A_bad_get_induction_length_p:
  forall (v v' : E),
    Value v  ->
    Value v' ->
    forall (n : nat),
     forall (p : Path),
       length p = n -> 
       get v p v' ->
       ~(exists v0 : E, exists v1 : E, v=(cpair v0 v1)) -> 
       forall (p' : Path) (v'' : E),
         ~(get v (p ++ [i_pe one_pe] ++ p') v'') /\
         ~(get v (p ++ [i_pe zero_pe] ++ p') v'').
Proof.
  intros v v' Valuev valuev' n.
  induction n.
  Case "n = 0".
   intros.
   apply list_of_length_0_is_nil in H.
   rewrite H in H0.
   rewrite H.
   rewrite app_nil_l.
   rewrite app_nil_l.
   inversion H0.
   rewrite <- H5.
   split. 
   SCase "~ get v ([i_pe one_pe] ++ p') v''".
    unfold not.
    intros.
    inversion H4.
    symmetry in H10.
    destruct H1.
    apply ex_intro with (x:= v2).
    apply ex_intro with (x:= v3).
    assumption.
  SCase "~ get v ([i_pe zero_pe] ++ p') v''".
    admit. (* similar, let's see if I can get the induction step. *)
  Case "length p = S n".
   intros.
   destruct p as [| pe p ].
   inversion H. (* P can't be nil as it has length n+1. *)
   destruct pe; try destruct i.
   SCase "zero_pe".
    inversion H.
    apply IHn with (p:= p) (p':= p') (v'':= v'') in H3;  try assumption.
    inversion H3.
    inversion H0.
    destruct H1.
    symmetry in H9.
    apply ex_intro with (x:= v1).
    apply ex_intro with (x:= v2).
    assumption.
    SSCase "get v p v'".
     inversion H0.
     symmetry in H7.
     destruct H1.
     apply ex_intro with (x:= v1).
     apply ex_intro with (x:= v2).
     assumption.
   SCase "one_pe".
    inversion H.
    apply IHn with (p:= p) (p':= p') (v'':= v'') in H3;  try assumption.
    inversion H3.
    inversion H0.
    destruct H1.
    symmetry in H9.
    apply ex_intro with (x:= v1).
    apply ex_intro with (x:= v2).
    assumption.
    SSCase "get v p v'".
     inversion H0.
     symmetry in H7.
     destruct H1.
     apply ex_intro with (x:= v1).
     apply ex_intro with (x:= v2).
     assumption.
   SCase "u_pe".
   
    inversion H.
    inversion H0.
    rewrite <- H6 in *.
    apply IHn with (p:= p) (p':= p') (v'':= v'') in H3;  try assumption.
    inversion H3.
    split.
    unfold not.
    intros.
    inversion H11.
    admit.
    admit.
    admit.
Admitted.

Lemma A_10_Path_Extension_1_A_bad_get_induction_length_p_tighten_v:
    forall (n : nat),
     forall (p : Path),
       length p = n -> 
       forall (v v' : E),
         Value v  ->
         Value v' ->
         get v p v' ->
         ~(exists v0 : E, exists v1 : E, v=(cpair v0 v1)) -> 
         forall (p' : Path) (v'' : E),
           ~(get v (p ++ [i_pe one_pe] ++ p') v'') /\
           ~(get v (p ++ [i_pe zero_pe] ++ p') v'').
Proof.
  intros n.
  induction n.
  Case "n = 0".
   intros.
   apply list_of_length_0_is_nil in H.
   rewrite H in *.
   rewrite app_nil_l.
   rewrite app_nil_l.
   inversion H2.
   rewrite <- H7.
   split.
   SCase "~ get v ([i_pe one_pe] ++ p') v''".
    unfold not.
    intros.
    inversion H6.
    symmetry in H12.
    destruct H3.
    apply ex_intro with (x:= v2).
    apply ex_intro with (x:= v3).
    assumption.
  SCase "~ get v ([i_pe zero_pe] ++ p') v''".
    admit. (* similar, let's see if I can get the induction step. *)
    (* Can I prove this with stronger v v'. *)
  Case "length p = S n".
   intros.
   destruct p as [| pe p ].
   SCase "p = nil".
    inversion H. (* P can't be nil as it has length n+1. *)
   destruct pe; try destruct i.
   SCase "zero_pe".
    inversion H.
    apply IHn with (p:= p) (p':= p') (v:= v) (v':= v') 
                           (v'':= v'') in H5;  try assumption.
    inversion H5.
    inversion H2.
    destruct H3.
    symmetry in H11.
    apply ex_intro with (x:= v1).
    apply ex_intro with (x:= v2).
    assumption.
    SSCase "get v p v'".
     inversion H2.
     symmetry in H9.
     destruct H3.
     apply ex_intro with (x:= v1).
     apply ex_intro with (x:= v2).
     assumption.
   SCase "one_pe".
    inversion H.
    apply IHn with (p:= p) (p':= p') (v:= v) (v':= v') 
                           (v'':= v'') in H5;  try assumption.
    inversion H5.
    inversion H2.
    destruct H3.
    symmetry in H11.
    apply ex_intro with (x:= v1).
    apply ex_intro with (x:= v2).
    assumption.
    SSCase "get v p v'".
     inversion H2.
     symmetry in H9.
     destruct H3.
     apply ex_intro with (x:= v1).
     apply ex_intro with (x:= v2).
     assumption.
   SCase "u_pe".
    inversion H.
    specialize (IHn p H5).
    inversion H2.
    specialize (IHn v' v''). (* wrong vs?*)
    admit.
Admitted.

Lemma A_10_Path_Extension_1_B_good_get:
  forall (v v' v0 : E) (tau tau' : Tau) (alpha : TVar) (k : Kappa)
         (p : Path),
    Value v  ->
    Value v' ->
    get v p v' ->
    v' = (pack tau' v0 (etype aliases alpha k tau)) ->
    get v (p ++ [u_pe]) v0 .
Proof.
  intros v v' v0 tau tau' alpha k p Valuev Valuev' getder.
  get_ind_cases (induction getder) Case.  
  Case "v [] v".
   intros.
   rewrite app_nil_l.
   rewrite <- app_nil_r with (l:= [u_pe]).
   rewrite H0 in Valuev.
   inversion Valuev; try assumption.
   rewrite H0.
   constructor; try assumption.
   constructor; try assumption.
  Case "(cpair v0 v1) (i_pe zero_pe :: p) v".
   intros.
   pose proof H0 as Valuev1'.
   apply IHgetder in H0; try assumption.
   constructor; try assumption.
   inversion H0; try assumption.
  Case "(cpair v0 v1) (i_pe one_pe :: p) v".
   intros.
   pose proof H1 as Valuev2'.
   apply IHgetder in H1; try assumption.
   constructor; try assumption.
   inversion H1; try assumption.
  Case "(pack tau' v1 (etype aliases alpha k tau)) (u_pe :: p)v".
   intros.
   pose proof H0 as Valuev1'.
   apply IHgetder in H0; try assumption.
   rewrite H1 in Valuev'.
   inversion Valuev'.
   constructor; try assumption.
Qed.
  
Lemma A_10_Path_Extension_1_B:
  forall (v v' v0 : E) (tau tau' : Tau) (alpha : TVar) (k : Kappa)
         (p : Path),
    Value v  ->
    Value v' ->
    get v p v' ->
    v' = (pack tau' v0 (etype aliases alpha k tau)) ->
    get v (p ++ [u_pe]) v0 \/
     forall (p' : Path) (v'' : E),
      ~(get v (p ++ [u_pe] ++ p') v'').
Proof.
  intros v v' v0 v1 p.
  intros valv valv' getvpv'.
  (* induction n. Not likely. *)
  (* crush gets 0. *)
Admitted.

Lemma A_10_Path_Extension_2_A:
  forall (u : Upsilon) (x : EVar) (p p' : Path) (tau tau' t0 t1 : Tau)
         (n : nat),
    gettype u x p tau p' tau' ->
    tau' = (cross t0 t1) ->
    (gettype u x p tau (p' ++ [i_pe zero_pe]) t0  /\
     gettype u x p tau (p' ++ [i_pe one_pe])  t1).
Proof.
  intros u x p p' tau tau' t0 t1 n gettypeder.
  gettype_ind_cases (induction gettypeder) Case.
  Case "gettype u x p tau [] tau".
   intros.
   split.
   rewrite H.
   constructor; try assumption.
   constructor.
   rewrite H.
   constructor; try assumption.
   constructor.
  Case "gettype u x p (cross t0 t1) (i_pe zero_pe :: p') tau".
   intros.
   rewrite H in gettypeder.
   apply IHgettypeder in H.
   inversion H.
   split.
   constructor; try assumption.
   constructor; try assumption.
  Case "gettype u x p (cross t0 t1) (i_pe one_pe :: p') tau".
   intros.
   rewrite H in gettypeder.
   apply IHgettypeder in H.
   inversion H.
   split.
   constructor; try assumption.
   constructor; try assumption.
  Case "gettype u x p (etype aliases alpha k tau') (u_pe :: p') tau)".
   intros.
   rewrite H0 in gettypeder.
   apply IHgettypeder in H0; try assumption.
   inversion H0; try assumption.
   split.
   SCase "left".
    rewrite <- app_assoc.
    apply gettype_etype with (tau'':= tau''); try assumption.
   SCase "right".
    rewrite <- app_assoc.
    apply gettype_etype with (tau'':= tau''); try assumption.
Qed.  
  
Lemma A_10_Path_Extension_2_B:
  forall (u : Upsilon) (x : EVar) (p : Path) (tau : Tau) (p' : Path) (tau' : Tau),
    gettype u x p tau p' tau' ->
    forall (alpha : TVar) (k : Kappa) (t0: Tau), 
      tau' = (etype aliases alpha k t0) ->
      forall (tau'' : Tau), 
        U.map u (x,p) = Some tau'' ->
        gettype u x p tau (p' ++ [u_pe]) (subst_Tau t0 tau'' alpha).
Proof.
  intros u x p tau p' tau' gettypeder.
  gettype_ind_cases (induction gettypeder) Case.
  Case "gettype u x p tau [] tau".
   intros.
   rewrite H.
   rewrite app_nil_l.
   rewrite <- app_nil_r with (l:= [u_pe]).
   apply gettype_etype with (tau'':= tau'');  try assumption.
   constructor.
  Case "gettype u x p (cross t0 t1) (i_pe zero_pe :: p') tau".
   intros.
  (* Should these invert away as only way to go into an etype is with a u ? *)
   rewrite H in gettypeder.
   rewrite <- app_assoc.
   constructor; try assumption.
   destruct tau''. 
  (* Six cases to whittle away with inversion gettypeder? *)
   admit.
   admit.
   SCase "cross t _".
    apply IHgettypeder with (tau'':= (cross tau''1 tau''2)) in H.
    try assumption.
    admit.
   SCase "cross _ t".
    admit.
   admit.
   admit.
   admit.
  Case "gettype u x p (cross t0 t1) (i_pe one_pe :: p') tau".
   admit.
  Case "gettype u x p (etype aliases alpha k tau') (u_pe :: p') tau)".
   intros.
   rewrite <- app_assoc.
   apply gettype_etype with (tau'':= tau''); try assumption.
   apply IHgettypeder with (k:= k0); try assumption.
   admit. (* GetU wrong path ? *)
Admitted.

(* Fix p problem in inductive cases. *)
(* Hypotheses:
    a) gettype is broken - I can't see it.
    b) theorem statement is broken.
       i) drop u_pe from p'.- no
       ii) add it in getU?
    c) induction is broken in that p is being changed. 
    d) I'm missing a way to find this even though it's contradictory.
    e) I should be able to unify the added path element, which is nonsense.
    f) The theorem is wrong for etypes. Which I doubt.
    g) The theorem statement is too weak. 
    h) The theorem is not provable on the gettype derivation.
       Must use path's or getU derivation. - not likely either
          as the other cases proved out right.
*)
Lemma A_10_Path_Extension_2_B':
  forall (u : Upsilon) (x : EVar) (p : Path) (tau : Tau) (p' : Path) (tau' : Tau),
    gettype u x p tau p' tau' ->
    forall (alpha : TVar) (k : Kappa) (t0: Tau), 
      tau' = (etype aliases alpha k t0) ->
      forall (tau'' : Tau),
        U.map u (x,p) = Some tau'' ->
        gettype u x p tau (p' ++ [u_pe]) (subst_Tau t0 tau'' alpha).
Proof.
  intros u x p tau p' tau' gettypeder.
  gettype_ind_cases (induction gettypeder) Case.
  Case "gettype u x p tau [] tau".
   intros.
   rewrite H.
   rewrite app_nil_l.
   rewrite <- app_nil_r with (l:= [u_pe]).
   apply gettype_etype with (tau'':= tau'');  try assumption.
   constructor.
  Case "gettype u x p (cross t0 t1) (i_pe zero_pe :: p') tau".
   intros.
   rewrite <- app_assoc.
   constructor; try assumption.
   apply IHgettypeder with (tau'':= tau'') in H; try assumption.
   admit. (* GetU wrong path? *)
  Case "gettype u x p (cross t0 t1) (i_pe one_pe :: p') tau".
   intros.
   rewrite <- app_assoc.
   constructor; try assumption.
   apply IHgettypeder with (tau'':= tau'') in H; try assumption.
   admit.
  Case "gettype u x p (etype aliases alpha k tau') (u_pe :: p') tau)".
   intros.
   rewrite <- app_assoc.
   apply gettype_etype with (tau'':= tau''); try assumption.
   apply IHgettypeder with (k:= k0); try assumption.
   admit. (* GetU wrong path ? *)
Qed.

Lemma A_10_Path_Extension_2_B_length_p':
  forall (n : nat),
    forall (p' : Path),
      length p' = n ->
      forall (u : Upsilon) (x : EVar) (p : Path) (tau : Tau) (tau' : Tau),
        gettype u x p tau p' tau' ->
        forall (alpha : TVar) (k : Kappa) (t0: Tau), 
          tau' = (etype aliases alpha k t0) ->
          forall (tau'' : Tau), 
            U.map u (x,p) = Some tau'' ->
            gettype u x p tau (p' ++ [u_pe]) (subst_Tau t0 tau'' alpha).
Proof.
  intros n.
  induction n.
  SCase "n = 0".
   intros.
   apply list_of_length_0_is_nil in H.
   rewrite H.
   rewrite app_nil_l.
   rewrite H in H0.
   inversion H0.
   rewrite H1.
   apply gettype_etype with (tau'':= tau''); try assumption.
   apply gettype_nil.
  SCase "n = S n".
   intros.
   case_eq (rev p').
   SSCase "rev p' = []".
    intros.
    apply rev_nil in H3.
    rewrite H3.
    rewrite app_nil_l.
    rewrite H1 in H0.
    rewrite H3 in H0.
    inversion H0.
    apply gettype_etype with (tau'':= tau''); try assumption.
    apply gettype_nil.
   SSCase "rev p' = p0 :: (rev l)".
    intros.
    apply rev_cons_app in H3.
    (* False! *)
    assert (Y: length ((rev l) ++ [p0]) = n).
    admit.
    apply IHn with (u:= u) (x:= x) (p:= p) (p':= (rev l) ++ [p0]) (tau:= tau)
                           (tau':=(etype aliases alpha k t0)) 
      (alpha:= alpha) (k:= k) (t0:= t0) (tau'':= tau'') in Y; try assumption.
    rewrite H1 in H0; try assumption.
    rewrite H3.
    assumption.
    rewrite H3 in H0.
    rewrite H1 in H0.
    assumption.
    reflexivity.
Qed.