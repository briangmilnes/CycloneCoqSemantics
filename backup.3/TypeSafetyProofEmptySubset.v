(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  The trivial subset of the language. 

 This is an attempt to see if I can work with these proofs.
 It is teaching me a few things but most of it is just rubbish. 

 Lessons: 

 So far it has shown me that I have to make gettype a relation again,
 as we induct on the structure of its derivation.

 Also it is checking for unused quantifiers.

 And it is teaching me how to do a proof by derivation of a relation.

 And it is teaching me how to set up a simultaneous instruction.

 And it is showing me how to do a proof by inspection and the form of values.

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.
Require Import CpdtTactics.

Require Export FormalSyntax.
Require Export DynamicSemanticsTypeSubstitution.
Require Export DynamicSemanticsHeapObjects.
Require Export DynamicSemantics.
Require Export DynamicSemanticsTypeSubstitution.
Require Export StaticSemanticsKindingAndContextWellFormedness.
Require Export StaticSemantics.
Require Export TypeSafetyProof.
Require Export TypeSafety.

Fixpoint EmptySubsetTau (tau : Tau) :=
  match tau with
    | _ => False
  end.

Fixpoint EmptySubsetSt (s : St) :=
  match s with
    | _ => False
  end.

Fixpoint EmptySubsetE (e : E) :=
  match e with
    | _ => False
  end.

(* Just test that I can easily automate away all cases. *)
Theorem Type_Safety_Empty_Bad_Induction: 
 forall (s : St) (tau : Tau),
   EmptySubsetSt s ->
   EmptySubsetTau tau ->
   styp [] [] [] tau s ->
   ret s ->
   exists (h' : H) (s' : St), 
     Sstar [] s h' s' -> 
     NotStuck h' s'.
Proof.
  intros s tau.
  induction s;  crush.
Qed.

Theorem Type_Safety_Empty_Mutual_Induction: 
 forall (s : St) (tau : Tau),
   EmptySubsetSt s ->
   EmptySubsetTau tau ->
   styp [] [] [] tau s ->
   ret s ->
   exists (h' : H) (s' : St), 
     Sstar [] s h' s' -> 
     NotStuck h' s'.
Proof.
  intros s tau.
  induction s;  crush.
Qed.

Lemma A_1_Context_Weakening_1:
  forall (d d' : Delta) (tau : Tau) (k : Kappa),
    EmptySubsetTau tau ->
    K d tau k ->
    K (d ++ d') tau k.
Proof.
  intros d d' tau k NoSuchType.
  intros Kderivation.
  induction Kderivation; 
  try inversion NoSuchType.
  induction tau; 
  try inversion NoSuchType.  
Qed.

(* TODO need ltac that just finds the EmptySubsetTau and gives it a
  known name ?*)
Lemma A_1_Context_Weakening_2:
  forall (u : Upsilon) (d : Delta) (tau : Tau) 
         (x : EVar) (p : P),
    EmptySubsetTau tau ->
    WFU u ->
    getU u x p = Some tau ->
    K d tau A.
Proof.
  intros u d tau x p NoSuchType WFUderivation.
  induction WFUderivation.
  induction tau; try inversion NoSuchType.
  induction tau; try inversion NoSuchType.
Qed.

(* Observation, not getting all that much here but a check on the
  quantifiers. *)

Lemma A_2_Term_Weakening_1 :
  forall (d: Delta) (u u' : Upsilon) (g g' : Gamma)
         (x : EVar) (p p' : P) (tau tau' : Tau),
    EmptySubsetTau tau ->
    EmptySubsetTau tau' ->
    WFC d (u ++ u') (g ++ g') ->
    gettype u x p tau p' = Some tau' ->
    gettype (u ++ u') x p tau p' = Some tau'.
Proof.
  intros d u u' g g' x p p' tau tau'.
  intros NoSuchTypeTau NoSuchTypeTau'.
  intros WFCd.
  intros gettypederivation.
  functional induction (gettype u x p tau p'); try inversion NoSuchTypeTau.
Qed.

Lemma A_2_Term_Weakening_2 :
  forall (d: Delta) (u u' : Upsilon) (g g' : Gamma)
         (e : E) (tau : Tau),
(*    EmptySubsetTau tau ->
    EmptySubsetE   e ->
*)
    WFC d (u ++ u') (g ++ g') ->
    ltyp d u g e tau ->
    ltyp d (u ++ u') (g++g') e tau.
Proof.
(*
  intros *.
  intros NoSuchType NoSuchExpression.
  intros H.
  intros ltypederivation.
  induction ltypederivation;
    try (try inversion NoSuchType; try inversion NoSuchExpression).
*)
  (* Simultaneous induction on the assumed typing derivation. 
    By which I think he means ltyp. *)
  (* So this is on ltyp, rtyp and stype. *)
  intros d u u' g g' e tau WFCder.
  (* No unification, good question why. I need to start on a simpler
   case. *)
(*  apply (typ_ind_mutual
           (fun (c1 : C) (tau : Tau) (s : St) (st : styp c1 tau s) =>
                 forall (u' : Upsilon) (g' : Gamma),
                   match c1 with
                     | d u g =>
                       ltyp d (u ++ u') (g ++ g') e tau
                   end)).
*)
  (* C failing to match so I either have to restructure the theorems or
   pattern match here. Going to try the pattern match. *)
Admitted.

Lemma A_2_Term_Weakening_3 :
  forall (d: Delta) (u u' : Upsilon) (g g' : Gamma)
         (e : E) (tau : Tau),
    EmptySubsetTau tau ->
    EmptySubsetE e ->
    WFC d (u ++ u') (g ++ g') ->
    rtyp d u g e tau ->
    rtyp d (u ++ u') (g++g') e tau.  
Proof.
  intros *.
  intros NoSuchType NoSuchExpression.
  intros WFCderivation.
  intros rtypederivation.
  induction rtypederivation;
    try (try inversion NoSuchType; try inversion NoSuchExpression).
Qed.

Lemma A_2_Term_Weakening_4 :
  forall (d: Delta) (u u' : Upsilon) (g g' : Gamma)
         (s : St) (tau : Tau),
    EmptySubsetTau tau ->
    EmptySubsetSt s ->
    WFC d (u ++ u') (g ++ g') ->
    styp d u g               tau s ->
    styp d (u ++ u') (g++g') tau s.
Proof.
  intros *.
  intros NoSuchType NoSuchStatement.
  intros WFC.
  intros stypderivation.
  induction stypderivation;
      try (try inversion NoSuchType; 
           try inversion NoSuchExpression;
           try inversion NoSuchStatement).
Qed.

(* Can't do any subsetting with heap weakening. *)

Lemma A_4_Useless_Substitutions_1:
  forall (d : Delta) (alpha : TVar) (tau tau' : Tau) (k : Kappa),
    EmptySubsetTau tau ->
    EmptySubsetTau tau' ->
    getD d alpha = None ->
    K d tau' k ->
    subst_Tau tau' tau alpha = tau'.
Proof.
  intros *.
  intros NoSuchTypeTau NoSuchTypeTau'.
  intros H.
  intros Kderivation.
  induction Kderivation;
  try (try inversion NoSuchTypeTau; try inversion NoSuchTypeTau'). 
  induction tau0;
  try (try inversion NoSuchTypeTau; try inversion NoSuchTypeTau'). 
Qed.

Lemma A_4_Useless_Substitutions_2:
  forall (d : Delta) (alpha : TVar) (tau tau' : Tau) (g : Gamma),
    EmptySubsetTau tau ->
    EmptySubsetTau tau' ->
    getD d alpha = None ->
    WFDG d g ->
    subst_Gamma g tau alpha = g.
Proof.
  intros *.
  intros NoSuchTypeTau NoSuchTypeTau'.
  intros H.
  intros Kderivation.
  induction Kderivation;
  try (try inversion NoSuchTypeTau; try inversion NoSuchTypeTau').
  induction tau;
  try (try inversion NoSuchTypeTau; try inversion NoSuchTypeTau').
Admitted.    

Lemma A_4_Useless_Substitutions_3:
  forall (d : Delta) (alpha : TVar) (tau tau': Tau) (u : Upsilon) (p : P)
         (x : EVar),
    EmptySubsetTau tau ->
    EmptySubsetTau tau' ->    
    getD d alpha = None ->
    WFU u ->
    getU u x p = Some tau' ->
    subst_Tau tau' tau alpha = tau'.
Proof.
  intros *.
  intros NoSuchTypeTau NoSuchTypeTau'.
  intros H.
  intros WFUderivation.
  induction WFUderivation;
  try (try inversion NoSuchTypeTau; try inversion NoSuchTypeTau').
Admitted.    

Lemma A_5_Commuting_Substitutions:
  forall (alpha beta : TVar) (t0 t1 t2 : Tau),
    EmptySubsetTau t0 ->
    EmptySubsetTau t1 ->    
    EmptySubsetTau t2 ->
    NotFreeInTau beta t2 = true ->
    (subst_Tau (subst_Tau t0 t1 beta) t2 alpha) = 
    (subst_Tau (subst_Tau t0 t2 alpha)
              (subst_Tau t1 t2 alpha)
              beta).
Proof.
  intros *.
  intros NoSuchTypeT0 NoSuchTypeT1 NoSuchTypeT2.
  induction t0;
  try (try inversion NoSuchTypeT0; 
       try inversion NoSuchTypeT1;
       try inversion NoSuchTypeT2).
Qed.

Lemma A_6_Substitution_1:
  forall (d : Delta) (alpha : TVar) (tau tau' : Tau) (k k': Kappa),
    EmptySubsetTau tau ->
    EmptySubsetTau tau' ->
    AK d tau k -> 
    K (d ++ [(alpha,k)]) tau' k' ->
    K d (subst_Tau tau' tau alpha) k'.
Proof.
  intros *.
  intros NoSuchTypeTau NoSuchTypeTau'.
  intros AKderivation.
  induction AKderivation;
    try (try inversion NoSuchTypeTau; try inversion NoSuchTypeTau').
  induction tau';
    try (try inversion NoSuchTypeTau; try inversion NoSuchTypeTau').
Qed.


Lemma A_6_Substitution_2:
  forall (d : Delta) (alpha : TVar) (tau tau' : Tau) (k k': Kappa),
    EmptySubsetTau tau  ->
    EmptySubsetTau tau' ->
    AK d tau k -> 
    K (d ++ [(alpha,k)]) tau' k' ->
    AK d (subst_Tau tau' tau alpha) k'.
Proof.
  intros *.
  intros NoSuchTypeTau NoSuchTypeTau'.
  intros AKderivation.
  induction AKderivation;
    try (try inversion NoSuchTypeTau; try inversion NoSuchTypeTau').
  induction tau';
    try (try inversion NoSuchTypeTau; try inversion NoSuchTypeTau').
Qed.

Lemma A_6_Substitution_3:
  forall (d : Delta) (alpha : TVar) (tau tau' : Tau) (k : Kappa),
    EmptySubsetTau tau  ->
    EmptySubsetTau tau' ->
    AK d tau k -> 
    ASGN (d ++ [(alpha, k)]) tau' ->
    ASGN d (subst_Tau tau' tau alpha).
Proof.
  intros *.
  intros NoSuchTypeTau NoSuchTypeTau'.
  intros AKderivation.
  induction AKderivation;
    try (try inversion NoSuchTypeTau; try inversion NoSuchTypeTau').
  induction tau';
    try (try inversion NoSuchTypeTau; try inversion NoSuchTypeTau').
Qed.

Lemma A_6_Substitution_4:
  forall (d : Delta) (alpha : TVar) (tau : Tau) (g : Gamma) (k : Kappa),
    EmptySubsetTau tau  ->
    AK d tau k -> 
    WFDG (d ++ [(alpha,k)]) g ->
    WFDG d (subst_Gamma g tau alpha).
Proof.
  intros *.
  intros NoSuchTypeTau.
  intros AKderivation.
  induction AKderivation;
    try (try inversion NoSuchTypeTau; try inversion NoSuchTypeTau').
  induction tau;
    try (try inversion NoSuchTypeTau; try inversion NoSuchTypeTau').
Qed.

Lemma A_6_Substitution_5:
  forall (d : Delta) (u : Upsilon ) (alpha : TVar) (tau : Tau) 
         (g : Gamma) (k : Kappa),
    EmptySubsetTau tau  ->
    AK d tau k -> 
    WFC (d ++ [(alpha,k)]) u g ->
    WFC d u (subst_Gamma g tau alpha).
Proof.
  intros *.
  intros NoSuchTypeTau.
  intros AKderivation.
  induction AKderivation;
    try (try inversion NoSuchTypeTau; try inversion NoSuchTypeTau').
  induction tau;
    try (try inversion NoSuchTypeTau; try inversion NoSuchTypeTau').
Qed.

Lemma A_6_Substitution_6:
  forall (d : Delta) (alpha : TVar) (tau : Tau) (s : St)
         (k : Kappa),
    EmptySubsetTau tau  ->
    EmptySubsetSt s  ->
    AK d tau k -> 
    ret s ->
    ret (subst_St s tau alpha).
Proof.
  intros *.
  intros NoSuchTypeTau NoSuchStatementS.
  intros AKderivation.
  induction AKderivation;
    try (try inversion NoSuchTypeTau; try inversion NoSuchStatementS).
  induction tau;
    try (try inversion NoSuchTypeTau; try inversion NoSuchStatementS).
Qed.

Lemma A_6_Substitution_7:
  forall (d: Delta) (u : Upsilon ) (alpha : TVar) (x : EVar) 
         (t1 t2 tau : Tau) (p p': P) (k : Kappa),
    EmptySubsetTau t1 ->
    EmptySubsetTau t2 ->
    EmptySubsetTau tau ->
    AK d tau k -> 
    WFU u ->
    gettype u x p t1 p' = Some t2 ->
    gettype u x p (subst_Tau t1 tau alpha) p' = 
    Some (subst_Tau t2 tau alpha).
Proof.
  intros *.
  intros NoSuchTypeT1 NoSuchTypeT2 NoSuchTypeTau.
  intros AKderivation.
  induction AKderivation;
    try (try inversion NoSuchTypeTau;
         try inversion NoSuchTypeT1;
         try inversion NoSuchTypeT2).
  intros W.
  intros gettypederviation;
    try (try inversion NoSuchTypeTau;
         try inversion NoSuchTypeT1;
         try inversion NoSuchTypeT2).
Admitted.    

Lemma A_6_Substitution_8_1:
  forall (d : Delta) (alpha : TVar) (u : Upsilon) (g : Gamma) 
         (e : E) (tau tau' : Tau) (k : Kappa),
    EmptySubsetTau tau ->
    EmptySubsetTau tau' ->
    EmptySubsetE e ->
    AK d tau k ->
    ltyp (d ++ [(alpha,k)]) u g  e tau' ->
    ltyp d u (subst_Gamma g tau alpha)
              (subst_E e tau alpha)
              (subst_Tau tau' tau alpha).
Proof.
  intros *.
  intros NoSuchTypeTau NoSuchTypeTau' NoSuchExpressionE.
  intros AKderivation.
  intros ltypederivation.
  induction AKderivation; induction ltypederivation;
    try (try inversion NoSuchTypeTau;
         try inversion NoSuchTypeTau';
         try inversion NoSuchExpressionE).
Qed.

Lemma A_6_Substitution_8_2:
  forall (d : Delta) (alpha : TVar) (u : Upsilon) (g : Gamma) 
         (e : E) (tau tau' : Tau) (k : Kappa),
    EmptySubsetTau tau ->
    EmptySubsetTau tau' ->
    EmptySubsetE e ->
    AK d tau k ->
    rtyp (d ++ [(alpha,k)]) u g  e tau' ->
    rtyp d u (subst_Gamma g tau alpha)
              (subst_E e tau alpha)
              (subst_Tau tau' tau alpha).
Proof.
  intros *.
  intros NoSuchTypeTau NoSuchTypeTau' NoSuchExpressionE.
  intros AKderivation.
  intros ltypederivation.
  induction AKderivation; induction ltypederivation;
    try (try inversion NoSuchTypeTau;
         try inversion NoSuchTypeTau';
         try inversion NoSuchExpressionE).
Qed.

Lemma A_6_Substitution_8_3:
  forall (d : Delta) (alpha : TVar) (u : Upsilon) (g : Gamma) 
         (s : St) (tau tau' : Tau) (k : Kappa),
    EmptySubsetTau tau ->
    EmptySubsetTau tau' ->
    EmptySubsetSt s ->
    AK d tau k ->
    styp (d ++ [(alpha,k)]) u g tau' s ->
    styp d u (subst_Gamma g tau alpha)
              (subst_Tau tau' tau alpha)
              (subst_St s tau alpha).
Proof.
  intros *.
  intros NoSuchTypeTau NoSuchTypeTau' NoSuchStatementS.
  intros AKderivation.
  intros stypederivation.
  induction AKderivation; induction stypederivation;
    try (try inversion NoSuchTypeTau;
         try inversion NoSuchTypeTau';
         try inversion NoSuchStatementS).
Qed.

Lemma A_7_Typing_Well_Formedness_1 :
  forall (d: Delta) (u : Upsilon) (x : EVar) (tau tau' : Tau) (p p' : P),
    EmptySubsetTau tau ->
    EmptySubsetTau tau' ->
    WFU u ->
    gettype u x p tau p' = Some tau' ->
    K d tau A ->
    K d tau' A.
Proof.
  intros *.
  intros NoSuchTypeTau NoSuchTypeTau'.
  functional induction (gettype u x p tau p');
    try (try inversion NoSuchTypeTau;
         try inversion NoSuchTypeTau').    
Qed.

Lemma A_7_Typing_Well_Formedness_2 :
  forall (d: Delta) (g : Gamma) (u : Upsilon) (tau : Tau) (e : E),
    EmptySubsetTau tau ->
    EmptySubsetE   e ->
    ltyp d u g e tau ->
    (WFC d u g /\ 
     K d tau A).
Proof.
  (* Simultaneous induction does not seem to be used here. *)
  intros *.
  intros NoSuchType NoSuchExpression.
  intros ltypderivation.
  induction ltypderivation;
    try (try inversion NoSuchType; try inversion NoSuchExpression).
Qed.

Lemma A_7_Typing_Well_Formedness_3 :
  forall (d: Delta) (g : Gamma) (u : Upsilon) (tau : Tau) (e : E),
    EmptySubsetTau tau ->
    EmptySubsetE   e ->
    rtyp d u g e tau ->
    (WFC d u g /\ 
     K d tau A).
Proof.
  intros *.
  intros NoSuchType NoSuchExpression.
  intros rtypderivation.
  induction rtypderivation;
    try (try inversion NoSuchType; try inversion NoSuchExpression).
Qed.

Lemma A_7_Typing_Well_Formedness_4 :
  forall (d: Delta) (g : Gamma) (u : Upsilon) (tau : Tau) (s : St),
    EmptySubsetTau tau ->
    EmptySubsetSt  s ->
    styp d u g tau s ->
    WFC d u g.
Proof.
  intros *.
  intros NoSuchType NoSuchStatement.
  intros stypderivation.
  induction stypderivation;
    try (try inversion NoSuchType; try inversion NoSuchStatement).
Qed.

Lemma A_7_Typing_Well_Formedness_5 :
  forall (d: Delta) (g : Gamma) (u : Upsilon) (tau : Tau) (s : St),
    EmptySubsetTau tau ->
    EmptySubsetSt  s ->
    styp d u g tau s ->
    ret s ->
    K d tau A.
Proof.
  intros *.
  intros NoSuchType NoSuchStatement.
  intros stypderivation retderivation.
  induction stypderivation; induction retderivation;
    try (try inversion NoSuchType; try inversion NoSuchStatement).
Qed.

Lemma A_8_Return_Preservation:
  forall (s s' : St) (h h' : H),
  EmptySubsetSt  s ->
  EmptySubsetSt  s' ->
  ret s ->
  S h s h' s' ->
  ret s'.
Proof.
  intros *.
  intros NoSuchStatementS NoSuchStatementS'.
  intros r.
  intros S.
  (* TODO this does not match Dan's induction on the S derivation. *)
  induction s';
    try (try inversion NoSuchStatementS;
         try inversion NoSuchStatementS').
Qed.

Lemma A_9_Cannonical_Forms_1:
  forall (u : Upsilon) (g : Gamma) (v : E) (tau : Tau),
    EmptySubsetTau tau ->
    EmptySubsetE   v ->
    rtyp [] u g v tau ->
    Value v ->
    tau = cint -> 
    exists z : Z, v = (i_e (i_i z)).
Proof.
  (* TODO is this inspection on rtyp and Value v? *)
  intros *.
  intros NoSuchType NoSuchExpression.
  intros R V T.
  destruct tau; 
    try (try inversion NoSuchType;
         try inversion NoSuchExpression).
Qed.

(* The other six are going to be identical. *)

Lemma A_10_Path_Extension_1_A:
  forall (v v0 v1 : E) (p : P),
    EmptySubsetE   v ->
    EmptySubsetE   v0 ->
    EmptySubsetE   v1 ->
    Value v ->
    Value v0 ->
    Value v1 -> 
    get v p (cpair v0 v1) ->
    get v (p ++ [i_pe (i_i 0)]) v0 /\ 
    get v (p ++ [i_pe (i_i 1)]) v1.
Proof.
  intros *.
  intros NoSuchExpressionv NoSuchExpressionv0 NoSuchExpressionv1.
  induction p.
  (* How do I induct on the length of a list ? *)
Admitted.


(* The induction is on htyp and refp simultaneously. *)
Lemma A_14_Term_Progress_1:
  forall (g : Gamma) (u : Upsilon) (h : H) (e : E) (tau : Tau),
    htyp u g h g ->
    refp h u ->
    (ltyp [] u g e tau -> 
     (exists (x : EVar) (p : P), e = (p_e x p) \/
      exists (h' : H) (e' : E),  L h (e_s e) h' (e_s e'))).
Proof.
  intros g u h e tau.
  intros H.
  induction H.
  intros R.
  induction R.
  (* Not a good test on mutual induction. *)
Admitted.
