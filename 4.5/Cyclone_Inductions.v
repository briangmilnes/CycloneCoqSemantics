(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION".   Daniel Grossman, August 2003 *)
(* Induction setups. *)
(* Brian Milnes 2016 *)

Set Implicit Arguments.
Require Export Cyclone_Classes.

(* Some syntactic sugar for sub lemmas. *)
Ltac lemma T :=  assert(T); autounfold; simpl.

Tactic Notation "prove" ident(L) "using" tactic(T) "qed" :=
  abstract T using L.

Ltac StEF_Induction M P :=
  apply (M
           (P var St StLangFuns)
           (P var E  ELangFuns)
           (P var F  FLangFuns));
  simpl_classes.

Ltac StEF_Var_Induction M P :=
  apply (M
           (P St StLangFuns)
           (P E ELangFuns)
           (P F FLangFuns));
  simpl_classes.

Ltac StEF_Tau_Var_Induction M P :=
  apply (M
           (P St  TauTermStLangFuns)
           (P E   TauTermELangFuns)
           (P F   TauTermFLangFuns)
           (P Tau TauLangFuns)); 
  simpl_classes.


Ltac StEF_Tau_Induction M P :=
  apply (M
           (P St  TauTermStLangFuns)
           (P E   TauTermELangFuns)
           (P F   TauTermFLangFuns)
           (P Tau TauLangFuns)); 
  simpl_classes.

Ltac StEF_Tau_Induction' M P :=
  apply (M
           (P St  TauTermStLangFuns)
           (P E   TauTermELangFuns)
           (P F   TauTermFLangFuns)
           (P Tau TauLangFuns)).

Ltac LCSt_Induction M P :=
  apply (M
           (P var St StLangFuns LcStJudgement)
           (P var E  ELangFuns  LcEJudgement)
           (P var F  FLangFuns  LcFJudgement));
  simpl_classes.

Ltac LCSt_Tau_Induction M P :=
  apply (M
           (P St TauTermStLangFuns LcTauStJudgement)
           (P E TauTermELangFuns  LcTauEJudgement)
           (P F TauTermFLangFuns  LcTauFJudgement));
  simpl_classes.

Ltac Typ_Induction M P :=
  apply (M
           (P St StypJudgement)
           (P E LtypJudgement) 
           (P E RtypJudgement));
  simpl_classes.