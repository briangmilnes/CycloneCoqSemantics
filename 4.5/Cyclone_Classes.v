(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION".   Daniel Grossman, August 2003 *)
(* Type classes to allow simpler proof construction. *)
(* Brian Milnes 2016 *)

Set Implicit Arguments.
Require Export Cyclone_LN_Types Cyclone_LN_Terms Cyclone_LN_Types_In_Terms Cyclone_LN_Tactics.

Section CC.
Class LangFuns (What ForWhat In: Type) := {
    fv'        : In -> fset Variables.var;
    subst'     : What -> var -> In -> In;
    open_rec'  : nat -> ForWhat -> In -> In;
    close_rec' : nat -> var -> In -> In;
    size'      : In -> nat}.

(* Types *)
Instance TauLangFuns : LangFuns Tau Tau Tau := {
    fv'        := T.fv;
    subst'     := T.subst;
    open_rec'  := T.open_rec;
    close_rec' := T.close_rec;
    size'      := T.size }.

(* Terms *)
Instance VLangFuns : LangFuns var var V := {
    fv'        := TM.fv_v;
    subst'     := TM.subst_v;
    open_rec'  := TM.open_rec_v;
    close_rec' := TM.close_rec_v;
    size'      := TM.size_v }.

Instance StLangFuns : LangFuns var var St := {
    fv'        := TM.fv_st;
    subst'     := TM.subst_st;
    open_rec'  := TM.open_rec_st;
    close_rec' := TM.close_rec_st;
    size'      := TM.size_st }.

Instance ELangFuns : LangFuns var var E := {
    fv'        := TM.fv_e;
    subst'     := TM.subst_e;
    open_rec'  := TM.open_rec_e;
    close_rec' := TM.close_rec_e;
    size'      := TM.size_e }.

Instance FLangFuns : LangFuns var var F := {
    fv'        := TM.fv_f;
    subst'     := TM.subst_f;
    open_rec'  := TM.open_rec_f;
    close_rec' := TM.close_rec_f;
    size'      := TM.size_f }.

(* Types in Terms. *)

Instance TermLangFuns : LangFuns var var Term := {
    fv'        := TM.fv;
    subst'     := TM.subst;
    open_rec'  := TM.open_rec;
    close_rec' := TM.close_rec;
    size'      := TM.size }.

Instance TauTermVLangFuns : LangFuns Tau Tau V := {
    fv'        := TTM.fv_v;
    subst'     := TTM.subst_v;
    open_rec'  := TTM.open_rec_v; 
    close_rec' := TTM.close_rec_v;
    size'      := TM.size_v }.

Instance TauTermStLangFuns : LangFuns Tau Tau St := {
    fv'        := TTM.fv_st;
    subst'     := TTM.subst_st;
    open_rec'  := TTM.open_rec_st;
    close_rec' := TTM.close_rec_st;
    size'      := TM.size_st }.

Instance TauTermELangFuns : LangFuns Tau Tau E := {
    fv'        := TTM.fv_e;
    subst'     := TTM.subst_e;
    open_rec'  := TTM.open_rec_e;
    close_rec' := TTM.close_rec_e;
    size'      := TM.size_e}.

Instance TauTermFLangFuns : LangFuns Tau Tau F := {
    fv'        := TTM.fv_f;
    subst'     := TTM.subst_f;
    open_rec'  := TTM.open_rec_f;
    close_rec' := TTM.close_rec_f;
    size'      := TM.size_f }.

Instance TauTermTauLangFuns : LangFuns Tau Tau Tau := {
    fv'        := T.fv;
    subst'     := T.subst;
    open_rec'  := T.open_rec;
    close_rec' := T.close_rec;
    size'      := T.size }.

Instance TauTermLangFuns : LangFuns Tau Tau Term := {
    fv'        := TTM.fv;
    subst'     := TTM.subst;
    open_rec'  := TTM.open_rec;
    close_rec' := TTM.close_rec;
    size'      := TM.size }.

Hint Unfold fv'.
Hint Unfold subst'.
Hint Unfold open_rec'.
Hint Unfold close_rec'.
Typeclasses Transparent TauLangFuns VLangFuns StLangFuns ELangFuns FLangFuns TermLangFuns TauTermStLangFuns TauTermELangFuns TauTermFLangFuns TauTermTauLangFuns TauTermLangFuns fv' subst' open_rec' close_rec'.

Class LcJudgement (In: Type) := { lc' : In -> Prop }.

Instance LcVJudgement    : LcJudgement V    := { lc' := TM.lc_v}.
Instance LcStJudgement   : LcJudgement St   := { lc' := TM.lc_st}.
Instance LcEJudgement    : LcJudgement E    := { lc' := TM.lc_e}.
Instance LcFJudgement    : LcJudgement F    := { lc' := TM.lc_f}.
Instance LcTauJudgement  : LcJudgement Tau  := { lc' := T.lc}.
Instance LcTermJudgement : LcJudgement Term := { lc' := TM.lc}.

Instance LcTauVJudgement    : LcJudgement V    := { lc' := TTM.lc_v}.
Instance LcTauStJudgement   : LcJudgement St   := { lc' := TTM.lc_st}.
Instance LcTauEJudgement    : LcJudgement E    := { lc' := TTM.lc_e}.
Instance LcTauFJudgement    : LcJudgement F    := { lc' := TTM.lc_f}.
Instance LcTauTermJudgement : LcJudgement Term := { lc' := TTM.lc}.

Class TypJudgement (In: Type) := { typ' : Delta -> Upsilon -> Gamma -> In -> Tau -> Prop }.

Instance RtypJudgement : TypJudgement E  := {typ' := rtyp}.
Instance LtypJudgement : TypJudgement E  := {typ' := ltyp}.
Instance StypJudgement : TypJudgement St := {typ' := styp}.

Hint Unfold lc'.
Typeclasses Transparent LcVJudgement LcStJudgement LcEJudgement LcFJudgement LcTermJudgement LcTauVJudgement LcTauStJudgement LcTauEJudgement LcTauFJudgement LcTauTermJudgement RtypJudgement LtypJudgement StypJudgement.
End CC.

(* Coq bug: only the first one of these works. *)
(* Ask Stuart. *)
Hint Extern 1 (_ \notin fv' _)         => idtac "(_ \notin fv' _)"; trace_goal; autounfold; repeat simpl.
Hint Extern 1 (open_rec' _ _ _ = _)  => idtac "(open_rec' _ _ _ = _)"; trace_goal;  autounfold; repeat simpl.
Hint Extern 1 ((close_rec' _ _ _) = _) => idtac "((close_rec' _ _ _) = _)"; trace_goal; autounfold; repeat simpl.
Hint Extern 1 ((subst' _ _ _) = _)     => idtac "((subst' _ _ _) = _)"; trace_goal; autounfold; repeat simpl.

Ltac simpl_classes_prop:=
   repeat 
     match goal with
       | H : context[?P _ TauLangFuns _] |- _ => unfold P in H
       |  |- context[?P _ TauLangFuns _]      => unfold P

       | H : context[?P _ _ VLangFuns _] |- _  => unfold P in H
       |  |- context[?P _ _ VLangFuns _]       => unfold P

       | H : context[?P _ _ StLangFuns _] |- _  => unfold P in H
       |  |- context[?P _ _ StLangFuns _]       => unfold P

       | H : context[?P _ _ ELangFuns _] |- _  => unfold P in H
       |  |- context[?P _ _ ELangFuns _]       => unfold P

       | H : context[?P _ _ FLangFuns _] |- _  => unfold P in H
       |  |- context[?P _ _ FLangFuns _]       => unfold P

       | H : context[?P _ _ TermLangFuns _] |- _  => unfold P in H
       |  |- context[?P _ _ TermLangFuns _]       => unfold P

       | H : context[?P _ VLangFuns _] |- _  => unfold P in H
       |  |- context[?P _ VLangFuns _]       => unfold P

       | H : context[?P _ StLangFuns _] |- _  => unfold P in H
       |  |- context[?P _ StLangFuns _]       => unfold P

       | H : context[?P _ ELangFuns _] |- _  => unfold P in H
       |  |- context[?P _ ELangFuns _]       => unfold P

       | H : context[?P _ FLangFuns _] |- _  => unfold P in H
       |  |- context[?P _ FLangFuns _]       => unfold P

       | H : context[?P _ TermLangFuns _] |- _  => unfold P in H
       |  |- context[?P _ TermLangFuns _]       => unfold P

       | H : context[?P _ TauTermVLangFuns _] |- _  => unfold P in H
       |  |- context[?P _ TauTermVLangFuns _]       => unfold P

       | H : context[?P _ TauTermStLangFuns _] |- _  => unfold P in H
       |  |- context[?P _ TauTermStLangFuns _]       => unfold P

       | H : context[?P _ TauTermELangFuns _] |- _  => unfold P in H
       |  |- context[?P _ TauTermELangFuns _]       => unfold P

       | H : context[?P _ TauTermFLangFuns _] |- _  => unfold P in H
       |  |- context[?P _ TauTermFLangFuns _]       => unfold P

       | H : context[?P _ TauTermTauLangFuns _] |- _  => unfold P in H
       |  |- context[?P _ TauTermTauLangFuns _]       => unfold P

       | H : context[?P _ TauTermLangFuns _] |- _  => unfold P in H
       |  |- context[?P _ TauTermLangFuns _]       => unfold P

       | H : context[?P _ _ _ LcVJudgement _] |- _  => unfold P in H
       |  |- context[?P _ _ _ LcVJudgement _]       => unfold P

       | H : context[?P _ _ _ LcStJudgement _] |- _  => unfold P in H
       |  |- context[?P _ _ _ LcStJudgement _]       => unfold P

       | H : context[?P _ _ _ LcEJudgement _] |- _  => unfold P in H
       |  |- context[?P _ _ _ LcEJudgement _]       => unfold P

       | H : context[?P _ _ _ LcFJudgement _] |- _  => unfold P in H
       |  |- context[?P _ _ _ LcFJudgement _]       => unfold P

       | H : context[?P _ _ _ LcTermJudgement _] |- _  => unfold P in H
       |  |- context[?P _ _ _ LcTermJudgement _]       => unfold P

       | H : context[?P _ _ _ LcTauVJudgement _] |- _  => unfold P in H
       |  |- context[?P _ _ _ LcTauVJudgement _]       => unfold P

       | H : context[?P _ _ _ LcTauStJudgement _] |- _  => unfold P in H
       |  |- context[?P _ _ _ LcTauStJudgement _]       => unfold P

       | H : context[?P _ _ _ LcTauEJudgement _] |- _  => unfold P in H
       |  |- context[?P _ _ _ LcTauEJudgement _]       => unfold P

       | H : context[?P _ _ _ LcTauFJudgement _] |- _  => unfold P in H
       |  |- context[?P _ _ _ LcTauFJudgement _]       => unfold P

       | H : context[?P _ _ _ LcTauTermJudgement _] |- _  => unfold P in H
       |  |- context[?P _ _ _ LcTauTermJudgement _]       => unfold P

       | H : context[?P _ RtypJudgement _ _ _ _ _ _]|- _  => unfold P in H
       |  |- context[?P _ RtypJudgement _ _ _ _ _ _]      => unfold P

       | H : context[?P _ LtypJudgement _ _ _ _ _ _]|- _  => unfold P in H
       |  |- context[?P _ LtypJudgement _ _ _ _ _ _]      => unfold P                                                                  
       | H : context[?P _ StypJudgement _ _ _ _ _ _]|- _  => unfold P in H
       |  |- context[?P _ StypJudgement _ _ _ _ _ _]      => unfold P
end.                                                      

Ltac simpl_classes_funs :=
   repeat 
     match goal with
       | H : context[fv' _ ] |- _ => unfold fv' in H
       |  |- context[fv' _]      => unfold fv'

       | H : context[open_rec' _ _  _ ] |- _ => unfold open_rec' in H
       |  |- context[open_rec' _ _ _]      => unfold open_rec'

       | H : context[close_rec' _ _ _ ] |- _ => unfold close_rec' in H
       |  |- context[close_rec' _ _ _ ]      => unfold close_rec'

       | H : context[subst' _ _ _] |- _ => unfold subst' in H
       |  |- context[subst' _ _ _]      => unfold subst'

       | H : context[lc' _ ] |- _ => unfold lc' in H
       |  |- context[lc' _]      => unfold lc'

       | H : context[typ' _ _ _ _ _] |- _ => unfold typ' in H
       |  |- context[typ' _ _ _ _ _]      => unfold typ'
     end.

(* Bug: can be simplified with type of match. *)
Ltac simpl_classes_classes :=
  repeat
    match goal with
       | H : context[TauLangFuns ] |- _ => unfold TauLangFuns in H
       |  |- context[TauLangFuns ]      => unfold TauLangFuns

       | H : context[ VLangFuns ] |- _  => unfold  VLangFuns in H
       |  |- context[ VLangFuns ]       => unfold  VLangFuns

       | H : context[ StLangFuns ] |- _  => unfold  StLangFuns in H
       |  |- context[ StLangFuns ]       => unfold  StLangFuns

       | H : context[ ELangFuns ] |- _  => unfold  ELangFuns in H
       |  |- context[ ELangFuns ]       => unfold  ELangFuns

       | H : context[ FLangFuns ] |- _  => unfold  FLangFuns in H
       |  |- context[ FLangFuns ]       => unfold  FLangFuns

       | H : context[ TermLangFuns ] |- _  => unfold  TermLangFuns in H
       |  |- context[ TermLangFuns ]       => unfold  TermLangFuns

       | H : context[VLangFuns ] |- _  => unfold VLangFuns in H
       |  |- context[VLangFuns ]       => unfold VLangFuns

       | H : context[StLangFuns ] |- _  => unfold StLangFuns in H
       |  |- context[StLangFuns ]       => unfold StLangFuns

       | H : context[ELangFuns ] |- _  => unfold ELangFuns in H
       |  |- context[ELangFuns ]       => unfold ELangFuns

       | H : context[FLangFuns ] |- _  => unfold FLangFuns in H
       |  |- context[FLangFuns ]       => unfold FLangFuns

       | H : context[TermLangFuns ] |- _  => unfold TermLangFuns in H
       |  |- context[TermLangFuns ]       => unfold TermLangFuns

       | H : context[TauTermVLangFuns ] |- _  => unfold TauTermVLangFuns in H
       |  |- context[TauTermVLangFuns ]       => unfold TauTermVLangFuns

       | H : context[TauTermStLangFuns ] |- _  => unfold TauTermStLangFuns in H
       |  |- context[TauTermStLangFuns ]       => unfold TauTermStLangFuns

       | H : context[TauTermELangFuns ] |- _  => unfold TauTermELangFuns in H
       |  |- context[TauTermELangFuns ]       => unfold TauTermELangFuns

       | H : context[TauTermFLangFuns ] |- _  => unfold TauTermFLangFuns in H
       |  |- context[TauTermFLangFuns ]       => unfold TauTermFLangFuns

       | H : context[TauTermTauLangFuns ] |- _  => unfold TauTermTauLangFuns in H
       |  |- context[TauTermTauLangFuns ]       => unfold TauTermTauLangFuns

       | H : context[TauTermLangFuns ] |- _  => unfold TauTermLangFuns in H
       |  |- context[TauTermLangFuns ]       => unfold TauTermLangFuns

       | H : context[LcVJudgement ] |- _ => unfold LcVJudgement in H
       |  |- context[LcVJudgement ]       => unfold LcVJudgement

       | H : context[LcStJudgement ] |- _ => unfold LcStJudgement in H
       |  |- context[LcStJudgement ]       => unfold LcStJudgement

       | H : context[LcEJudgement ] |- _ => unfold LcEJudgement in H
       |  |- context[LcEJudgement ]       => unfold LcEJudgement

       | H : context[LcFJudgement ] |- _ => unfold LcFJudgement in H
       |  |- context[LcFJudgement ]       => unfold LcFJudgement

       | H : context[LcTermJudgement ] |- _ => unfold LcTermJudgement in H
       |  |- context[LcTermJudgement ]       => unfold LcTermJudgement      

       | H : context[LcTauVJudgement ] |- _ => unfold LcTauVJudgement in H
       |  |- context[LcTauVJudgement ]       => unfold LcTauVJudgement

       | H : context[LcTauStJudgement ] |- _ => unfold LcTauStJudgement in H
       |  |- context[LcTauStJudgement ]       => unfold LcTauStJudgement

       | H : context[LcTauEJudgement ] |- _ => unfold LcTauEJudgement in H
       |  |- context[LcTauEJudgement ]       => unfold LcTauEJudgement

       | H : context[LcTauFJudgement ] |- _ => unfold LcTauFJudgement in H
       |  |- context[LcTauFJudgement ]       => unfold LcTauFJudgement

       | H : context[LcTauTermJudgement ] |- _ => unfold LcTauTermJudgement in H
       |  |- context[LcTauTermJudgement ]       => unfold LcTauTermJudgement

       | H : context[RtypJudgement ] |- _ => unfold RtypJudgement in H
       |  |- context[RtypJudgement ]      => unfold RtypJudgement

       | H : context[StypJudgement ] |- _ => unfold StypJudgement in H
       |  |- context[StypJudgement ]      => unfold StypJudgement

       | H : context[LtypJudgement ] |- _ => unfold LtypJudgement in H
       |  |- context[LtypJudgement ]      => unfold LtypJudgement
end.

Ltac simpl_classes := simpl_classes_prop; simpl_classes_funs; simpl_classes_classes.

Ltac auto_tilde ::= simpl_classes; try invert_x_notin_x; intuition eauto.
Ltac auto_star  ::= simpl_classes; try invert_x_notin_x; auto_star_default.
