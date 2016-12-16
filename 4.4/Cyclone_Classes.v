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

Hint Unfold lc'.
Typeclasses Transparent LcVJudgement LcStJudgement LcEJudgement LcFJudgement LcTermJudgement LcTauVJudgement LcTauStJudgement LcTauEJudgement LcTauFJudgement LcTauTermJudgement.
End CC.

(* Coq bug: only the first one of these works. *)
(* Ask Stuart. *)
Hint Extern 1 (_ \notin fv' _)         => autounfold; repeat simpl.
Hint Extern 1 (open_rec' _ _ _ = _)  =>  autounfold; repeat simpl.
Hint Extern 1 ((close_rec' _ _ _) = _) => autounfold; repeat simpl.
Hint Extern 1 ((subst' _ _ _) = _)     => autounfold; repeat simpl.

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
     end.

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
       |  |- context[LcTauTermJudgement ]       => unfold LcTauTermJudgement      end.

Ltac simpl_classes := simpl_classes_prop; simpl_classes_funs; simpl_classes_classes.

(* Old
Ltac us_1 A := unfold A; simpl.
Ltac us_2 P A := unfold P; unfold A; simpl.
Ltac us_in_1 A H := unfold A in H; simpl in H.
Ltac us_in_2 P A H := unfold P in H; unfold A in H; simpl in H.
Ltac aus := autounfold in *; simpl in *.

Ltac simpl_classes :=
   repeat 
     match goal with
       | H : context[fv' _ ] |- _ => us_in_1 fv' H
       |  |- context[fv' _]      => us_1 fv'

       | H : context[open_rec' _ _  _ ] |- _ => us_in_1 open_rec' H
       |  |- context[open_rec' _ _ _]      => us_1 open_rec'

       | H : context[close_rec' _ _ _ ] |- _ => us_in_1 close_rec' H
       |  |- context[close_rec' _ _ _ ]      => us_2 close_rec'

       | H : context[subst' _ _ _] |- _ => us_in_1 subst' H
       |  |- context[subst' _ _ _]      => us_1 subst'

       | H : context[lc' _ ] |- _ => us_in_1 lc' H
       |  |- context[lc' _]      => us_1 lc'

       | H : context[?P _ TauLangFuns _] |- _ => us_in_2 P TauLangFuns H
       |  |- context[?P _ TauLangFuns _]      => us_2 P TauLangFuns

       | H : context[?P _ _ VLangFuns _] |- _  => us_in_2 P VLangFuns H
       |  |- context[?P _ _ VLangFuns _]       => us_2 P VLangFuns

       | H : context[?P _ _ StLangFuns _] |- _  => us_in_2 P StLangFuns H
       |  |- context[?P _ _ StLangFuns _]       => us_2 P StLangFuns

       | H : context[?P _ _ ELangFuns _] |- _  => us_in_2 P ELangFuns H
       |  |- context[?P _ _ ELangFuns _]       => us_2 P ELangFuns

       | H : context[?P _ _ FLangFuns _] |- _  => us_in_2 P FLangFuns H
       |  |- context[?P _ _ FLangFuns _]       => us_2 P FLangFuns

       | H : context[?P _ _ TermLangFuns _] |- _  => us_in_2 P TermLangFuns H
       |  |- context[?P _ _ TermLangFuns _]       => us_2 P TermLangFuns

       | H : context[?P _ VLangFuns _] |- _  => us_in_2 P VLangFuns H
       |  |- context[?P _ VLangFuns _]       => us_2 P VLangFuns

       | H : context[?P _ StLangFuns _] |- _  => us_in_2 P StLangFuns H
       |  |- context[?P _ StLangFuns _]       => us_2 P StLangFuns

       | H : context[?P _ ELangFuns _] |- _  => us_in_2 P ELangFuns H
       |  |- context[?P _ ELangFuns _]       => us_2 P ELangFuns

       | H : context[?P _ FLangFuns _] |- _  => us_in_2 P FLangFuns H
       |  |- context[?P _ FLangFuns _]       => us_2 P FLangFuns

       | H : context[?P _ TermLangFuns _] |- _  => us_in_2 P TermLangFuns H
       |  |- context[?P _ TermLangFuns _]       => us_2 P TermLangFuns

       | H : context[?P _ TauTermVLangFuns _] |- _  => us_in_2 P TauTermVLangFuns H
       |  |- context[?P _ TauTermVLangFuns _]       => us_2 P TauTermVLangFuns

       | H : context[?P _ TauTermStLangFuns _] |- _  => us_in_2 P TauTermStLangFuns H
       |  |- context[?P _ TauTermStLangFuns _]       => us_2 P TauTermStLangFuns

       | H : context[?P _ TauTermELangFuns _] |- _  => us_in_2 P TauTermELangFuns H
       |  |- context[?P _ TauTermELangFuns _]       => us_2 P TauTermELangFuns

       | H : context[?P _ TauTermFLangFuns _] |- _  => us_in_2 P TauTermFLangFuns H
       |  |- context[?P _ TauTermFLangFuns _]       => us_2 P TauTermFLangFuns

       | H : context[?P _ TauTermTauLangFuns _] |- _  => us_in_2 P TauTermTauLangFuns H
       |  |- context[?P _ TauTermTauLangFuns _]       => us_2 P TauTermTauLangFuns

       | H : context[?P _ TauTermLangFuns _] |- _  => us_in_2 P TauTermLangFuns H
       |  |- context[?P _ TauTermLangFuns _]       => us_2 P TauTermLangFuns

       | H : context[?P _ _ _ LcVJudgement _] |- _  => us_in_2 P LcVJudgement H
       |  |- context[?P _ _ _ LcVJudgement _]       => us_2 P LcVJudgement

       | H : context[?P _ _ _ LcStJudgement _] |- _  => us_in_2 P LcStJudgement H
       |  |- context[?P _ _ _ LcStJudgement _]       => us_2 P LcStJudgement

       | H : context[?P _ _ _ LcEJudgement _] |- _  => us_in_2 P LcEJudgement H
       |  |- context[?P _ _ _ LcEJudgement _]       => us_2 P LcEJudgement

       | H : context[?P _ _ _ LcFJudgement _] |- _  => us_in_2 P LcFJudgement H
       |  |- context[?P _ _ _ LcFJudgement _]       => us_2 P LcFJudgement

       | H : context[?P _ _ _ LcTermJudgement _] |- _  => us_in_2 P LcTermJudgement H
       |  |- context[?P _ _ _ LcTermJudgement _]       => us_2 P LcTermJudgement
                                                      
     end.
*) 

(* 
  match goal with 
    |  |- context[?P _ _ _ ?X]      => 
      match type of X with V => idtac "matched" end
    end.

Alas this won't match a class. 

Ltac simpl_classes :=
   repeat 
     match goal with
       | H : context[fv' _ ] |- _ => us_in_1 fv' H
       |  |- context[fv' _]      => us_1 fv'

       | H : context[open_rec' _ _  _ ] |- _ => us_in_1 open_rec' H
       |  |- context[open_rec' _ _ _]      => us_1 open_rec'

       | H : context[close_rec' _ _ _ ] |- _ => us_in_1 close_rec' H
       |  |- context[close_rec' _ _ _ ]      => us_2 close_rec'

       | H : context[subst' _ _ _] |- _ => us_in_1 subst' H
       |  |- context[subst' _ _ _]      => us_1 subst'

       | H : context[lc' _ ] |- _ => us_in_1 lc' H
       |  |- context[lc' _]      => us_1 lc'

       | H : context[?P _ _ ?X _] |- _ => 
         match type of X with LangFuns => us_in_2 P X H end
       |  |- context[?P _ _ ?X _]      => 
         match type of X with LangFuns => us_in_2 P X end

       | H : context[?P _ _ _ ?X _] |- _  => 
         match type of X with LcJudgement => us_in_2 P X H end
       |  |- context[?P _ _ _ ?X _]       => 
         match type of X with LcJudgement => us_in_2 P X end
end.
*)

Ltac auto_tilde ::= simpl_classes; try invert_x_notin_x; intuition eauto.
Ltac auto_star  ::= simpl_classes; try invert_x_notin_x; auto_star_default.
