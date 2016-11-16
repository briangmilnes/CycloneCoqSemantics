(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION".   Daniel Grossman, August 2003 *)
(* Testing { x ?> y } tm open/close notations. *)
(* Brian Milnes 2016 *)

Set Implicit Arguments.
Require Export Cyclone_LN_Open_Close.
Open Scope cyclone_scope.

Example open_notation_1:
  forall t alpha tm, { t ttvt>    alpha } tm = tm.

Example open_notation_2:
  forall t alpha tm, { t ttvt_v>  alpha } tm = tm.

Example open_notation_3:
  forall t alpha tm, { t ttvt_e>  alpha } tm = tm.

Example open_notation_4:
  forall t alpha tm, { t ttvt_st> alpha } tm = tm.

Example open_notation_5:
  forall t alpha tm, { t ttvt_f>  alpha } tm = tm.

Example open_notation_6:
  forall t alpha tm, {t ttvtm> alpha } tm = tm.

Example open_notation_7:
  forall x y tm, { x vvtm_v> y } tm = tm.

Example open_notation_8:
  forall x y tm, { x vvtm_e> y } tm = tm.

Example open_notation_8:
  forall x y tm, { x vvtm_st> y } tm = tm.

Example open_notation_8:
  forall x y tm, { x vvtm_f> y } tm = tm.

Example open_notation_8:
  forall x y tm, { x vvtm> y } tm = tm.
