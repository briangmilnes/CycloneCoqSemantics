(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  This defines case auxiliary checks so if I change any definitions then
 if their cases get changed, I'll get notifications.

*)

Require Export Case.
Require Export LanguageModule.
Require Export StaticSemantics.

Tactic Notation "Tau_ind_cases" tactic(first) ident(c) :=
  first;
[
 Case_aux c "(tv_t t)"
| Case_aux c "cint"
| Case_aux c "(cross t t0)"
| Case_aux c "(arrow t t0)"
| Case_aux c "(ptype t)"
| Case_aux c "(utype t k t0)"
| Case_aux c "(etype p t k t0)"
].

Tactic Notation "Tau_ind_cases_from_apply" tactic(first) ident(c) :=
  first;
[
 Case_aux c "(tv_t t)"
| Case_aux c "cint"
| Case_aux c "(cross t t0)"
| Case_aux c "(arrow t t0)"
| Case_aux c "(ptype t)"
| Case_aux c "(utype t k t0)"
| Case_aux c "(etype p t k t0)"
| Case_aux c "base"
].

Tactic Notation "E_ind_cases" tactic(first) ident(c) :=
  first;
[
  Case_aux c "(i_e i)"
| Case_aux c "(p_e e l)"
| Case_aux c "(f_e f1)"
| Case_aux c "(amp e)"
| Case_aux c "(star e)"
| Case_aux c "(cpair e e0)"
| Case_aux c "(dot e i)"
| Case_aux c "(assign e e0)"
| Case_aux c "(appl e e0)"
| Case_aux c "(call s)"
| Case_aux c "(inst e t)"
| Case_aux c "(pack t e t0)"
].

Tactic Notation "ltyp_ind_mutual_cases" tactic(first) ident(c) :=
  first;
[
  Case_aux c "styp_e_3_1"
 | Case_aux c "styp_return_3_2"
 | Case_aux c "styp_seq_3_3"
 | Case_aux c "styp_while_3_4"
 | Case_aux c "styp_if_3_5"
 | Case_aux c "styp_let_3_6"
 | Case_aux c "styp_open_3_7"
 | Case_aux c "styp_openstar_3_8"
 | Case_aux c "SL_3_1"
 | Case_aux c "SL_3_2"
 | Case_aux c "SL_3_3"
 | Case_aux c "SL_3_4"
 | Case_aux c "SR_3_1"
 | Case_aux c "SR_3_2"
 | Case_aux c "SR_3_3"
 | Case_aux c "SR_3_4"
 | Case_aux c "SR_3_5"
 | Case_aux c "SR_3_6"
 | Case_aux c "SR_3_7"
 | Case_aux c "SR_3_8"
 | Case_aux c "SR_3_9"
 | Case_aux c "SR_3_10"
 | Case_aux c "SR_3_11"
 | Case_aux c "SR_3_12"
 | Case_aux c "SR_3_13"
 | Case_aux c "SR_3_14"
 | Case_aux c "base"].
 
Tactic Notation "rtyp_ind_cases" tactic(first) ident(c) :=
  first;
[ Case_aux c "rtyp d u g (p_e x p) tau"
| Case_aux c "rtyp d u g (star e) tau"
| Case_aux c "rtyp d u g (dot e zero_pe) t0"
| Case_aux c "rtyp d u g (dot e one_pe) t1"
| Case_aux c "rtyp d u g (i_e (i_i z)) cint"
| Case_aux c "rtyp  d u g (amp e) (ptyp tau)"
| Case_aux c "rtyp d u g (cpair e0 e1) (cross t0 t1)"
| Case_aux c "rtyp d u g (assign e1 e2) tau"
| Case_aux c "rtyp d u g (appl e1 e2) tau"
| Case_aux c "rtyp d u g (call s) tau"
| Case_aux c "rtyp d u g (inst e tau) (subst_Tau tau' tau alpha)"
| Case_aux c "rtyp  d u g (pack tau' e (etype p alpha k tau)) (etyp p alpha k tau)"
| Case_aux c "rtyp d u g (f_e (dfun tau x tau' s)) (arrow tau tau')"
| Case_aux c "rtyp  d u g (f_e (ufun alpha k f12)) (utyp alpha k tau))"
].

Tactic Notation "rtyp_ind_mutual_cases" tactic(first) ident(c) :=
  first;
[  Case_aux c "styp_e_3_1"
 | Case_aux c "styp_return_3_2"
 | Case_aux c "styp_seq_3_3"
 | Case_aux c "styp_while_3_4"
 | Case_aux c "styp_if_3_5"
 | Case_aux c "styp_let_3_6"
 | Case_aux c "styp_open_3_7"
 | Case_aux c "styp_openstar_3_8"
 | Case_aux c "SL_3_1"
 | Case_aux c "SL_3_2"
 | Case_aux c "SL_3_3"
 | Case_aux c "SL_3_4"
 | Case_aux c "SR_3_1"
 | Case_aux c "SR_3_2"
 | Case_aux c "SR_3_3"
 | Case_aux c "SR_3_4"
 | Case_aux c "SR_3_5"
 | Case_aux c "SR_3_6"
 | Case_aux c "SR_3_7"
 | Case_aux c "SR_3_8"
 | Case_aux c "SR_3_9"
 | Case_aux c "SR_3_10"
 | Case_aux c "SR_3_11"
 | Case_aux c "SR_3_12"
 | Case_aux c "SR_3_13"
 | Case_aux c "SR_3_14"
 | Case_aux c "base" ].


Tactic Notation "rtyp_ind_mutual_cases_2base" tactic(first) ident(c) :=
  first;
[  Case_aux c "styp_e_3_1"
 | Case_aux c "styp_return_3_2"
 | Case_aux c "styp_seq_3_3"
 | Case_aux c "styp_while_3_4"
 | Case_aux c "styp_if_3_5"
 | Case_aux c "styp_let_3_6"
 | Case_aux c "styp_open_3_7"
 | Case_aux c "styp_openstar_3_8"
 | Case_aux c "SL_3_1"
 | Case_aux c "SL_3_2"
 | Case_aux c "SL_3_3"
 | Case_aux c "SL_3_4"
 | Case_aux c "SR_3_1"
 | Case_aux c "SR_3_2"
 | Case_aux c "SR_3_3"
 | Case_aux c "SR_3_4"
 | Case_aux c "SR_3_5"
 | Case_aux c "SR_3_6"
 | Case_aux c "SR_3_7"
 | Case_aux c "SR_3_8"
 | Case_aux c "SR_3_9"
 | Case_aux c "SR_3_10"
 | Case_aux c "SR_3_11"
 | Case_aux c "SR_3_12"
 | Case_aux c "SR_3_13"
 | Case_aux c "SR_3_14"
 | Case_aux c "base" 
 | Case_aux c "base2" 
].

Tactic Notation "styp_ind_cases" tactic(first) ident(c) :=
  first;
[ 
  Case_aux c "styp d u g tau (e_s e))"
| Case_aux c "styp d u g tau (retn e))"
| Case_aux c "styp d u g tau (seq s1 s2))"
| Case_aux c "styp d u g tau (while e s))"
| Case_aux c "styp d u g tau (if_s e s1 s2))"
| Case_aux c "styp d u g tau (letx x e s))"
| Case_aux c "styp d u g tau (open e alpha x s))"
| Case_aux c "styp d u g tau (openstar e alpha x s))"
].


Tactic Notation "styp_ind_mutual_cases" tactic(first) ident(c) :=
  first;
[ 
  Case_aux c "styp_e_3_1"
 | Case_aux c "styp_return_3_2"
 | Case_aux c "styp_seq_3_3"
 | Case_aux c "styp_while_3_4"
 | Case_aux c "styp_if_3_5"
 | Case_aux c "styp_let_3_6"
 | Case_aux c "styp_open_3_7"
 | Case_aux c "styp_openstar_3_8"
 | Case_aux c "SL_3_1"
 | Case_aux c "SL_3_2"
 | Case_aux c "SL_3_3"
 | Case_aux c "SL_3_4"
 | Case_aux c "SR_3_1"
 | Case_aux c "SR_3_2"
 | Case_aux c "SR_3_3"
 | Case_aux c "SR_3_4"
 | Case_aux c "SR_3_5"
 | Case_aux c "SR_3_6"
 | Case_aux c "SR_3_7"
 | Case_aux c "SR_3_8"
 | Case_aux c "SR_3_9"
 | Case_aux c "SR_3_10"
 | Case_aux c "SR_3_11"
 | Case_aux c "SR_3_12"
 | Case_aux c "SR_3_13"
 | Case_aux c "SR_3_14"
 | Case_aux c "base" ].

Tactic Notation "K_ind_cases" tactic(first) ident(c) :=
  first;
[ Case_aux c "K d cint B"
 | Case_aux c "K d (tv_t alpha) B"
 | Case_aux c "K d (ptype (tv_t alpha)) B"
 | Case_aux c "K d tau A"
 | Case_aux c "K d (cross t0 t1) A"
 | Case_aux c "K d (arrow t0 t1) A"
 | Case_aux c "K d (ptype tau) B"
 | Case_aux c "K d (utype alpha k tau) A"
 | Case_aux c "K d (etype p alpha k tau) A)"
].

Tactic Notation "WFU_ind_cases" tactic(first) ident(c) :=
  first;
[  Case_aux c "WFU []"
 | Case_aux c "WFU ([(x, p, tau)] ++ u)"
].

Tactic Notation "gettype_ind_cases" tactic(first) ident(c) :=
 first;
[
  Case_aux c "gettype u x p tau [] tau"
| Case_aux c "gettype u x p (cross t0 t1) (i_pe zero_pe :: p') tau"
| Case_aux c "gettype u x p (cross t0 t1) (i_pe one_pe :: p') tau"
| Case_aux c "gettype u x p (etype aliases alpha k tau') (u_pe :: p') tau)"
].

Tactic Notation "ltyp_ind_cases" tactic(first) ident(c) :=
 first;
[ 
 Case_aux c "ltyp d u g (p_e x p) tau"
| Case_aux c "ltyp d u g (star e) tau"
| Case_aux c "ltyp d u g (dot e zero_pe) t0"
| Case_aux c "ltyp d u g (dot e one_pe) t1"
].

(*
Tactic Notation "ltyp_ind_cases" tactic(first) ident(c) :=
 first;
[ 
 Case_aux c "styp d u g tau (e_s e) (styp_e_3_1 d u g tau e r)"
| Case_aux c "styp d u g tau (retn e) (styp_return_3_2 d u g tau e r)"
| Case_aux c "styp d u g tau (seq s1 s2) (styp_seq_3_3 d u g tau s1 s2 s s0)"
| Case_aux c "styp d u g tau (while e s) (styp_while_3_4 d u g tau e s r s0)"
| Case_aux c "styp d u g tau (if_s e s1 s2) (styp_if_3_5 d u g tau e s1 s2 r s s0)"
| Case_aux c "styp d u g tau (letx x e s) (styp_let_3_6 d u g x tau tau' s e e0 s0 r)"
| Case_aux c "styp d u g tau (open e alpha x s) (styp_open_3_7 d u g x p alpha k tau tau' s e e0 e1 k0 r s0))"
| Case_aux c "styp d u g tau (openstar e alpha x s) (styp_openstar_3_8 d u g x alpha k tau tau' s e r s0 e0 e1 k0))"
| Case_aux c "ltyp d u g (p_e x p) tau (SL_3_1 d g u x p tau tau' e g0 w k))"
| Case_aux c "ltyp d u g (star e) tau (SL_3_2 d u g e tau r k))"
| Case_aux c "ltyp d u g (dot e zero_pe) t0 (SL_3_3 d u g e t0 t1 l))"
| Case_aux c "ltyp d u g (dot e one_pe) t1 (SL_3_4 d u g e t0 t1 l))"
| Case_aux c "rtyp d u g (p_e x p) tau (SR_3_1 d g u x p tau tau' e g0 k w))"
| Case_aux c "rtyp d u g (star e) tau (SR_3_2 e tau d u g r k))"
| Case_aux c "rtyp d u g (dot e zero_pe) t0 (SR_3_3 d u g e t0 t1 r))"
| Case_aux c "rtyp d u g (dot e one_pe) t1 (SR_3_4 d u g e t0 t1 r))"
| Case_aux c "rtyp d u g (i_e (i_i z)) cint (SR_3_5 d u g z w))"
| Case_aux c "rtyp d u g (amp e) (ptype tau) (SR_3_6 d u g e tau l))"
| Case_aux c "rtyp d u g (cpair e0 e1) (cross t0 t1) (SR_3_7 d u g e0 e1 t0 t1 r r0))"
| Case_aux c "rtyp d u g (assign e1 e2) tau (SR_3_8 d u g e1 e2 tau l r a))"
| Case_aux c "rtyp d u g (appl e1 e2) tau (SR_3_9 d u g e1 e2 tau tau' r r0))"
| Case_aux c "rtyp d u g (call s) tau (SR_3_10 d u g tau s s0 r))"
| Case_aux c "rtyp d u g (inst e tau) (subst_Tau tau' tau alpha) (SR_3_11 d u g e tau tau' alpha k r a))"
| Case_aux c "rtyp d u g (pack tau' e (etype p alpha k tau)) (etype p alpha k tau) (SR_3_12 d u g e tau tau' alpha k p r a k0))"
| Case_aux c "rtyp d u g (f_e (dfun tau x tau' s)) (arrow tau tau') (SR_3_13 d u g tau tau' s x e s0 r))"
| Case_aux c "rtyp d u g (f_e (ufun alpha k f24)) (utype alpha k tau) (SR_3_14 d u g f24 tau alpha k e w r))"
| Case_aux c "base"
].
*)

Tactic Notation "Tau_ind_cases" tactic(first) ident(c) :=
 first;
[ Case_aux c "(tv_t t)"
| Case_aux c "cint"
| Case_aux c "(cross t t0)"
| Case_aux c "(arrow t t0)"
| Case_aux c "(ptype t)"
| Case_aux c "(utype t k t0)"
| Case_aux c "(etype p t k t0)"
].

Tactic Notation "AK_ind_cases" tactic(first) ident(c) :=
 first;
[ Case_aux c "AK d (tv_t alpha) A"
| Case_aux c "AK d (subst_Tau (tv_t alpha0) alpha k) A"
].

Tactic Notation "ASGN_ind_cases" tactic(first) ident(c) :=
 first;
[ Case_aux c "ASGN d cint"
| Case_aux c "ASGN d (tv_t alpha)"
| Case_aux c "ASGN d (ptype tau)"
| Case_aux c "ASGN d (cross t0 t1)"
| Case_aux c "ASGN d (arrow t0 t1)"
| Case_aux c "ASGN d (utype alpha k tau)"
| Case_aux c "ASGN d (etype witnesschanges alpha k tau))"
].

Tactic Notation "WFDG_ind_cases" tactic(first) ident(c) :=
 first;
[ Case_aux c "WFDG d []"
| Case_aux c "WFDG d ([(x, tau)] ++ g)"
| Case_aux c "WFDG ([(alpha, k)] ++ d) g"
].

Tactic Notation "WFD_ind_cases" tactic(first) ident(c) :=
 first;
[ 
  Case_aux c "WFD []"
| Case_aux c "WFD ([(alpha, k)] ++ d)"
].

Tactic Notation "ret_ind_cases" tactic(first) ident(c) :=
 first;
[ Case_aux c "ret (if_s e s1 s2)"
| Case_aux c "ret (seq s s') 1"
| Case_aux c "ret (seq s s') 2"
| Case_aux c "ret (letx x e s)"
| Case_aux c "ret (open e alpha x s)"
| Case_aux c "ret (openstar e alpha x s))"
].

Tactic Notation "htyp_ind_cases" tactic(first) ident(c) :=
 first;
[ Case_aux c "htyp u g [] []"
| Case_aux c "htyp u g h ([(x, tau)] ++ g')"
].

Tactic Notation "refp_ind_cases" tactic(first) ident(c) :=
 first;
[ Case_aux c "refp h []"
| Case_aux c "refp h ([(x, p, tau')] ++ u)"
].

Tactic Notation "Value_ind_cases" tactic(first) ident(c) :=
 first;
[ Case_aux c "(i_e i)"
| Case_aux c "(amp (p_e x p))"
| Case_aux c "(f_e (dfun t1 x t2 s))"
| Case_aux c "(f_e (ufun t k f2))"
| Case_aux c "(cpair v0 v1)"
| Case_aux c "(pack tau v tau')"
].

Tactic Notation "get_ind_cases" tactic(first) ident(c) :=
 first;
[ Case_aux c "v [] v"
| Case_aux c "(cpair v0 v1) (i_pe zero_pe :: p) v"
| Case_aux c "(cpair v0 v1) (i_pe one_pe :: p) v"
| Case_aux c "(pack tau' v1 (etype aliases alpha k tau)) (u_pe :: p)v"
].

