(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

 Provide standard test objects for all test files. 

*)

Set Implicit Arguments.
Require Export Cyclone_Formal_Syntax.
Require Export List.
Import ListNotations.
Import LibEnvNotations.

Definition k  := A.
Definition ka := A.
Definition kb := B.

(* Bug 4 i_i does not handle negative numbers! *)
Definition v'    := (i_e (i_i 4)).
Definition v''   := (i_e (i_i 6)).
Definition v     := (i_e (i_i 3)).
Definition v0    := (i_e (i_i 0)).
Definition v1    := (i_e (i_i 1)).
Definition vi0   := (i_e (i_i 0)).
Definition vi1   := (i_e (i_i 1)).
Definition vi2   := (i_e (i_i 2)).

Definition e    := (i_e (i_i 0)).
Definition e'   := (i_e (i_i 1)).
Definition e0   := (i_e (i_i 0)).
Definition e1   := (i_e (i_i 1)).
Definition e2   := (i_e (i_i 1)).

Definition s  := (retn (i_e (i_i 0))).
Definition s' := (retn (i_e (i_i 0))).
Definition s1 := (retn (i_e (i_i 1))).
Definition s2 := (retn (i_e (i_i 2))).

Parameter alpha_ : var.
Parameter beta_  : var.
Parameter gamma_ : var.

Definition alpha := (ftvar alpha_).
Definition beta  := (ftvar beta_).
Definition gamma := (ftvar gamma_).

Parameter varx  : var.
Parameter varx' : var.
Parameter vary  : var.
Parameter vary' : var.
Parameter varz  : var.
Parameter varz' : var.

Definition x     := (fevar varx).
Definition x'    := (fevar varx').
Definition y     := (fevar vary).
Definition y'    := (fevar vary').
Definition z     := (fevar varz).
Definition z'    := (fevar varz').

Definition i     := (i_i 0).
Definition i1    := (i_i 1).
Definition i2    := (i_i 2).
Definition i3    := (i_i 3).

Definition tau  := cint.
Definition tau' := cross cint cint.
Definition t    := cint.
Definition t'   := cross cint cint.
Definition t0   := cint.
Definition t1   := cross cint cint.

Definition p0   := [(i_pe zero_pe)].
Definition p1   := [(i_pe one_pe)].


Definition h    := (single varx e) & hdot.

Definition q := aliases.

(* We use these to show that substitution ignores expresions without
  type variables, f, substitutes all alphas falphaalpha, and ignores
  type other type variables, fbetabeta. *)
Definition f           := 
  (dfun tau  tau (retn (inst (p_e x pdot) tau))).
Definition faa := 
  (dfun tau  alpha (retn (inst (p_e x pdot) alpha))).
Definition fbb  := 
  (dfun tau  beta (retn (inst (p_e x pdot) beta))).

Definition applff  := (e_s (appl (f_e f)   (f_e f))).
Definition applfaa := (e_s (appl (f_e faa) (f_e faa))).
Definition applfbb := (e_s (appl (f_e fbb) (f_e fbb))).

Definition ufg  := (ufun A faa).
Definition ufaa := (ufun A faa).
Definition ufbb := (ufun A faa).

Ltac unfold_test_utilities :=
 unfold k, ka, kb, v', v'', v, v0, v1, vi0, vi1, vi2, e, e', e0, e1, e2, s, s', s1, s2, alpha, beta, gamma, x, x', y, y', z, z', i, i1, i2, i3, tau, tau', t, t', t0, t1, p0, p1, h, q, f, faa, fbb, applff, applfaa, applfbb, ufg, ufaa, ufbb in *.

