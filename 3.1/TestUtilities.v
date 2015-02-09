(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

 Provide standard test objects for all test files. 

*)

Set Implicit Arguments.
Require Export LanguageModuleDef.

Definition k  := A.
Definition ka := A.
Definition kb := B.

(* Bug 4 i_i does not handle negative numbers! *)
Definition v'    := (i_e (i_i 4)).
Definition v''   := (i_e (i_i 6)).
Definition v     := (i_e (i_i 3)).
Definition v0    := (i_e (i_i Z0)).
Definition v1    := (i_e (i_i 1)).
Definition vi0   := (i_e (i_i Z0)).
Definition vi1   := (i_e (i_i 1)).
Definition vi2   := (i_e (i_i 2)).

Definition e    := (i_e (i_i Z0)).
Definition e'   := (i_e (i_i 1)).
Definition e0   := (i_e (i_i Z0)).
Definition e1   := (i_e (i_i 1)).
Definition e2   := (i_e (i_i 1)).

Definition s  := (retn (i_e (i_i 0))).
Definition s' := (retn (i_e (i_i 0))).
Definition s1 := (retn (i_e (i_i 1))).
Definition s2 := (retn (i_e (i_i 2))).

Definition x     := (EV.var 0).
Definition x'    := (EV.var 3).
Definition y     := (EV.var 1).
Definition y'    := (EV.var 4).
Definition z     := (EV.var 2).
Definition z'    := (EV.var 8).

Definition alpha := (TV.var 0).
Definition beta  := (TV.var 1).
Definition gamma := (TV.var 2).

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


Definition h    := (hctxt x e hdot).

Definition q := aliases.

(* We use these to show that substitution ignores expresions without
  type variables, f, substitutes all alphas falphaalpha, and ignores
  type other type variables, fbetabeta. *)
Definition f           := 
  (dfun tau   x tau (retn (inst (p_e x pdot) tau))).
Definition faa := 
  (dfun tau   x (tv_t alpha) (retn (inst (p_e x pdot) (tv_t alpha)))).
Definition fbb  := 
  (dfun tau   x (tv_t beta) (retn (inst (p_e x pdot) (tv_t beta)))).

Definition applff  := (e_s (appl (f_e f)   (f_e f))).
Definition applfaa := (e_s (appl (f_e faa) (f_e faa))).
Definition applfbb := (e_s (appl (f_e fbb) (f_e fbb))).

Definition ufg  := (ufun gamma A faa).
Definition ufaa := (ufun alpha A faa).
Definition ufbb := (ufun beta  A faa).



