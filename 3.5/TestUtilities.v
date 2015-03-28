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

Definition p0   := [(Path.i_pe Path.zero_pe)].
Definition p1   := [(Path.i_pe Path.one_pe)].

(* Some type equality issues remain. *)
(* Definition d    := (D.ctxt alpha A D.dot). *)
Definition g    := (G.ctxt x cint G.dot).
Definition u    := (D.ctxt alpha A D.dot).
Definition h    := (H.ctxt x e H.dot).


Definition q := aliases.

(* We use these to show that substitution ignores expresions without
  type variables, f, substitutes all alphas falphaalpha, and ignores
  type other type variables, fbetabeta. *)
(*
Print cint.
Check cint : Tau.
Check cint : T.Tau.
Print dfun.
*)

Definition fx   := (fevar x).
Definition b0   := (bevar 0).

Definition f   :=
  (dfun cint   cint (retn (inst (p_e fx pdot) tau))).
Definition faa := 
  (dfun tau   (ftvar alpha) (retn (inst (p_e fx pdot) (ftvar alpha)))).
Definition fbb  := 
  (dfun tau  (ftvar beta) (retn (inst (p_e fx pdot) (ftvar beta)))).

Definition applff  := (e_s (appl (f_e f)   (f_e f))).
Definition applfaa := (e_s (appl (f_e faa) (f_e faa))).
Definition applfbb := (e_s (appl (f_e fbb) (f_e fbb))).

(* TODO  These are done only with free type variables which should not be enough. *)
Definition ufg  := (ufun A faa).
Definition ufaa := (ufun A faa).
Definition ufbb := (ufun A faa).

