(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION".   Daniel Grossman, August 2003 *)
(* This is all of the LN infrastructure packed in a module for types. *)
(* Brian Milnes 2016 *)

Require Export Cyclone_Formal_Syntax Cyclone_LN_Types Cyclone_LN_Terms Cyclone_LN_Types_In_Terms.
Require Export TLC.LibEnv TLC.LibList.
Close Scope list_scope.
Import LibEnvNotations.
Import LVPE.LibVarPathEnvNotations.


Function fv_heap (h : Heap) : vars :=
    dom h \u fv_in_values (fun (e : E) => TTM.fv_e e \u TM.fv_e e) h.

Function fv_state (s : State) :=
  match s with
    | (h,st) => fv_heap h \u TM.fv_st st \u TTM.fv_st st
  end.

Function fv_delta   (d : Delta)   : vars := dom d.
Function fv_gamma   (g : Gamma)   : vars :=
  dom g \u fv_in_values (fun (t : Tau) => T.fv t) g.

Function fv_upsilon (u : Upsilon) : vars := 
  LVPE.fv_in_keys (fun (xp : varpath) => \{fst xp}) u \u
  LVPE.fv_in_values (fun (t : Tau) => T.fv t) u.


(* Now we need lemmas to simplify the abstract versions of these. *)
Lemma values_empty:
  forall (A : Type),
    (@values A) (@empty A) = nil.
Admitted.

Lemma values_app:
  forall (A : Type) E F,
    (@values A) (E & F) = app (@values A E) (@values A F).
Admitted.
  
Lemma lvpe_values_empty:
    (@LVPE.V.values varpath) (@LVPE.V.empty varpath)  = nil.
Admitted.

Lemma fv_in_values_empty:
  forall (A : Type),
   forall f, fv_in_values f (@empty A) = \{}.
Proof.
  intros.
  unfold fv_in_values.
  rewrite values_empty.
  apply fold_right_nil.
Qed.

Lemma values_single:
  forall (A : Type) x v,
    (@values A (x ~ v)) = (cons v nil).
Admitted.

Lemma lvpe_values_single:
  forall  x v,
    (@LVPE.V.values varpath (x ~p v)) = (cons v nil).
Admitted.

Lemma lvpe_fv_in_values_empty:
   forall f, (@LVPE.fv_in_values varpath) f (@LVPE.V.empty varpath) = \{}.
Proof.
  intros.
  unfold LVPE.fv_in_values.
  rewrite lvpe_values_empty.
  apply fold_right_nil.
Qed.

Lemma lvpe_fv_in_keys_concat:
  forall E F f,
  LVPE.fv_in_keys f (E &p F) =
  ((@LVPE.fv_in_keys varpath) f E) \u ((@LVPE.fv_in_keys varpath) f F).
Admitted.

Lemma fv_heap_empty:
  fv_heap empty = \{}.
Proof.
  unfold fv_heap.
  rewrite dom_empty.
  rewrite union_empty_l.
  unfold fv_in_values.
  rewrite values_empty.
  apply fold_right_nil.
Qed.

Lemma fv_delta_empty:
  fv_delta empty = \{}.
Proof.
  unfold fv_delta.
  rewrite* dom_empty.
Qed.

Lemma fv_gamma_empty:
  fv_gamma empty = \{}.
Proof.
  unfold fv_gamma.
  rewrite dom_empty.
  rewrite union_empty_l.
  unfold fv_in_values.
  rewrite values_empty.
  apply fold_right_nil.
Qed.

Lemma fv_upsilon_empty:
  fv_upsilon LVPE.V.empty = \{}.
Proof.
  unfold fv_upsilon.
  unfold LVPE.fv_in_values.
  (* Coq but more likely my understanding of unverses rewriting bug. *)
  (* rewrite lvpe_values_empty.*)
Admitted.

Lemma fv_heap_single :
  forall x v,
    fv_heap (x ~ v) = \{x} \u TTM.fv_e v \u TM.fv_e v.
Proof.
  intros.
  unfold fv_heap.
  rewrite dom_single.
  unfold fv_in_values.
  rewrite values_single.
  rewrite fold_right_cons.
  rewrite fold_right_nil.
  auto.
  rewrite union_empty_r.
  reflexivity.
Qed.

Lemma fv_delta_single :
  forall x v,
    fv_delta (x ~ v) = \{x}.
Proof.
  intros.
  unfold fv_delta.
  rewrite dom_single.
  reflexivity.
Qed.

Lemma fv_gamma_single :
  forall x v,
    fv_gamma (x ~ v) = \{x} \u T.fv v.
Proof.
  intros.
  unfold fv_gamma.
  rewrite dom_single.
  unfold fv_in_values.
  rewrite values_single.
  rewrite fold_right_cons.
  rewrite fold_right_nil.
  rewrite union_empty_r.
  reflexivity.
Qed.

Lemma fv_upsilon_single:
  forall x p t,
    fv_upsilon ((x,p) ~p t) = \{x} \u T.fv t.
Proof.
  intros.
  unfold fv_upsilon, LVPE.fv_in_keys, LVPE.fv_in_values.
  (* rewrite lvpe_values_single. *)
Admitted.

Lemma fv_heap_concat:
  forall E F,
    fv_heap (E & F) = fv_heap E \u fv_heap F.
Proof.
  intros.
  unfold fv_heap.
  unfold fv_in_values.
  rewrite values_app.
Admitted.

Lemma fv_delta_concat:
  forall E F,
    fv_delta (E & F) = fv_delta E \u fv_delta F.
Proof.
  intros.
  unfold fv_delta.
  rewrite dom_concat.
  reflexivity.
Qed.

Lemma fv_gamma_concat:
  forall E F,
    fv_gamma (E & F) = fv_gamma E \u fv_gamma F.
Proof.
  intros.
  unfold fv_gamma.
  rewrite dom_concat.
  unfold fv_in_values.
  rewrite values_app.
(*  rewrite fold_right_app. *)
Admitted.

Lemma fv_upsilon_concat:
  forall E F,
    fv_upsilon (E &p F) = fv_upsilon E \u fv_upsilon F.
Proof.
  intros.
  unfold fv_upsilon.
  (* again some universe problem. *)
Admitted.  


Lemma fv_heap_push: 
forall x v E,
  fv_heap (E & x ~ v) = fv_heap E \u fv_heap(x ~ v).
Admitted.

Lemma fv_delta_push: 
forall x v E,
  fv_delta (E & x ~ v) = fv_delta E \u fv_delta(x ~ v).
Admitted.

Lemma fv_gamma_push: 
forall x v E,
  fv_gamma (E & x ~ v) = fv_gamma E \u fv_gamma(x ~ v).
Admitted.

Lemma fv_upsilon_push: 
forall x v E,
  fv_upsilon (E &p x ~p v) = fv_upsilon E \u fv_upsilon(x ~p v).
Admitted.


