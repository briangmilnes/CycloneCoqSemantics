(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

   Admitting that environments commute. This is not true in the object theory of coq.

*)

Set Implicit Arguments.
Require Export Cyclone_Formal_Syntax.
Require Export TLC.LibEnv LibVarPathEnv.
Close Scope list_scope.
Import LibEnvNotations.
Import LVPE.LibVarPathEnvNotations.

Lemma env_assoc:
  forall A (E : env A) F G, 
    E & F & G = E & (F & G).
Admitted.

Lemma env_comm:
  forall A (E : env A) F,
    E & F = F & E.
Admitted.

Lemma libvarpathenv_assoc:
  forall (E : LVPE.varpathenv Tau) F G, 
    E &p F &p G = E &p (F &p G).
Admitted.

Lemma libvarpathenv_comm:
  forall (E : LVPE.varpathenv Tau) F, 
    E &p F = F &p E.
Admitted.

Lemma drop_empty:
  forall A (d : env A),
    d & empty = d.
Admitted.

Lemma drop_lvpe_empty:
  forall (u : LVPE.varpathenv Tau),
    u &p LVPE.V.empty = u.
Admitted.

(* How do I get these admissibly ?*)
Lemma eq_inversion_env:
  forall A (g : env A) x tau0 g0 alpha tau,
    g & x ~ tau0 = g0 & alpha ~ tau ->
    (g = g0 /\ x = alpha /\ tau0 = tau).
Admitted.

Lemma empty_not_constructed:
  forall A (g : env A) alpha tau,
    empty = g & alpha ~ tau ->
    False.
Admitted.

Lemma add_empty_delta:
  forall (d : Delta),
    d = d & empty.
Admitted.
