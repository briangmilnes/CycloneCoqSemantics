(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION".   Daniel Grossman, August 2003 *)
(* Other required infrastructure from LN, free variable calculations*)
(* Brian Milnes 2016 *)

Set Implicit Arguments.
Require Export Cyclone_Formal_Syntax LibVarPathEnv.

(* Free Variables. *)

(* Free variables of types. *)

Fixpoint ftyv_tau (tau : Tau) {struct tau} : vars :=
  match tau with
    | btvar i      => \{}
    | ftvar x      => \{x}
    | cint         => \{}
    | cross t0 t1  => (ftyv_tau t0) \u (ftyv_tau t1)
    | arrow t0 t1  => (ftyv_tau t0) \u (ftyv_tau t1)
    | ptype t0     => (ftyv_tau t0)
    | utype k t0   => (ftyv_tau t0)
    | etype _ _ t0 => (ftyv_tau t0)
end.

Definition closed_tau t := ftyv_tau t = \{}.

(* Free term variables of terms. *)

Function fv_v (v : V) {struct v} : vars := 
  match v with
    | (bevar i) => \{}
    | (fevar x) => \{x}
  end.

Fixpoint fv_st (t : St) {struct t} : vars :=
  match t with
    | e_s  e       => fv_e e
    | retn e       => fv_e e
    | seq s0 s1    => (fv_st s0) \u (fv_st s1)
    | if_s e s0 s1 => (fv_e e) \u ((fv_st s0) \u (fv_st s1))
    | while e s0   => (fv_e e) \u (fv_st s0)
    | letx e s     => (fv_e e) \u (fv_st s)
    | open e s     => (fv_e e) \u (fv_st s)
    | openstar e s => (fv_e e) \u (fv_st s)
  end
with  fv_e (e : E) {struct e} : vars := 
  match e with 
    | v_e v         => fv_v v
    | i_e  i        => \{}
    | p_e v p       => (fv_v v)
    | f_e f         => fv_f f
    | amp e         => fv_e e
    | star e        => fv_e e
    | cpair e0 e1   => (fv_e e0) \u (fv_e e1)
    | dot e ipe     => fv_e e
    | assign e1 e2  => (fv_e e1) \u (fv_e e2)
    | appl e1 e2    => (fv_e e1) \u (fv_e e2)
    | call s        => fv_st s 
    | inst e t      => fv_e e
    | pack t0 e t1  => fv_e e
  end
with  fv_f (f : F) {struct f} : vars := 
  match f with
  | dfun t1 t2 s => (fv_st s)
  | ufun k f     => fv_f f
end.

Function fv_term (t : Term) {struct t} : vars :=
  match t with 
    | term_st s    => fv_st s
    | term_e  e    => fv_e e
    | term_f  f    => fv_f f 
  end.

Definition closed_Term x := fv_term x = \{}.

(* Free type variables of a term. *)

Function ftyv_v (v : V) : vars := 
  match v with 
    | (bevar i) => \{} 
    | (fevar x) => \{}
  end.

Fixpoint ftyv_st (t : St) {struct t} : vars :=
  match t with
    | e_s  e       => ftyv_e e
    | retn e       => ftyv_e e
    | seq s0 s1    => (ftyv_st s0) \u (ftyv_st s1)
    | if_s e s0 s1 => (ftyv_e e) \u (ftyv_st s0) \u (ftyv_st s1)
    | while e s0   => (ftyv_e e) \u (ftyv_st s0)
    | letx e s     => (ftyv_e e) \u (ftyv_st s)
    | open e s     => (ftyv_e e) \u (ftyv_st s)
    | openstar e s => (ftyv_e e) \u (ftyv_st s)
  end
with  ftyv_e (e : E) {struct e} : vars := 
  match e with 
    | v_e v         => ftyv_v v
    | i_e  i        => \{}
    | p_e x p       => \{}
    | f_e f         => ftyv_f f
    | amp e         => ftyv_e e
    | star e        => ftyv_e e
    | cpair e0 e1   => (ftyv_e e0) \u (ftyv_e e1)
    | dot e ipe     => ftyv_e e
    | assign e1 e2  => (ftyv_e e1) \u (ftyv_e e2)
    | appl e1 e2    => (ftyv_e e1) \u (ftyv_e e2)
    | call s        => ftyv_st s 
    | inst e t      => (ftyv_e e) \u (ftyv_tau t)
    | pack t0 e t1  => (ftyv_tau t0) \u (ftyv_e e) \u (ftyv_tau t1)
  end
with  ftyv_f (f : F) {struct f} : vars := 
  match f with
  | dfun t1 t2 s    => (ftyv_tau t1) \u (ftyv_tau t2) \u (ftyv_st s) 
  | ufun k f        => ftyv_f f
end.

Function ftyv_term (t : Term) {struct t} : vars :=
  match t with 
    | term_st s    => ftyv_st s
    | term_e  e    => ftyv_e e
    | term_f  f    => ftyv_f f 
 end.

Definition closed_tau_Term x := ftyv_term x = \{}.

(* Free variables from environments. *)

(* Dom' is just first composed with dom to get the variable. *)
Definition fv_upsilon (u : Upsilon)  : vars := LVPE.V.dom' u.
Definition fv_heap    (h : Heap)     : vars := dom h.
Definition ftyv_delta (d : Delta)    : vars := dom d.
Definition fv_gamma   (g : Gamma)    : vars := dom g.

Function fv_state  (s : State) : vars :=
  match s with
    | (h, st) => (fv_heap h) \u (fv_st st) \u (ftyv_st st)
  end.
