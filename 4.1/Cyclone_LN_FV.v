(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION".   Daniel Grossman, August 2003 *)
(* Other required infrastructure from LN, free variable calculations*)
(* Brian Milnes 2016 *)

Set Implicit Arguments.
Require Export Cyclone_Formal_Syntax LibVarPathEnv.

(* Free Variables. *)

(* Free variables of types. *)

Fixpoint ftv_t (tau : Tau) {struct tau} : vars :=
  match tau with
    | btvar i      => \{}
    | ftvar x      => \{x}
    | cint         => \{}
    | cross t0 t1  => (ftv_t t0) \u (ftv_t t1)
    | arrow t0 t1  => (ftv_t t0) \u (ftv_t t1)
    | ptype t0     => (ftv_t t0)
    | utype k t0   => (ftv_t t0)
    | etype _ _ t0 => (ftv_t t0)
end.

Definition closed_t t := ftv_t t = \{}.

(* Free type variables of a term. *)

Function ftv_tm_v (v : V) : vars := 
  match v with 
    | (bevar i) => \{} 
    | (fevar x) => \{}
  end.

Fixpoint ftv_tm_st (t : St) {struct t} : vars :=
  match t with
    | e_s  e       => ftv_tm_e e
    | retn e       => ftv_tm_e e
    | seq s0 s1    => (ftv_tm_st s0) \u (ftv_tm_st s1)
    | if_s e s0 s1 => (ftv_tm_e e) \u (ftv_tm_st s0) \u (ftv_tm_st s1)
    | while e s0   => (ftv_tm_e e) \u (ftv_tm_st s0)
    | letx e s     => (ftv_tm_e e) \u (ftv_tm_st s)
    | open e s     => (ftv_tm_e e) \u (ftv_tm_st s)
    | openstar e s => (ftv_tm_e e) \u (ftv_tm_st s)
  end
with  ftv_tm_e (e : E) {struct e} : vars := 
  match e with 
    | v_e v         => ftv_tm_v v
    | i_e  i        => \{}
    | p_e x p       => \{}
    | f_e f         => ftv_tm_f f
    | amp e         => ftv_tm_e e
    | star e        => ftv_tm_e e
    | cpair e0 e1   => (ftv_tm_e e0) \u (ftv_tm_e e1)
    | dot e ipe     => ftv_tm_e e
    | assign e1 e2  => (ftv_tm_e e1) \u (ftv_tm_e e2)
    | appl e1 e2    => (ftv_tm_e e1) \u (ftv_tm_e e2)
    | call s        => ftv_tm_st s 
    | inst e t      => (ftv_tm_e e) \u (ftv_t t)
    | pack t0 e t1  => (ftv_t t0) \u (ftv_tm_e e) \u (ftv_t t1)
  end
with  ftv_tm_f (f : F) {struct f} : vars := 
  match f with
  | dfun t1 t2 s    => (ftv_t t1) \u (ftv_t t2) \u (ftv_tm_st s) 
  | ufun k f        => ftv_tm_f f
end.

Function ftv_tm (t : Term) {struct t} : vars :=
  match t with 
    | term_st s    => ftv_tm_st s
    | term_e  e    => ftv_tm_e e
    | term_f  f    => ftv_tm_f f 
 end.

Definition closed_tv_tm x := ftv_tm x = \{}.

(* Free term variables of terms. *)

Function fv_tm_v (v : V) {struct v} : vars := 
  match v with
    | (bevar i) => \{}
    | (fevar x) => \{x}
  end.

Fixpoint fv_tm_st (t : St) {struct t} : vars :=
  match t with
    | e_s  e       => fv_tm_e e
    | retn e       => fv_tm_e e
    | seq s0 s1    => (fv_tm_st s0) \u (fv_tm_st s1)
    | if_s e s0 s1 => (fv_tm_e e) \u ((fv_tm_st s0) \u (fv_tm_st s1))
    | while e s0   => (fv_tm_e e) \u (fv_tm_st s0)
    | letx e s     => (fv_tm_e e) \u (fv_tm_st s)
    | open e s     => (fv_tm_e e) \u (fv_tm_st s)
    | openstar e s => (fv_tm_e e) \u (fv_tm_st s)
  end
with  fv_tm_e (e : E) {struct e} : vars := 
  match e with 
    | v_e v         => fv_tm_v v
    | i_e  i        => \{}
    | p_e v p       => (fv_tm_v v)
    | f_e f         => fv_tm_f f
    | amp e         => fv_tm_e e
    | star e        => fv_tm_e e
    | cpair e0 e1   => (fv_tm_e e0) \u (fv_tm_e e1)
    | dot e ipe     => fv_tm_e e
    | assign e1 e2  => (fv_tm_e e1) \u (fv_tm_e e2)
    | appl e1 e2    => (fv_tm_e e1) \u (fv_tm_e e2)
    | call s        => fv_tm_st s 
    | inst e t      => fv_tm_e e
    | pack t0 e t1  => fv_tm_e e
  end
with  fv_tm_f (f : F) {struct f} : vars := 
  match f with
  | dfun t1 t2 s => (fv_tm_st s)
  | ufun k f     => fv_tm_f f
end.

Function fv_tm (t : Term) {struct t} : vars :=
  match t with 
    | term_st s    => fv_tm_st s
    | term_e  e    => fv_tm_e e
    | term_f  f    => fv_tm_f f 
  end.

Definition closed_c_tm x := fv_tm x = \{}.

(* Free variables from environments. *)

(* Dom' is just first composed with dom to get the variable. *)
Definition fv_upsilon (u : Upsilon)  : vars := LVPE.V.dom' u.
Definition fv_heap    (h : Heap)     : vars := dom h.
Definition fv_delta (d : Delta)    : vars := dom d.
Definition fv_gamma   (g : Gamma)    : vars := dom g.

Function fv_state  (s : State) : vars :=
  match s with
    | (h, st) => (fv_heap h) \u (fv_tm_st st) \u (ftv_tm_st st)
  end.
