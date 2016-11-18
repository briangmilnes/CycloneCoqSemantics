(* Cyclone Semantics using TLC/LN in Coq Version 4 *)
(* "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION".   Daniel Grossman, August 2003 *)
(* Sizing terms for induction. *)
(* Brian Milnes 2016 *)

Set Implicit Arguments.
Require Export Cyclone_Formal_Syntax LibVarPathEnv.

Fixpoint size_t (tau : Tau) {struct tau} : nat :=
  match tau with
    | btvar i      => 1
    | ftvar x      => 1
    | cint         => 1
    | cross t0 t1  => (size_t t0) + (size_t t1)
    | arrow t0 t1  => (size_t t0) + (size_t t1)
    | ptype t0     => (size_t t0)
    | utype k t0   => (size_t t0)
    | etype p k t0 => (size_t t0)
  end.

Function size_tm_v (v : V) : nat :=  1.

Fixpoint size_tm_st (t : St) {struct t} : nat :=
  match t with
    | e_s  e       => 1 + size_tm_e e
    | retn e       => 1 + size_tm_e e
    | seq s0 s1    => 1 + (size_tm_st s0) + (size_tm_st s1)
    | if_s e s0 s1 => 1 + (size_tm_e e) + (size_tm_st s0) + (size_tm_st s1)
    | while e s0   => 1 + (size_tm_e e) + (size_tm_st s0)
    | letx e s     => 1 + (size_tm_e e) + (size_tm_st s)
    | open e s     => 1 + (size_tm_e e) + (size_tm_st s)
    | openstar e s => 1 + (size_tm_e e) + (size_tm_st s)
  end
with  size_tm_e (e : E) {struct e} : nat := 
  match e with 
    | v_e v         => 1 + size_tm_v v
    | i_e  i        => 1
    | p_e x p       => 1
    | f_e f         => 1 + size_tm_f f
    | amp e         => 1 + size_tm_e e
    | star e        => 1 + size_tm_e e
    | cpair e0 e1   => 1 + (size_tm_e e0) + (size_tm_e e1)
    | dot e ipe     => 1 + size_tm_e e
    | assign e1 e2  => 1 + (size_tm_e e1) + (size_tm_e e2)
    | appl e1 e2    => 1 + (size_tm_e e1) + (size_tm_e e2)
    | call s        => 1 + size_tm_st s 
    | inst e t      => 1 + (size_tm_e e) + (size_t t)
    | pack t0 e t1  => 1 + (size_t t0) + (size_tm_e e) + (size_t t1)
  end
with  size_tm_f (f : F) {struct f} : nat := 
  match f with
  | dfun t1 t2 s    => 1 + (size_t t1) + (size_t t2) + (size_tm_st s) 
  | ufun k f        => 1 + size_tm_f f
end.

Function size_tm (t : Term) {struct t} : nat :=
  match t with 
    | term_st s    => 1 + size_tm_st s
    | term_e  e    => 1 + size_tm_e e
    | term_f  f    => 1 + size_tm_f f 
 end.

