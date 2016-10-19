(* Can I use Theorem with if I can get a clean induction? *)

Inductive Fred : Prop -> Prop :=
 | Fred1 : Fred True
with Joe : Prop -> Prop := 
 | Joe1  : Joe True.

Theorem FredTrue:
  Fred True ->
  True
with JoeTrue:
  Joe False ->
  True.
Proof.
  intros.
  induction H.
  admit.
  admit.
Admitted.
(* Not clear to me that this works. *)

(* Statement inhabited. *)

Inductive Kappa : Type :=
 | B                         (* 'boxed' kind. *)
 | A.                        (* 'any'   kind. *)

Inductive Tau : Type :=
 | btvar     : nat -> Tau
 | ftvar     : nat -> Tau
 | arrow     : Tau -> Tau -> Tau    
 | utype     : Kappa -> Tau -> Tau.

Inductive St : Type :=                        
 | e_s       : E   -> St
 | letx      : E -> St   -> St        
with E : Type :=                              
 | bevar     : nat -> E
 | fevar     : nat -> E
 | f_e       : F -> E
with F : Type :=
 | dfun      : Tau -> Tau -> St -> F.

Function foo_st (s : St) : bool :=
  match s with
  | e_s e  => foo_e e 
  | letx e s => 
    match (foo_e e) with
      | true  => foo_st s
      | false => false
    end
end
with foo_e (e : E) : bool :=
 match e with 
  | bevar x => true
  | fevar x => true
  | f_e f   => foo_f f
end
with foo_f (f : F) : bool :=
  match f with
   | dfun t1 t2 s => foo_st s
  end.

(* Fucked up in that it assumes all three cases in every case! LOL. *)
Theorem st_foo:
  forall s, foo_st s = true
with e_foo:
  forall e, foo_e e = true
with f_foo:
  forall f, foo_f f = true.
Proof.
  intros.
  induction s.
  admit.
  admit.
  admit.
  admit.
Qed.
  (* and it gives me an undocumented 'not enough abstractions' error *)
