(* I was having to break out all of the notins to apply the inductive hypothesis.
   Arthur however is doing it backwards using auto and it works smoothly. 

Ltac ns :=
 match goal with
   | H: _ \notin (_ \u _) |-  _ => apply LibVar.notin_union_r in H; clear H;
    match goal with
        | I: (_ \notin _) /\ (_ \notin _) |- _ => inversion I; ns
    | _ => idtac 
  end
end.

*)

