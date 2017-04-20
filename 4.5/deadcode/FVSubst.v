Lemma fv_subst:
  forall tau alpha tau',
    T.fv tau' = \{} ->
    T.subst tau alpha tau' = tau'.
Proof.
  intros.
  induction tau'; auto;
    try solve[simpl in H; simpl; fequals*].
  simpl in H.
  apply singleton_empty in H.
  inversion H.

  simpl in H.
  simpl.
  assert(T.fv tau'1 = \{}). admit.
  assert(T.fv tau'2 = \{}). admit.
  fequals*.

  simpl in H.
  simpl.
  assert(T.fv tau'1 = \{}). admit.
  assert(T.fv tau'2 = \{}). admit.
  fequals*.  
Qed.
