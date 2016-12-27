Lemma extends_get':
  forall A (E E' : env A),
    extends E E' ->
    forall x v,
      get x E  = Some v ->
      get x E' = Some v.
Proof.
  intros.
  unfold extends, binds in H.
  induction E'; auto.
Qed.

