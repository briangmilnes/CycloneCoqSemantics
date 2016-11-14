(** Properties of substitutions *)

Lemma subst_tau_core:
  forall t0 t1 t v v' ,
    v <> v' ->
    (subst_tau t0 v t) = (subst_tau t1 v' (subst_tau t0 v t)) ->
     t = (subst_tau t1 v' t).
Proof.
  induction t; introv Neq Equ; simpls; inversion* Equ; fequals*.
  case_var*.
  case_var*.
Qed.

Lemma subst_tau_v_core:
  forall t0 t1 t v v',
    v <> v' ->
    (subst_tau_v t0 v t) = (subst_tau_v t1 v' (subst_tau_v t0 v t)) ->
     t = (subst_tau_v t1 v' t).
Proof.
  induction t;
  introv Neq Equ;
  simpls*.
Qed.

Lemma subst_tau_st_core:
  forall s v v',
    v <> v' ->
    forall s0 s1, 
      (subst_tau_st s0 v s) = (subst_tau_st s1 v' (subst_tau_st s0 v s)) ->
      s = (subst_tau_st s1 v' s).
Proof.
  apply (St_ind_mutual 
           (fun s : St => 
              forall v v',
                v <> v' ->
              forall s0 s1, 
                (subst_tau_st s0 v s) = (subst_tau_st s1 v' (subst_tau_st s0 v s)) ->
                s = (subst_tau_st s1 v' s))
           (fun e : E  => 
              forall v v',
                v <> v' ->
              forall e0 e1,
                (subst_tau_e e0 v e) = (subst_tau_e e1 v' (subst_tau_e e0 v e)) ->
                e = (subst_tau_e e1 v' e))
           (fun f : F  => 
              forall v v',
                v <> v' ->
              forall f0 f1,
                (subst_tau_f f0 v f) = (subst_tau_f f1 v' (subst_tau_f f0 v f)) ->
                f = (subst_tau_f f1 v' f))); 
  intros;
  simpl;
  fequals;
  try solve[
        try inversion H4 as [I4];
        try inversion H3 as [I3];
        try inversion H2 as [I2];
        try inversion H1 as [I1];
        try solve[applys* H];
        try solve[applys* H0];
        try solve[applys* H1];
        try solve[applys* H2];
        try solve[applys* H3];
        try solve[applys* subst_tau_core]].

  destruct v; simpl; reflexivity.
Qed.

Lemma subst_tau_e_core:
  forall e v v',
    v <> v' ->
    forall e0 e1, 
      (subst_tau_e e0 v e) = (subst_tau_e e1 v' (subst_tau_e e0 v e)) ->
      e = (subst_tau_e e1 v' e).
Proof.
  apply (E_ind_mutual 
           (fun s : St => 
              forall v v',
                v <> v' ->
              forall s0 s1, 
                (subst_tau_st s0 v s) = (subst_tau_st s1 v' (subst_tau_st s0 v s)) ->
                s = (subst_tau_st s1 v' s))
           (fun e : E  => 
              forall v v',
                v <> v' ->
              forall e0 e1,
                (subst_tau_e e0 v e) = (subst_tau_e e1 v' (subst_tau_e e0 v e)) ->
                e = (subst_tau_e e1 v' e))
           (fun f : F  => 
              forall v v',
                v <> v' ->
              forall f0 f1,
                (subst_tau_f f0 v f) = (subst_tau_f f1 v' (subst_tau_f f0 v f)) ->
                f = (subst_tau_f f1 v' f)));
  intros;
  simpl;
  fequals;
  try solve[
        try inversion H4 as [I4];
        try inversion H3 as [I3];
        try inversion H2 as [I2];
        try inversion H1 as [I1];
        try solve[applys* H];
        try solve[applys* H0];
        try solve[applys* H1];
        try solve[applys* H2];
        try solve[applys* H3];
        try solve[applys* subst_tau_core]].
  destruct v; simpl; reflexivity.
Qed.

Lemma subst_tau_f_core:
  forall f v v',
    v <> v' ->
    forall f0 f1, 
      (subst_tau_f f0 v f) = (subst_tau_f f1 v' (subst_tau_f f0 v f)) ->
      f = (subst_tau_f f1 v' f).
Proof.
  apply (F_ind_mutual 
           (fun s : St => 
              forall v v',
                v <> v' ->
              forall s0 s1, 
                (subst_tau_st s0 v s) = (subst_tau_st s1 v' (subst_tau_st s0 v s)) ->
                s = (subst_tau_st s1 v' s))
           (fun e : E  => 
              forall v v',
                v <> v' ->
              forall e0 e1,
                (subst_tau_e e0 v e) = (subst_tau_e e1 v' (subst_tau_e e0 v e)) ->
                e = (subst_tau_e e1 v' e))
           (fun f : F  => 
              forall v v',
                v <> v' ->
              forall f0 f1,
                (subst_tau_f f0 v f) = (subst_tau_f f1 v' (subst_tau_f f0 v f)) ->
                f = (subst_tau_f f1 v' f)));
  intros;
  simpl;
  fequals;
  try solve[
        try inversion H4 as [I4];
        try inversion H3 as [I3];
        try inversion H2 as [I2];
        try inversion H1 as [I1];
        try solve[applys* H];
        try solve[applys* H0];
        try solve[applys* H1];
        try solve[applys* H2];
        try solve[applys* H3];
        try solve[applys* subst_tau_core]].
  destruct v; simpl; reflexivity.
Qed.

Lemma open_rec_term_core_term:
  forall v v',
    v <> v' ->
    forall t0 t1 t, 
      (subst_tau_term t0 v t) = (subst_tau_term t1 v' (subst_tau_term t0 v t)) ->
      t = (subst_tau_term t1 v' t).
Proof.
  intros; destruct t; inversion H0; simpl; fequals*.
  apply subst_tau_st_core with (v:=v) (s0:=t0); try assumption.
  apply subst_tau_e_core with  (v:=v) (e0:=t0); try assumption.
  apply subst_tau_f_core with  (v:=v) (f0:=t0); try assumption.
Qed.

