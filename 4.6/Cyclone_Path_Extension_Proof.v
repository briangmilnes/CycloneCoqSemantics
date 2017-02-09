(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 
  
 Path Extension
*)

Set Implicit Arguments.
Require Export Cyclone_Formal_Syntax Cyclone_Static_Semantics_Kinding_And_Context_Well_Formedness.
Require Export Cyclone_Dynamic_Semantics.
Require Export Cyclone_Classes Cyclone_Inductions Cyclone_LN_Tactics Cyclone_LN_Extra_Lemmas_And_Automation.
Require Export Cyclone_WFC_Lemmas.
Require Export Cyclone_WFU_Lemmas.
Require Export Cyclone_Context_Weakening_Proof.
Require Export Cyclone_Substitutions_Proof.
Require Export Cyclone_LN_Types_Lemmas.
Require Export Cyclone_Get_Lemmas.
Require Export Cyclone_Admit_Environment.
Open Scope list_scope.

(* Dan is probably thinking like this but not saying it in the text of the proof. *)
(* Thesis difference, using getd. *)
Lemma get'_path_extension_r:
  forall v p v' v'' pe,
    Value v ->
    Value v' ->
    Value v'' ->
    get' v p v' ->
    get' v' (cons pe nil) v'' ->
    get' v (app p (cons pe nil)) v''.
Proof.  
  introv vv vv' vv'' getd.
  induction getd; intros.
  simpl; auto.
  apply IHgetd in H2; auto.
  constructor*.
  apply IHgetd in H2; auto.
  constructor*.
  apply IHgetd in H1; auto.
  constructor*.
Qed.  
  
Ltac invert_exists :=
  repeat
    match goal with
    | H : exists _ _, _ |- _ => inversions H
    | H : exists _, _ |- _ => inversions H
    | H : Value (cpair _ _) |- _ => inversions H
   end.

Lemma A_10_Path_Extension_1_A_pair:
  forall v p v',
    get' v p v' ->
    (forall v0 v1, 
        v' = (cpair v0 v1) ->
        get' v (app p (cons (i_pe zero_pe) nil)) v0 /\
        get' v (app p (cons (i_pe one_pe)  nil)) v1) .
Proof.
  introv getd.
  induction getd; intros; split; subst; inversions* H;
  try solve[constructor*]; 
  try solve[ apply get'_path_extension_r with (v':= (cpair v2 v3)); auto];
  try solve[apply get'_path_extension_r with (v':= (cpair v0 v2)); auto].
Qed.

Ltac invert_pathed_get :=
  match goal with
   | H : get' _ (app _ _) _ |- _ => inversions* H
  end.

Lemma A_10_Path_Extension_1_A_no_pair:
  forall v p v',
    get' v p v' ->
    ( ~(exists v0 v1,  v' = (cpair v0 v1)) ->
      ~(exists i p' v'', get' v (app p (cons (i_pe i) p')) v'')).
Proof.
  introv getd.
  induction getd; intros; unfolds; intros;
    invert_exists;
    invert_pathed_get.
Qed.

Lemma A_10_Path_Extension_1_A_pack:
  forall v p v',
    get' v p v' ->
   forall t' v0 t k,
     v' = (pack t' v0 (etype aliases k t)) ->
     get' v (app p (cons u_pe nil)) v0.
Proof.
  introv getd.
  induction getd; intros; subst; inversions* H;
  simpl;
  try solve[constructor*].
Qed.

Lemma A_10_Path_Extension_1_A_no_pack:
  forall v p v',
    get' v p v' ->
    ~(exists t' v0 t k, v' = (pack t' v0 (etype aliases k t))) ->
    ~(exists p' v'',  get' v (app p (cons u_pe p')) v'').
Proof.
  introv getd.
  induction getd; intros; unfolds; intros;
  try solve[invert_exists; invert_pathed_get].
  invert_exists.
  simpl in H1.
  inversions* H1.
  unfolds in H0.
  contradict H0.
  exists* tau' v1 tau k.
Qed.

(* ? Extend both ps? *)
Lemma gettype_path_extension_r:
  forall u x p t p' t',
    gettype u x p t p' t' ->
    forall pe t'', 
      gettype u x (app p (cons pe nil)) t' (app (cons pe nil) p') t'' ->
      gettype u x (app p (cons pe nil)) t p' t''.
Proof.  
  introv gettyped.
  induction gettyped; intros; simpl; auto.
  destruct pe. destruct i.
Admitted.

Lemma A_10_Path_Extension_2_cross:
  forall u x p t p' t',
    gettype u x p t p' t' ->
    forall t0 t1,
      t' = (cross t0 t1) ->
      (gettype u x p t (app p' (cons (i_pe zero_pe) nil)) t0 /\
       gettype u x p t (app p' (cons (i_pe one_pe ) nil)) t1).
Proof.
  introv gettyped.
  induction gettyped; intros; try solve[split; subst; simpl; constructor*];
  try solve[intros; split; subst; simpl; constructor*; try apply* IHgettyped].
  try solve[intros; split; subst; simpl; apply gettype_etype with (tau'':= tau''); auto;
  apply* IHgettyped].
Qed.

Lemma fix_path:
  forall (a :PE), 
    (a :: nil) = (app (a :: nil) nil).
Proof.
  auto.
Qed.

(* this is a weak version of an intermediate type theorem. *)
Lemma punt:
  forall x p u tau0 k t0 t2 p',
   LVPE.V.get (x, p) u = Some tau0 ->
   forall pe, 
     gettype u x (p ++ pe :: nil) t0 p' (etype aliases k t2) ->
     LVPE.V.get (x, p ++ pe :: nil) u = Some tau0.
Admitted.

Lemma gettype_nil_get_agreement: 
  forall u x p t t' t'',
    gettype u x p t nil t' ->
    LVPE.V.get (x, p) u = Some t'' ->
    (t = t' /\ t = t'').
Admitted.

Lemma intermediate_type_zero:
  forall u x p t0 p' t2,
  gettype u x (p ++ (i_pe zero_pe) :: nil) t0 p' t2 ->
  exists t1,
    gettype u x p t0 p' t1.
Admitted.

Lemma intermediate_type_one:
  forall u x p t0 p' t2,
  gettype u x (p ++ (i_pe one_pe) :: nil) t0 p' t2 ->
  exists t1,
    gettype u x p t0 p' t1.
Admitted.

Lemma intermediate_type_u:
  forall u x p t0 p' t2,
  gettype u x (p ++ u_pe :: nil) t0 p' t2 ->
  exists t1,
    gettype u x p t0 p' t1.
Admitted.

Lemma append_to_app_nil:
  forall A (x : list A) y,
    x & y = (app x (cons y nil)).
Admitted.

Lemma A_10_Path_Extension_2_etype:
  forall p',  
   forall u x p t t',
    gettype u x p t p' t' ->
    forall k t0,
      t' = (etype aliases k t0) ->
      forall tau, 
        LVPE.V.get (x,p) u = Some tau ->
        (gettype u x p t (app p' (cons u_pe nil)) (T.open_rec 0 tau t0)).
Proof.
(* breaks at the induction unless I find some way to radically change the types/paths. *)
  intros p'.
  induction p'; intros.
  apply gettype_nil_get_agreement with (t'':= tau) in H; auto.
  inversions H; subst.
  simpl.
  apply gettype_etype with (tau'':= (etype aliases k t0)); auto.

  subst.
  inversion H; subst.
  simpl.
  constructor.
  assert(E: etype aliases k t0 = etype aliases k t0). admit.
  specialize (IHp' u x (p ++ i_pe zero_pe :: nil) t1 (etype aliases k t0)).
  rewrite append_to_app_nil in IHp'.
  specialize (IHp' H8 k t0 E tau).
  inversions* H8.
  apply IHp'.
  (* Assume Dan is right, then tau is t1? invert more? *)

(*
  introv gettyped.
  induction gettyped; intros; subst.
  simpl.
  rewrite fix_path.
  apply gettype_etype with (tau'':= tau0); auto.

  intros; subst; simpl; constructor*.
(*  inversions gettyped. *)
  apply IHgettyped with (k0:=k); auto.
  admit.

  intros; subst; simpl; constructor*.
(*  inversions gettyped. *)
  apply IHgettyped with (k0:=k); auto.
  admit.  
  
  simpl.
  apply gettype_etype with (tau'':=tau''); auto.
  apply IHgettyped with (k:=k0); auto.
  admit.
Qed.
 *)
Admitted.
