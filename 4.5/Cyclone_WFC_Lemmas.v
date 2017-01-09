(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

   WFC Lemmas

*)

Set Implicit Arguments.
Require Export Cyclone_Formal_Syntax Cyclone_Static_Semantics_Kinding_And_Context_Well_Formedness Cyclone_LN_Tactics.
Require Export Cyclone_WFD_Lemmas Cyclone_WFU_Lemmas Cyclone_WFDG_Lemmas Cyclone_K_Lemmas.
Close Scope list_scope.
Import LibEnvNotations.
Import LVPE.LibVarPathEnvNotations.

Lemma WFC_ok_delta:
  forall d u g, 
    WFC d u g ->
    ok d.
Proof.
  intros.
  inversion* H.
Qed.
Ltac WFC_ok_delta :=
  match goal with
    | H : WFC ?d ?u' ?g'|- ok ?d => apply WFC_ok_delta with (u:=u') (g:=g')
  end.
Hint Extern 1 (ok _) => try WFC_ok_delta.

Lemma WFC_ok_gamma:
  forall d u g, 
    WFC d u g ->
    ok g.
Proof.
  intros*.
  inversion* H; subst.
Qed.
Ltac WFC_ok_gamma :=
  match goal with
    | H : WFC ?d' ?u' ?g|- ok ?g => apply WFC_ok_gamma with (d:= d') (u:=u')
  end.
Hint Extern 1 (ok _) => try WFC_ok_gamma.

Lemma WFC_gamma_K:
  forall d u g, 
    WFC d u g ->
    forall x tau, 
      get x g = Some tau ->
      K d tau A.
Proof.
  intros.
  inversion H; subst.
  apply WFDG_gamma_K with (g:= g) (x:=x); try assumption.
Qed.
Ltac WFC_gamma_K :=
  match goal with 
    | H: WFC ?d' ?u' ?g',
      I: get ?x' ?g' = Some ?tau'
    |- K ?d' ?tau' A =>
    apply WFDG_gamma_K with (d:=d') (u:=u') (g:=g') (x:=x') (tau:=tau')
  end.
Hint Extern 1 (K _ _ A) => WFC_gamma_K.


Lemma WFC_upsilon_K:
  forall d u g, 
    WFC d u g ->
    forall x p tau, 
      LVPE.V.get (x,p) u = Some tau ->
      K empty tau A.
Proof.
 introv WFCd.
 inversion WFCd; subst.
 apply WFU_upsilon_K; assumption.
Qed.
Ltac WFC_upsilon_K :=
  match goal with 
    | H: WFC ?d' ?u' ?g',
      I: LVPE.V.get (?x',?p') ?u' = Some ?tau'
      |-  K empty ?tau' A =>
      apply WFU_upsilon_K
end.
Hint Extern 1 (K empty _ A) => WFC_upsilon_K.



(* The heart of the magic K.
 So either rtyp/ltyp/styp when they bind (write the store) or read (p_e (fevar x) p)
that type has to K empty ? A. 

  So either Dan has failed to check this or its provable from type typing derivations.

  WFU checks this but nothing in the typing rules do.

  Assuming the thesis needs addition, rules that should check this are:
  SS 3.6 (or all rtyp)
  SS 3.7
  SS 3.8
  SL3.1
  SR 3.1
  SR 3.8 - has asgn.
  SR 3.11 - has ak 
  SR 3.12 - has ak
*)

Lemma WFC_gamma_weakening:
  forall d u g,
    WFC d u g ->
    forall tau, 
      K empty tau A ->  (* Magic K *)
      forall y, 
        y \notin (fv_gamma g) ->
        WFC d u (g & (y ~ tau)).
Proof.
SearchAbout(_ -> K _ _ A).
  lets: WFDG_gamma_weakening.
  introv WFCd.
  inversion WFCd; subst.
  constructor; try assumption.
  constructor; auto.
  apply K_weakening with (d:= empty); auto.
Qed.
Ltac WFC_gamma_weakening :=
  match goal with
    | H: K ?d' ?tau' A,
      I: WFC ?d' ?u' ?g' 
    |-  WFC ?d' ?u' (?g' & (?y' ~ ?tau')) =>
      apply WFC_gamma_weakening with (tau:=tau');
      notin_solve
  end.
Hint Extern 1 (WFC _ _ (_ & (_ ~ _))) => WFC_gamma_weakening.

Lemma WFDG_delta_gamma_weakening:
  forall alpha d g x k tau, 
    alpha \notin fv_delta d ->
    x \notin  fv_gamma g ->
    K d tau A ->
    WFDG d g ->
    WFDG (d & alpha ~ k) (g & x ~ tau).
Proof.
  introv ANI XNI Kd WFCd.
  apply WFDG_delta_weakening; try assumption.
  apply WFDG_gamma_weakening; try assumption.
Qed.  

Ltac WFDG_delta_gamma_weakening :=
  match goal with
    | H: ?alpha \notin _,
      I: ?x \notin _,
      J: WFDG ?d' ?g'
    |- WFDG (?d' & ?alpha ~ ?k) (?g' & ?x ~ ?tau)  =>
      apply WFDG_delta_gamma_weakening; notin_solve
  end.
Hint Extern 1 (WFDG (_ & _ ~ _) (_ & _ ~ _)) => WFDG_delta_gamma_weakening.

Lemma WFC_delta_weakening:
  forall alpha d u g k,  
    alpha \notin fv_delta d ->
    WFC d u g ->
    WFC (d & alpha ~ k) u g.
Proof.
  lets: WFDG_delta_weakening.
  introv ANI WFCd.
  inversion WFCd; subst.
  auto.
Qed.
Ltac WFC_delta_weakening :=
  match goal with
    | H: ?alpha \notin _,
      J: WFC ?d' ?u ?g'
    |- WFC (?d' & ?alpha ~ ?k) _ ?g' =>
      apply WFC_delta_weakening; notin_solve; try assumption
  end.

Hint Extern 1 (WFC (_ & _ ~ _) _ _) => WFDG_delta_gamma_weakening.

Lemma WFC_delta_gamma_weakening:
  forall alpha d u g x k tau, 
    alpha \notin fv_delta d ->
    x \notin fv_gamma g ->
    K d tau A ->
    WFC d u g ->
    WFC (d & alpha ~ k) u (g & x ~ tau).
Proof.
  lets: WFDG_delta_gamma_weakening.
  introv ANI XNI Kd WFCd.
  inversion WFCd; subst.
  auto.
Qed.
Ltac WFC_delta_gamma_weakening :=
  match goal with
    | H: ?alpha \notin _,
      I: ?x \notin _,
      J: WFC ?d' ?g' _
    |- WFC (?d' & ?alpha ~ ?k) _ (?g' & ?x ~ ?tau)  =>
      apply WFC_delta_gamma_weakening; notin_solve
  end.
Hint Extern 1 (WFC (_ & _ ~ _) _ (_ & _ ~ _)) => WFDG_delta_gamma_weakening.


Lemma WFC_WFU:
  forall d u g, 
    WFC d u g ->
    WFU u.
Proof.
  introv WFCd.
  inversion WFCd; auto.
Qed.
Ltac WFC_WFU :=
  match goal with
    | H: WFC ?d' ?u' ?g' |- WFU ?u' => apply WFC_WFU with (d:=d')(g:=g')
  end.
Hint Extern 1 (WFU _) => WFC_WFU; auto.

Lemma WFC_WFDG:
  forall d u g, 
    WFC d u g ->
    WFDG d g.
Proof.
  introv WFCd.
  inversion WFCd; auto.
Qed.
Ltac WFC_WFDG :=
  match goal with
    | H: WFC ?d' ?u' ?g' |- WFDG ?d' ?g'  => apply WFC_WFDG with (u:= u')
  end.
Hint Extern 1 (WFDG _) => WFC_WFDG; auto.

Lemma WFC_ok_upsilon:
  forall d u g, 
    WFC d u g ->
    LVPE.okp u.
Proof.
  introv WFCd.
  inversion WFCd; auto.
Qed.
Hint Immediate WFC_ok_upsilon.

Lemma WFC_strength:
  forall alpha d0 u0 g0 tau,
    alpha \notin fv_delta d0 ->
    alpha \notin fv_gamma g0 ->
    alpha \notin fv_upsilon u0 ->
    WFC d0 u0 (g0 & alpha ~ tau) ->
    WFC d0 u0 g0.
Proof.
  introv a1 a2 a3 WFCd.
  constructor*.
  inversions WFCd.
  apply WFDG_strength with (alpha:= alpha) (tau:= tau); auto.
Qed.
