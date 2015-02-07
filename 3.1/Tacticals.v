(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Tacticals to make auto and crush simplify.

*)
 
Set Implicit Arguments.
Require Export LanguageModuleDef.
Require Export DynamicSemanticsTypeSubstitution.
Require Export DynamicSemanticsHeapObjects.
Require Export DynamicSemantics.
Require Export StaticSemanticsKindingAndContextWellFormedness.
Require Export StaticSemantics.
(* Require Export ContextExtensionRelation. *)

Create HintDb Chapter3.
Hint Constructors Value : Chapter3.
Hint Constructors S : Chapter3.
Hint Constructors R : Chapter3.
Hint Constructors L : Chapter3.
Hint Constructors get : Chapter3.
Hint Constructors set : Chapter3.
Hint Constructors gettype : Chapter3.
Hint Constructors ret : Chapter3.
Hint Constructors styp : Chapter3.
Hint Constructors ltyp : Chapter3.
Hint Constructors rtyp : Chapter3.
Hint Constructors htyp : Chapter3.
Hint Constructors refp : Chapter3.
Hint Constructors prog : Chapter3.
Hint Constructors K : Chapter3.
Hint Constructors AK : Chapter3.
Hint Constructors ASGN : Chapter3.
Hint Constructors WFDG : Chapter3.
Hint Constructors WFU : Chapter3.
Hint Constructors WFC : Chapter3.
Hint Constructors WFD : Chapter3.
(* Hint Constructors ExtendedByD : Chapter3. *)

Hint Extern 4 => discriminate. (* For ifs. *)

(* Getting eauto to evaluate functions requires some of this. *)
Hint Extern 0 ((HM.map _ _) = Some _) => try reflexivity : Chapter3.
Hint Extern 0 ((HM.add _ _) = _) => try reflexivity : Chapter3.
Hint Extern 0 ((HM.delete _ _) = _) => try reflexivity : Chapter3.

Hint Extern 0 ((DM.map _ _) = Some _) => try reflexivity : Chapter3.
Hint Extern 0 ((GM.map _ _) = Some _) => try reflexivity : Chapter3.
Hint Extern 0 (UM.map _ _ _ = None) => try reflexivity : Chapter3.

(* Now the judgements work by popping of the left most element of their lists. *)

Lemma app_removefirst_first :
  forall (A : Type) (d : A) (l : list A),
    l <> nil -> l = [hd d l] ++ (tail l).
Proof.
Admitted.

Ltac left_list_recurse_gamma m :=
  rewrite app_removefirst_first with (l:= m) (d:=(evar(1000),cint));
  try simpl hd;
  try simpl tail;
  try discriminate.

Ltac left_list_recurse_delta m :=
  rewrite app_removefirst_first with (l:= m) (d:=(tvar(1000),A));
  try simpl hd;
  try simpl tail;
  try discriminate.
 
Ltac left_list_recurse_upsilon m :=
  rewrite app_removefirst_first with (l:= m) (d:= ( ((evar 1000), []), cint));
  try simpl hd;
  try simpl tail;
  try discriminate.

Ltac left_list_recurse_path m :=
  rewrite app_removefirst_first with (l:= m) (d:= (u_pe));
  try simpl hd;
  try simpl tail;
  try discriminate.

Ltac list_splitter :=
   match goal with
     | [ |- gettype _ _ _ _ (?x ++ ?y) _ ]   => try constructor
     | [ |- gettype _ _ _ _ ?x _ ] 
       => try (left_list_recurse_path x; constructor)

   end.

Hint Extern 3 (gettype _ _ _ _ _ _)   => list_splitter.

Hint Extern 5 ([] ++ _ = _) => try reflexivity.
Hint Extern 5 (_ = [] + _)  => try reflexivity.

(* A sleazy way to work around this eauto requires my db bug. *)
Ltac Crunch := eauto 20 with Chapter3; crush; eauto 20 with Chapter3.
