(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

 This defines some early attempts at tacticals for the dynamic
  semantics. 

*)
 
Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.

Require Export FormalSyntax.
Require Export DynamicSemanticsTypeSubstitution.
Require Export DynamicSemanticsHeapObjects.
Require Export DynamicSemantics.
Require Export StaticSemanticsKindingAndContextWellFormedness.
Require Export StaticSemantics.

(* e/auto using *)

Create HintDb Chapter3.
Hint Constructors Value     : Chapter3.
Hint Constructors S         : Chapter3.
Hint Constructors R         : Chapter3.
Hint Constructors L         : Chapter3.
Hint Constructors get       : Chapter3.
Hint Constructors set       : Chapter3.
(* Hint Constructors gettype   : Chapter3. *)
Hint Constructors ret       : Chapter3.
Hint Constructors styp      : Chapter3.
Hint Constructors ltyp      : Chapter3.
Hint Constructors rtyp      : Chapter3.
Hint Constructors htyp      : Chapter3.
Hint Constructors refp      : Chapter3.
Hint Constructors prog      : Chapter3.
Hint Constructors K         : Chapter3.
Hint Constructors AK        : Chapter3.
Hint Constructors ASGN      : Chapter3.
Hint Constructors WFDG      : Chapter3.
Hint Constructors WFU       : Chapter3.
Hint Constructors WFC       : Chapter3.
Hint Extern 4 => discriminate : Chapter3. (* For ifs. *)
(* Getting eauto to evaluate functions requires some of this. *)
Hint Extern 0 (getG _ _ = Some _)           => apply eq_refl : Chapter3.
Hint Extern 0 (gettype _ _ _ _ _ = Some _) => apply eq_refl : Chapter3.

(* Some contexts require (cons nil [v]) for empty matches. *)
Theorem app_nil_l_nil:
  forall (A : Type) (l : list A),
    l = nil ++ l ++ nil.
Proof.
  intros A l.
  induction l.
  reflexivity.
  simpl in IHl.
  simpl.
  rewrite <- IHl.
  reflexivity.
Qed.

Hint Extern 2 (K [?x] _ _)      => try rewrite <- app_nil_l with (l:=[x]).
Hint Extern 2 (ASGN [?x] _ )    => try rewrite <- app_nil_l with (l:=[x]).
Hint Extern 2 (WFU  [?x]   )    => try rewrite <- app_nil_l with (l:=[x]).
Hint Extern 2 (WFC _ _ [?x])    => try rewrite <- app_nil_l with (l:=[x]).
Hint Extern 2 (WFDG _ [?x])     => try rewrite <- app_nil_l with (l:=[x]).
Hint Extern 2 (htyp _ _ _ [?x]) => try rewrite <- app_nil_l with (l:=[x]).
Hint Extern 2 (htyp _ _ [?y] _) => try rewrite app_nil_l_nil with (l:=[y]).
Hint Extern 2 (refp _ [?y])     => try rewrite app_nil_l_nil with (l:=[y]).
Hint Extern 2 (ltyp  _ _ [?y] _)
                                => try rewrite app_nil_l_nil with (l:=[y]).
Hint Extern 2 (R [?h] _ _ _)
                                => try rewrite app_nil_l_nil with (l:=[h]).
Hint Extern 2 (R _ _ [?h] _)
                                => try rewrite app_nil_l_nil with (l:=[h]).

Hint Extern 2 (S [?h] _ _ _)
                                => try rewrite app_nil_l_nil with (l:=[h]).
Hint Extern 2 (S _ _ [?h] _)
                                => try rewrite app_nil_l_nil with (l:=[h]).

(* TODO can I just use the automation here to reorder heaps ? *)
