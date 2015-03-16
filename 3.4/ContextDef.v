(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 
*)
Set Implicit Arguments.
Require Export BooleanEqualitySetDef.

Module Type Context.
  Declare Module K : BooleanEqualitySet.
  Declare Module T : BooleanEquality.

  Parameter Context  : Type.
  Parameter empty    : Context.
  Parameter add      : Context -> K.elt -> T.t -> Context.
  Parameter map      : Context -> K.elt -> option T.t.
  Parameter nodup    : Context -> bool.
  Parameter equal    : Context -> Context -> bool.
  Parameter concat   : Context -> Context -> Context.
  Parameter dom      : Context -> K.t.
  Parameter extends  : Context -> Context -> bool.
End Context.
