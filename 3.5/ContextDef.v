(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 
*)
Set Implicit Arguments.
Require Export BooleanEqualitySetDef.

Module Type Context.
  Declare Module K  : BooleanEquality.
  Declare Module T  : BooleanEquality.
 (* A set on K but not represented here. *)
  Declare Module KS : BooleanEqualitySet. 

  Parameter Context  : Type.
  Parameter empty    : Context.
  Parameter add      : Context -> K.t -> T.t -> Context.
  Parameter map      : Context -> K.t -> option T.t.
  Parameter nodup    : Context -> bool.
  Parameter equal    : Context -> Context -> bool.
  Parameter concat   : Context -> Context -> Context.
  Parameter dom      : Context -> KS.t.
  Parameter extends  : Context -> Context -> bool.
End Context.
