import .Environments

/- Binds tests -/

lemma bound_some_fred {α : Type } (a : α) (b : list (string × α)) :
  binds "fred" (("fred",a) :: b) = some a := 
begin
  simp,
end


#eval to_string 'a' 
#check "a"
#check @binds Kappa "fred" []
#eval @binds Kappa "fred" []
#eval binds "fred" [("fred",A)]

#eval "fred"
#eval ["fred"]
#eval @none string 
#eval @none Kappa

