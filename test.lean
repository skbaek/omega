lemma foo : ∀ x : list unit, unit
| []      := ()
| (eq::_) := 
  begin
    have h0 : 0 = 0 :=
    (calc 0 
        = 0 : rfl
    ... = 0 : rfl)
  end


  #check @eq