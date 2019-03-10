import ..term

--@[reducible] def consts := (list term) × (list term)
--
--namespace consts
--
--meta instance has_to_format : has_to_format consts := by apply_instance

--def weaker : consts → consts → Prop 
--| ⟨eqs1,les1⟩ ⟨eqs2,les2⟩ := eqs1 ⊆ eqs2 ∧ les1 ⊆ les2 


#exit

@[reducible] def sat (c : consts) : Prop :=
  ∃ v : nat → int, holds v c

lemma sat_of_weaker {c1 c2} : 
  weaker c1 c2 → sat c2 → sat c1 :=
begin
  intros h1 h2, cases h2 with v h2,
  refine ⟨v,holds_of_weaker h1 h2⟩,
end

def unsat (c : consts) : Prop := ¬ c.sat 

def append (c1 c2 : consts) : consts :=
(c1.fst ++ c1.fst, c1.snd ++ c2.snd)

def holds_append {v c1 c2} : 
holds v c1 → holds v c2 → holds v (append c1 c2) := 
begin
  intros h1 h2, 
  cases c1 with eqs1 les1,
  cases c2 with eqs2 les2,
  cases h1, cases h2,
  constructor; rw list.forall_mem_append; 
  constructor; assumption,
end

end consts