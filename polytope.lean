import .term 

@[reducible] def polytope := list term 

namespace polytope

@[reducible] def holds (v) (p : polytope) : Prop :=
∀ t ∈ p, (0 ≤ term.val v t)

def sat (p : polytope) : Prop := ∃ v, holds v p

def unsat (p : polytope) : Prop := ¬ sat p

end polytope

def polytopes.sat (ps : list polytope) : Prop := 
∃ c ∈ ps, polytope.sat c  

def polytopes.unsat (ps) : Prop := ¬ polytopes.sat ps

lemma polytopes.unsat_nil : polytopes.unsat [] := 
begin intro h1, rcases h1 with ⟨c,h1,h2⟩, cases h1 end

lemma polytopes.unsat_cons (p ps) : 
  polytope.unsat p → polytopes.unsat ps → 
  polytopes.unsat (p::ps) | h1 h2 h3 := 
begin
  simp only [polytopes.sat] at h3,
  rw list.exists_mem_cons_iff at h3, 
  cases h3; contradiction,
end
