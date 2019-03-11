import .term

@[reducible] def polytope := list term 

namespace polytope

@[reducible] def holds (v) (p : polytope) : Prop :=
∀ t ∈ p, (0 ≤ term.val v t)

def sat (p : polytope) : Prop := ∃ v, holds v p

def unsat (p : polytope) : Prop := ¬ sat p

end polytope

@[reducible] def polytopes.unsat (ps : list polytope) : Prop := 
  ∀ p ∈ ps, polytope.unsat p

lemma polytopes.unsat_nil : polytopes.unsat [] := list.forall_mem_nil _

lemma polytopes.unsat_cons (p ps) : 
  polytope.unsat p → polytopes.unsat ps → polytopes.unsat (p::ps) 
| h1 h2 := list.forall_mem_cons.elim_right ⟨h1,h2⟩   


