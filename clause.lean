import .term

@[reducible] def clause := (list term) × (list term)

namespace clause

def weaker : clause → clause → Prop 
| ⟨eqs1,les1⟩ ⟨eqs2,les2⟩ := eqs1 ⊆ eqs2 ∧ les1 ⊆ les2 

def holds (v) : clause → Prop 
| (eqs,les) :=
  ( (∀ t : term, t ∈ eqs → 0 = term.val v t) 
    ∧ (∀ t : term, t ∈ les → 0 ≤ term.val v t) )

lemma holds_of_weaker {v c1 c2} : 
  weaker c1 c2 → holds v c2 → holds v c1 :=
begin
  intros h1 h2, 
  cases c1 with eqs1 les1, 
  cases c2 with eqs2 les2, 
  constructor, 
  { apply list.forall_mem_of_subset h1.left h2.left }, 
  { apply list.forall_mem_of_subset h1.right h2.right }, 
end

def sat (c : clause) : Prop :=
  ∃ v : nat → int, holds v c

lemma sat_of_weaker { c1 c2} : 
  weaker c1 c2 → sat c2 → sat c1 :=
begin
  intros h1 h2, cases h2 with v h2,
  refine ⟨v,holds_of_weaker h1 h2⟩,
end

def unsat (c : clause) : Prop := ¬ c.sat 

def append (c1 c2 : clause) : clause :=
(c1.fst ++ c2.fst, c1.snd ++ c2.snd)

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

end clause

def clauses.sat (ps : list clause) : Prop := 
∃ c ∈ ps, clause.sat c  

def clauses.unsat (ps) : Prop := ¬ clauses.sat ps

lemma clauses.unsat_nil : clauses.unsat [] := 
begin intro h1, rcases h1 with ⟨c,h1,h2⟩, cases h1 end

lemma clauses.unsat_cons (p ps) : 
  clause.unsat p → clauses.unsat ps → 
  clauses.unsat (p::ps) | h1 h2 h3 := 
begin
  simp only [clauses.sat] at h3,
  rw list.exists_mem_cons_iff at h3, 
  cases h3; contradiction,
end
