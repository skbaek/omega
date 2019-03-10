import ..term

def holds (v) (eqs les : list term) : Prop :=
(∀ t ∈ eqs, 0 = term.val v t) ∧
(∀ t ∈ les, 0 ≤ term.val v t) 

def sat (eqs les : list term) : Prop := ∃ v, holds v eqs les
@[reducible] def sat' (cs : list term × list term) : Prop := ∃ v, holds v cs.fst cs.snd

def unsat (eqs les : list term) : Prop := ¬ sat eqs les
@[reducible] def unsat' (cs : list term × list term) : Prop := ¬ sat' cs

lemma holds_of_weaker {v} {eqs1 eqs2 les1 les2 : list term} : 
  eqs1 ⊆ eqs2 → les1 ⊆ les2 → holds v eqs2 les2 → holds v eqs1 les1 :=
begin
  intros h1 h2 h3, constructor, 
  { apply list.forall_mem_of_subset h1 h3.left }, 
  { apply list.forall_mem_of_subset h2 h3.right } 
end

lemma sat_of_weaker {eqs1 eqs2 les1 les2 : list term} : 
  eqs1 ⊆ eqs2 → les1 ⊆ les2 → sat eqs2 les2 → sat eqs1 les1 :=
begin
  intros h1 h2 h3, cases h3 with v h3,
  refine ⟨v,_⟩, apply holds_of_weaker h1 h2 h3
end