import .preterm 
--..simp_omega 
..logic

namespace int

@[derive has_reflect]
inductive form 
| eq  : preterm → preterm → form
| le  : preterm → preterm → form
| not : form → form
| or  : form → form → form
| and : form → form → form

notation x `=*` y := form.eq x y
notation x `≤*` y := form.le x y
notation `¬*` p := form.not p
notation p `∨*` q := form.or p q
notation p `∧*` q := form.and p q

-- | (t =* s) :=
-- | (t ≤* s) :=
-- | (¬* p)   :=
-- | (p ∨* q) := 
-- | (p ∧* q) := 

def valuation.cons (i : int) (v : nat → int) : nat → int
| 0     := i 
| (k+1) := v k

notation i `::` v := valuation.cons i v

open tactic

namespace form

@[omega] def holds (v : nat → int) : form → Prop 
| (t =* s) := t.val v = s.val v
| (t ≤* s) := t.val v ≤ s.val v
| (¬* p)   := ¬ p.holds
| (p ∨* q) := p.holds ∨ q.holds
| (p ∧* q) := p.holds ∧ q.holds

end form

@[omega] def uniclo (p : form) : (nat → int) → nat → Prop 
| v 0     := p.holds v
| v (k+1) := ∀ i : int, uniclo (i::v) k 

namespace form

def fresh_idx : form → nat 
| (t =* s) := max t.fresh_idx s.fresh_idx
| (t ≤* s) := max t.fresh_idx s.fresh_idx
| (¬* p)   := p.fresh_idx
| (p ∨* q) := max p.fresh_idx q.fresh_idx
| (p ∧* q) := max p.fresh_idx q.fresh_idx

--def uniclo (p : form) : Prop := 
--uniclo_core p p.fresh_idx (λ _, 0)

def valid (p : form) : Prop := 
∀ v, holds v p

def sat (p : form) : Prop := 
∃ v, holds v p

def implies (p q : form) : Prop := 
∀ v, (holds v p → holds v q)

def equiv (p q : form) : Prop := 
∀ v, (holds v p ↔ holds v q)

lemma sat_of_implies_of_sat {p q} :
  implies p q → sat p → sat q :=
begin intros h1 h2, apply exists_of_exists h1 h2 end

lemma sat_or {p q : form} :
  sat (p ∨* q) ↔ sat p ∨ sat q :=
begin
  constructor; intro h1,
  { cases h1 with v h1, cases h1 with h1 h1;
    [left,right]; refine ⟨v,_⟩; assumption },
  { cases h1 with h1 h1; cases h1 with v h1;
    refine ⟨v,_⟩; [left,right]; assumption }
end

def unsat (p : form) : Prop := ¬ sat p

def repr : form → string 
| (t =* s) := "(" ++ t.repr ++ " = " ++ s.repr ++ ")"
| (t ≤* s) := "(" ++ t.repr ++ " ≤ " ++ s.repr ++ ")"
| (¬* p)   := "¬" ++ p.repr
| (p ∨* q) := "(" ++ p.repr ++ " ∨  " ++ q.repr ++ ")"
| (p ∧* q) := "(" ++ p.repr ++ " ∧ " ++ q.repr ++ ")"

instance has_repr : has_repr form := ⟨repr⟩ 
meta instance has_to_format : has_to_format form := ⟨λ x, x.repr⟩ 

end form

lemma uniclo_of_valid {p : form} : 
  ∀ {m v}, p.valid → uniclo p v m 
| 0 v h1     := h1 _ 
| (m+1) v h1 := λ i, uniclo_of_valid h1

--lemma uniclo_of_valid {p : form} (h : p.valid) : p.uniclo := 
--uniclo_core_of_valid h 

lemma valid_of_unsat_not {p : form} : (¬*p).unsat → p.valid := 
begin
  simp only [form.sat, form.unsat, form.valid, form.holds], 
  rw classical.not_exists_not, intro h, assumption
end

meta def form.induce (t : tactic unit := skip) : tactic unit := 
`[ intro p, induction p with t s t s p ih p q ihp ihq p q ihp ihq; t]

end int