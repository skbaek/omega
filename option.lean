import data.option .logic

variables {α β : Type}

open tactic

namespace option

lemma orelse_eq_none_iff {α : Type} {f g : option α} :
((f <|> g) = none) ↔ (f = none ∧ g = none) :=
begin
  cases h1 : f; cases h2 : g,
  apply iff_of_left_of_right; exact_dec_trivial,
  repeat { apply iff_of_not_of_not; exact_dec_trivial }
end

@[reducible] def is_none' : option α → Prop 
| none     := true
| (some _) := false

def is_some' : option α → Prop 
| none     := false
| (some _) := true

instance is_none'.decidable : 
  ∀ x : option α, decidable x.is_none' 
| none     := decidable.true
| (some _) := decidable.false

instance is_some'.decidable : 
  ∀ x : option α, decidable x.is_some' 
| none     := decidable.false
| (some _) := decidable.true

lemma is_none_iff_eq_none' {o : option α} : is_none' o ↔ o = none :=
by cases o; exact_dec_trivial

lemma not_is_none' {α : Type} {f : option α} :
  ¬ f.is_none' ↔ f.is_some' := by cases f; exact_dec_trivial

lemma not_is_some' {α : Type} {f : option α} :
  ¬ f.is_some' ↔ f.is_none' := by cases f; exact_dec_trivial

lemma orelse_is_none' {α : Type} {f g : option α} :
(f <|> g).is_none' ↔ f.is_none' ∧ g.is_none' :=
begin
  cases h1 : f; cases h2 : g,
  { apply iff_of_left_of_right; exact_dec_trivial },
  repeat { apply iff_of_not_of_not; exact_dec_trivial },
end

lemma orelse_is_some'_of_right {α : Type} {f g : option α} :
g.is_some' → (f <|> g).is_some' :=
begin intro h1, cases f, simp, apply h1, trivial end

lemma orelse_eq (x y : option α) :
  (x <|> y) = x ∨ (x <|> y) = y :=
begin
  cases h1 : x,
  { right, cases y; refl },
  { left, refl }
end

lemma orelse_eq' {x y z : option α} :
  (x <|> y) = z → (x = z ∨ y = z) :=
begin
  intro h1, cases (orelse_eq x y) with h2 h2;
  rw h2 at h1; [left, right]; assumption
end


end option