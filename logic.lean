import logic.basic

variables {α : Type} {p q r s : Prop}

lemma imp_of_imp (p) {q} : (p → q) → (p → q) := id

lemma exists_of_exists {α : Type} {p q : α → Prop} :
  (∀ a, p a → q a) → (∃ a, p a) → (∃ a, q a) :=
begin
  intros h1 h2, cases h2 with w h2, refine ⟨w,_⟩, 
  apply h1, assumption
end

lemma exists_iff_exists {α : Type} {p q : α → Prop} :
  (∀ a, p a ↔ q a) → ((∃ a, p a) ↔ ∃ a, q a) :=
begin
  intro h, constructor; intro h; 
  cases h with a ha; existsi a; 
  [{rw (h a).symm}, {rw h}]; assumption
end

lemma forall_iff_forall {α : Type} {p q : α → Prop} :
  (∀ a, p a ↔ q a) → ((∀ a, p a) ↔ (∀ a, q a)) :=
begin
  intro h1, constructor; intros h2 a;
  [{rw (h1 a).symm}, {rw h1}]; apply h2
end 

lemma and_of_and : (p → q) → (r → s) → (p ∧ r) → (q ∧ s) :=
begin
  intros h1 h2 h3, cases h3 with h3 h4,
  apply and.intro (h1 h3) (h2 h4)
end

lemma or_iff_or {p p' q q' : Prop} :
  (p ↔ p') → (q ↔ q') → ((p ∨ q) ↔ (p' ∨ q')) := 
begin
  intros hp hq, rewrite hp, rewrite hq
end

lemma and_iff_and {p p' q q' : Prop} :
  (p ↔ p') → (q ↔ q') → ((p ∧ q) ↔ (p' ∧ q')) := 
begin intros hp hq, rewrite hp, rewrite hq end

lemma ite.rec {p} [hd : decidable p] {q : α → Prop} {f g : α} 
  (hf : p → q f) (hg : ¬ p → q g) : q (@ite p hd α f g) := 
begin
  unfold ite, tactic.unfreeze_local_instances, 
  cases hd with h h, simp, apply hg h, simp, apply hf h
end

lemma of_ite_eq {p} [decidable p] {f g h : α} :
@ite p _ α f g = h → g ≠ h → p := 
begin
  intros h1 h2, by_cases h3 : p,
  assumption, rw if_neg h3 at h1, 
  exfalso, apply h2 h1
end


namespace classical

local attribute [instance] classical.dec 

lemma iff_iff {a b : Prop} : (a ↔ b) ↔ ((¬a ∨ b) ∧ (a ∨ ¬b)) := 
begin
  rw [iff_iff_implies_and_implies a b],
  simp only [imp_iff_not_or, or.comm]
end

lemma imp_iff_not_or {a b : Prop} : a → b ↔ ¬a ∨ b := 
_root_.imp_iff_not_or 

lemma not_exists_not :
  ∀ {p : α → Prop}, (¬∃ (x : α), ¬p x) ↔ ∀ (x : α), p x := 
λ p, _root_.not_exists_not

lemma not_not : ¬¬p ↔ p := _root_.not_not

lemma not_and_distrib : ¬(p ∧ q) ↔ ¬p ∨ ¬q := not_and_distrib

end classical