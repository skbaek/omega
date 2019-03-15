import .form ..list

namespace nat

def update (m n) (v : nat → nat) : nat → nat 
| x := if x = m then n else v x

lemma update_eq (m n v) : update m n v m = n :=
begin simp only [update, if_pos rfl] end

lemma update_eq_of_ne {m n v k} : 
  m ≠ k → update m n v k = v k :=
begin
  intro h1, simp only [update],
  rw if_neg h1.symm
end

namespace preterm

def sub_terms : preterm → option (preterm × preterm)
| (& i)      := none
| (i ** n)   := none
| (t +* s) := t.sub_terms <|> s.sub_terms
| (t -* s) := t.sub_terms <|> s.sub_terms <|> some (t,s)

def sub_subst (t s : preterm) (k : nat) : preterm → preterm 
| t@(& m)    := t
| t@(m ** n) := t
| (x +* y) := x.sub_subst +* y.sub_subst
| (x -* y) := 
  if x = t ∧ y = s then (1 ** k)
  else x.sub_subst -* y.sub_subst

lemma val_sub_subst {k x y v} :
  ∀ {t : preterm}, t.fresh_idx ≤ k → 
  (sub_subst x y k t).val 
  (update k (x.val v - y.val v) v) = t.val v 
| (& m)    h1 := rfl
| (m ** n) h1 := 
  begin 
    simp_omega [sub_subst], apply congr_arg,
    apply update_eq_of_ne (ne_of_gt _),
    apply lt_iff_add_one_le.elim_right h1,
 end
| (t +* s) h1 := 
  begin
    simp_omega [sub_subst], apply fun_mono_2;
    apply val_sub_subst (le_trans _ h1), 
    apply le_max_left, apply le_max_right
  end
| (t -* s) h1 := 
  begin
    simp_omega [sub_subst], 
    by_cases h2 : t = x ∧ s = y,
    { rw if_pos h2, simp_omega,
      rw [update_eq, h2.left, h2.right, one_mul] },
    { rw if_neg h2, simp_omega [sub_subst],
      apply fun_mono_2;
      apply val_sub_subst (le_trans _ h1), 
      apply le_max_left, apply le_max_right, }
  end

end preterm

namespace form

def sub_terms : form → option (preterm × preterm)
| (t =* s) := t.sub_terms <|> s.sub_terms
| (t ≤* s) := t.sub_terms <|> s.sub_terms
| (¬* p)   := p.sub_terms
| (p ∨* q) := p.sub_terms <|> q.sub_terms
| (p ∧* q) := p.sub_terms <|> q.sub_terms

@[omega] def sub_subst (x y : preterm) (k : nat) : form → form 
| (t =* s) := preterm.sub_subst x y k t =* preterm.sub_subst x y k s
| (t ≤* s) := preterm.sub_subst x y k t ≤* preterm.sub_subst x y k s
| (¬* p)   := ¬* p.sub_subst
| (p ∨* q) := p.sub_subst ∨* q.sub_subst
| (p ∧* q) := p.sub_subst ∧* q.sub_subst

end form

def is_diff (t s k) : form := 
((t =* (s +* (1 ** k))) ∨* (t ≤* s ∧* ((1 ** k) =* &0))) 

lemma holds_is_diff {t s : preterm} {k} {v : nat → nat} :
  v k = t.val v - s.val v → (is_diff t s k).holds v := 
begin
  intro h1, simp_omega [is_diff, if_pos (eq.refl 1)],
  by_cases h2 : t.val v ≤ s.val v, 
  { right, refine ⟨h2,_⟩, 
    rw [h1, one_mul, nat.sub_eq_zero_iff_le], exact h2 },
  { left, rw [h1, one_mul, add_comm, nat.sub_add_cancel _], 
    rw not_le at h2, apply le_of_lt h2 }
end

def sub_elim_core (t s k) (p : form) : form := 
(form.sub_subst t s k p) ∧* (is_diff t s k)

def sub_fresh_idx (t s : preterm) (p : form) : nat :=
max p.fresh_idx (max t.fresh_idx s.fresh_idx) 

def sub_elim (t s) (p : form) : form := 
-- sub_elim_core t s p.fresh_idx p
sub_elim_core t s (sub_fresh_idx t s p) p

lemma sub_subst_equiv {k} {x y : preterm} {v} :
  ∀ p : form, p.fresh_idx ≤ k → ((form.sub_subst x y k p).holds 
    (update k (x.val v - y.val v) v) ↔ (p.holds v)) 
| (t =* s) h1 := 
  begin
    simp_omega, apply pred_mono_2;
    apply preterm.val_sub_subst (le_trans _ h1),
    apply le_max_left, apply le_max_right
  end
| (t ≤* s) h1 := 
  begin
    simp_omega, apply pred_mono_2;
    apply preterm.val_sub_subst (le_trans _ h1),
    apply le_max_left, apply le_max_right
  end
| (¬* p) h1 :=  
  by { apply not_iff_not_of_iff, apply sub_subst_equiv p h1 } 
| (p ∨* q) h1 := 
  begin
    simp_omega, apply pred_mono_2; apply propext;
    apply sub_subst_equiv _ (le_trans _ h1),
    apply le_max_left, apply le_max_right
  end
| (p ∧* q) h1 := 
  begin
    simp_omega, apply pred_mono_2; apply propext;
    apply sub_subst_equiv _ (le_trans _ h1),
    apply le_max_left, apply le_max_right
  end

lemma sat_sub_elim {t s} {p : form} :
  p.sat → (sub_elim t s p).sat := 
begin
  intro h1, simp only [sub_elim, sub_elim_core], 
  cases h1 with v h1, 
  refine ⟨update (sub_fresh_idx t s p) (t.val v - s.val v) v, _⟩, 
  constructor,
  { apply (sub_subst_equiv p _).elim_right h1,
    apply le_max_left },
  { apply holds_is_diff, rw update_eq, 
    apply sub_eq_sub_of_eq_of_eq;
    apply preterm.val_constant; intros x h2;
    rw update_eq_of_ne; apply ne_of_gt;
    apply lt_of_lt_of_le h2;
    apply le_trans _ (le_max_right _ _),
    apply le_max_left, apply le_max_right }
end

lemma unsat_of_unsat_sub_elim (t s p) :
  (sub_elim t s p).unsat → p.unsat := 
not_of_imp_of_not sat_sub_elim

end nat