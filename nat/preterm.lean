import ..simp_omega ..term ..logic ..option ..nat

open tactic

namespace nat 

@[derive has_reflect, derive decidable_eq]
inductive preterm : Type
| cst : nat → preterm 
| var : nat → nat → preterm
| add : preterm → preterm → preterm 
| sub : preterm → preterm → preterm 


notation `&` k := preterm.cst k
infix `**` : 300 := preterm.var 
notation t `+*` s := preterm.add t s
notation t `-*` s := preterm.sub t s

-- | (& m) := sorry
-- | (m ** n) := sorry
-- | (t +* s) := sorry
-- | (t -* s) := sorry

namespace preterm 

meta def induce (tac : tactic unit := tactic.skip) : tactic unit := 
`[ intro t, induction t with m m n t s iht ihs t s iht ihs; tac]

@[omega] def val (v : nat → nat) : preterm → nat 
| (& i) := i
| (i ** n) := 
  if i = 1 
  then v n
  else (v n) * i
| (t1 +* t2) := t1.val + t2.val 
| (t1 -* t2) := t1.val - t2.val 

def fresh_idx : preterm → nat 
| (& _)      := 0
| (i ** n)   := n + 1
| (t1 +* t2) := max t1.fresh_idx t2.fresh_idx 
| (t1 -* t2) := max t1.fresh_idx t2.fresh_idx 

def repr : preterm → string 
| (& i)      := i.repr
| (i ** n)   := i.repr ++ "*x" ++ n.repr
| (t1 +* t2) := "(" ++ t1.repr ++ " + " ++ t2.repr ++ ")"
| (t1 -* t2) := "(" ++ t1.repr ++ " - " ++ t2.repr ++ ")"

@[omega] def succ (t : preterm) : preterm := t +* (&1)

def sub_free : preterm → Prop 
| (& m)    := true
| (m ** n) := true
| (t +* s) := t.sub_free ∧ s.sub_free
| (_ -* _) := false

/-
def sub_count : preterm → nat
| (& i)      := 0
| (i ** n)   := 0
| (t1 +* t2) := t1.sub_count + t2.sub_count
| (t1 -* t2) := 1 + t1.sub_count + t2.sub_count 

def sub_terms : preterm → option (preterm × preterm)
| (& i)      := none
| (i ** n)   := none
| (t +* s) := t.sub_terms <|> s.sub_terms
| (t -* s) := t.sub_terms <|> s.sub_terms <|> some (t,s)


def sub_subst (t s r : preterm) : preterm → preterm 
| t@(& m)    := t
| t@(m ** n) := t
| (x +* y) := x.sub_subst +* y.sub_subst
| (x -* y) := 
  if x = t ∧ y = s then r
  else x.sub_subst +* y.sub_subst

def sub_occurs (t s : preterm) : preterm → Prop 
| (& m)    := false
| (m ** n) := false
| (x +* y) := x.sub_occurs ∨ y.sub_occurs
| (x -* y) := x.sub_occurs ∨ y.sub_occurs ∨ (x = t ∧ y = s) 

lemma sub_occurs_of_sub_terms_eq {t s} :
∀ r, sub_terms r = some (t,s) → sub_occurs t s r 
| (m ** n) h1 := by cases h1
| (& m)    h1 := by cases h1
| (x +* y) h1 := 
  begin
    cases (option.orelse_eq' h1) with h2 h2; 
    [left, right]; apply sub_occurs_of_sub_terms_eq; 
    assumption
  end
| (x -* y) h1 := 
  begin
    cases (option.orelse_eq' h1) with h2 h2;
    [left, {cases (option.orelse_eq' h2) with h3 h3; 
     right; [left, {right, cases h3, constructor; refl}]}];
    apply sub_occurs_of_sub_terms_eq; assumption
  end

lemma sub_free_of_sub_count_zero : 
  ∀ {t}, sub_count t = 0 → sub_free t 
| (& m)    h1 := trivial
| (m ** n) h1 := trivial
| (t +* s) h1 := 
  begin
    simp only [sub_count, add_eq_zero_iff] at h1, 
    cases h1, constructor; 
    apply sub_free_of_sub_count_zero; 
    assumption,
  end
| (_ -* _) h1 := 
  begin simp [sub_count] at h1, cases h1 end

lemma sub_terms_is_none' :
  ∀ t, (sub_terms t).is_none' ↔ sub_free t 
| (& m)    := iff_of_left_of_right dec_trivial trivial
| (m ** n) := iff_of_left_of_right dec_trivial trivial
| (t +* s) := 
  begin
    simp only [sub_terms, option.orelse_is_none', sub_free], 
    apply and_iff_and; apply sub_terms_is_none'
  end
| (t -* s) :=
  begin
    apply iff_of_not_of_not; simp only [sub_terms, sub_free], 
    rw [option.not_is_none'],
    repeat {apply option.orelse_is_some'_of_right}, 
    trivial, trivial
  end 

lemma sub_count_sub_subst_le {x y z : preterm} :
  ∀ t : preterm, z.sub_count ≤ 1 → 
  sub_count (sub_subst x y z t) ≤ sub_count t 
| (& m) h1    := le_refl _
| (m ** n) h1 := le_refl _
| (t +* s) h1 := 
  begin
    simp only [sub_count, sub_subst], apply add_le_add; 
    apply sub_count_sub_subst_le; assumption,
  end
| (t -* s) h1 := 
  begin
    simp only [sub_count, sub_subst], 
    by_cases h2 : t = x ∧ s = y,
    { rw if_pos h2, apply le_trans h1,
      rw add_assoc, apply nat.le_add_right },
    { rw [if_neg h2, add_assoc],
      apply le_trans _ (nat.le_add_left _ _),
      simp only [sub_count, sub_subst], apply add_le_add; 
      apply sub_count_sub_subst_le; assumption }
  end

lemma sub_count_sub_subst_lt {x y z : preterm} :
  ∀ t : preterm, z.sub_count = 0 → sub_occurs x y t → 
  sub_count (sub_subst x y z t) < sub_count t 
| (m ** n) h1 h2 := by cases h2
| (& m)    h1 h2 := by cases h2
| (t +* s) h1 h2 := 
  begin
    apply nat.add_lt_add_of_le_of_le_of_lt_or_lt,
    repeat {apply sub_count_sub_subst_le, rw h1, exact_dec_trivial },
    apply or_of_or _ _ h2,
    repeat {apply sub_count_sub_subst_lt _ h1}
  end
| (t -* s) h1 h2 := 
  begin
    simp only [sub_count, sub_subst],
    by_cases h3 : t = x ∧ s = y,
    { rw [if_pos h3, h1, add_assoc], 
      apply lt_of_lt_of_le zero_lt_one, 
      apply le_add_right },
    { rw [if_neg h3], apply lt_of_le_of_lt
        (sub_count_sub_subst_le (t +* s) _),
      rw [add_assoc, sub_count, add_comm 1], apply lt_add_one,
      rw h1, apply zero_le }
  end
-/
end preterm

@[omega] def canonize : preterm → term 
| (& m)    := ⟨↑m,[]⟩  
| (m ** n) := ⟨0,[]{n ↦ ↑m}⟩ 
| (t +* s) := term.add (canonize t) (canonize s)
| (_ -* _) := ⟨0,[]⟩ -- Irr.

@[omega] lemma val_canonize {v : nat → nat} : 
  ∀ {t : preterm}, t.sub_free → 
  (canonize t).val (λ x, ↑(v x)) = t.val v
| (& i) h1 := by simp_omega
| (i ** n) h1 := 
  begin 
    simp_omega, 
    rw [← int.coe_nat_mul],
    apply congr_arg,
    apply ite.rec; intro h1,
    { simp only [one_mul, h1] },
    { rw mul_comm }
  end
| (t +* s) h1 := 
  by simp_omega [val_canonize h1.left, 
    val_canonize h1.right, int.coe_nat_add]

end nat
