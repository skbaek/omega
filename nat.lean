import data.nat.basic

namespace nat

lemma lt_iff_add_one_le {m n : ℕ} :
  m < n ↔ m + 1 ≤ n  := by rw succ_le_iff

lemma add_lt_add_of_le_of_le_of_lt_or_lt {a b c d : nat} :
  a ≤ b → c ≤ d → (a < b ∨ c < d) → a + c < b + d := 
begin
  intros h1 h2 h3, cases h3,
  apply add_lt_add_of_lt_of_le; assumption,
  apply add_lt_add_of_le_of_lt; assumption
end

lemma max_succ_succ {m n} : 
  max (succ m) (succ n) = succ (max m n) :=
begin
  by_cases h1 : m ≤ n, 
  rw [max_eq_right h1, max_eq_right (succ_le_succ h1)], 
  { rw not_le at h1, have h2 := le_of_lt h1,
    rw [max_eq_left h2, max_eq_left (succ_le_succ h2)] }
end

#exit
| 0 n := 
  begin
    rw [max_eq_right, max_eq_right];
    simp only [zero_le, succ_le_succ_iff]
  end
| m 0 := 
  begin
    rw [max_eq_left, max_eq_left];
    simp only [zero_le, succ_le_succ_iff]
  end
| (succ m) (succ n) :=
  begin
  end

end nat