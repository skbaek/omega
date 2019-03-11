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

end nat