variable {α : Type}

def update (m a) (v : nat → α) : nat → α 
| n := if n = m then a else v n

notation v `⟨` m `↦` a `⟩` := update m a v

lemma update_eq (m a) (v : nat → α) : (v ⟨m ↦ a⟩) m = a :=
begin simp only [update, if_pos rfl] end

lemma update_eq_of_ne {m a} {v : nat → α} (k) : 
  k ≠ m → update m a v k = v k :=
begin intro h1, simp only [update], rw if_neg h1 end