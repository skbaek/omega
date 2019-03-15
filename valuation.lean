
variable {α : Type}


def update (m a) (v : nat → α) : nat → α 
| n := if n = m then a else v n

notation v `⟨` m `↦` a `⟩` := update m a v

lemma update_eq (m a) (v : nat → α) : (v ⟨m ↦ a⟩) m = a :=
begin simp only [update, if_pos rfl] end

lemma update_eq_of_ne {m a} {v : nat → α} (k) : 
  k ≠ m → update m a v k = v k :=
begin intro h1, simp only [update], rw if_neg h1 end

def eq_upto (m) (v w : nat → α) : Prop := ∀ x < m, v x = w x 

def eq_upto_symm {m} {v w : nat → α} : 
  eq_upto m v w → eq_upto m w v | h1 x h2 := by rw h1 _ h2 

lemma update_eq_upto {k a} {v : nat → α} : 
  eq_upto k (v ⟨k ↦ a⟩) v := 
begin
  intros x h1, rw update_eq_of_ne,
  apply ne_of_lt h1,
end

def eq_except (m : nat) (v w : nat → α) : Prop := ∀ x ≠ m, v x = w x 