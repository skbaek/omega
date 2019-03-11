import .list data.int.basic

-- def ints.gcd : list int → nat
-- | []      := 0
-- | (i::is) := nat.gcd i.nat_abs (ints.gcd is)

lemma forall_mem_nil_eq_zero : ∀ x : int, x ∈ ([] : list int) → x = (0 : int) :=
begin intros x h1, cases h1 end

lemma forall_mem_cons_eq_zero (i : int) (is : list int) :
  (i = (0 : int)) → 
  (∀ x : int, x ∈ is → x = (0 : int)) → 
  (∀ x : int, x ∈ (i::is) → x = (0 : int)) := 
begin
  intros h1 h2, rw list.forall_mem_cons,
  constructor; assumption
end

meta instance int.has_reflect : has_reflect int := by tactic.mk_has_reflect_instance