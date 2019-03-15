import .list data.int.basic .logic

data.int.gcd

namespace int

lemma add_div {a b c : int} : 
c ∣ a → c ∣ b → (a + b) / c = a / c + b / c :=
begin
  intros h1 h2, 
  by_cases h3 : c = 0,
  { rw [h3, zero_dvd_iff] at *, 
    rw [h1, h2, h3], refl },
  { apply eq_of_mul_eq_mul_right h3,
    rw add_mul, repeat {rw [int.div_mul_cancel]};
    try {apply dvd_add}; assumption }
end

end int

def ints.gcd : list int → nat
| []      := 0
| (i::is) := nat.gcd i.nat_abs (ints.gcd is)

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

def symdiv (i j : int) : int := 
if (2 * (i % j)) < j
then i / j
else (i / j) + 1

def symmod (i j : int) : int := 
if (2 * (i % j)) < j
then i % j
else (i % j) - j

lemma symmod_add_one {i} : 
  0 < i → symmod i (i+1) = -1 := 
begin
  intro h1, 
  simp only [symmod],
  rw int.mod_eq_of_lt (le_of_lt h1) (lt_add_one _),
  rw if_neg, simp,
  have h2 : 2 * i = (1 + 1) * i := rfl,
  simp [h2, add_mul], apply h1 
end

lemma mul_symdiv_eq {i j} :
j * (symdiv i j) = i - (symmod i j) := 
begin
  simp only [symdiv, symmod],
  by_cases h1 : (2 * (i % j)) < j,
  { repeat {rw if_pos h1}, 
    rw [int.mod_def, sub_sub_cancel] },
  { repeat {rw if_neg h1},
    rw [int.mod_def, sub_sub, sub_sub_cancel,
      mul_add, mul_one] }
end

lemma symmod_eq {i j} :
  symmod i j = i - j * (symdiv i j) := 
by rw [mul_symdiv_eq, sub_sub_cancel]

#exit
lemma zero_symmod {i} : symmod 0 i = 0 := 
begin
  simp only [symmod], 
  --apply @ite.rec _ _ _ (0 % i) (0 % i - i)  (λ x, x = 0) _ _,
end