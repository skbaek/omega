import .list .nat .int .logic .preterm tactic.ring

open list

@[derive has_reflect, derive decidable_eq]
structure term := 
(const : int) (coeffs : list int)

@[omega] def val_aux (v : nat → int) : nat → list int → int 
| _ []      := 0 
| d (i::is) := i * v d + val_aux (d+1) is

@[omega] def val_aux_set {v i} :
  ∀ {m n}, val_aux v m ([]{n ↦ i}) = i * v (n + m) 
| 0 0 := by simp_omega 
| 0 (n+1) := begin simp_omega, apply @val_aux_set 1 n end
| (m+1) 0 := by simp_omega
| (m+1) (n+1) :=
  begin 
    simp with omega,
    have heq : m + (n + 2) = n + (m + 2) := by ring,
    rw heq, apply @val_aux_set (m+2) n, 
  end

@[omega] lemma val_aux_neg {v} : 
  ∀ {m is}, val_aux v m (list.neg is) = -(val_aux v m is) 
| m []      := by simp_omega
| m (i::is) := begin simp_omega, rw val_aux_neg, simp end

@[omega] lemma val_aux_add {v} : 
  ∀ {m is js}, val_aux v m (list.add is js) = 
  (val_aux v m is) + (val_aux v m js)
| m []      []      := by simp_omega
| m []      (j::hs) := begin simp_omega end
| m (i::is) []      := begin simp_omega end
| m (i::is) (j::hs) := begin simp_omega, rw val_aux_add, ring end

@[omega] lemma val_aux_sub {v} : 
  ∀ {m is js}, val_aux v m (list.sub is js) = 
  (val_aux v m is) - (val_aux v m js)
| m []      []      := by simp_omega
| m []      (j::hs) := begin simp_omega, simp end
| m (i::is) []      := begin simp_omega end
| m (i::is) (j::hs) := begin simp_omega, rw val_aux_sub, ring end

-- @[omega] lemma val_aux_sub' {v} : 
--   ∀ {m is js}, val_aux v m (ints.sub is js) = 
--   (val_aux v m is) - (val_aux v m js) := sorry

@[omega] lemma val_aux_mul₁ {v i} :
  ∀ {m is}, val_aux v m (i *₁ is) = i * val_aux v m is 
| m [] := by simp_omega
| m (j::is) := begin simp_omega, rw val_aux_mul₁, ring end 

lemma dvd_val_aux {j v} :
  ∀ {is n}, (∀ x ∈ is, j ∣ x) → (j ∣ val_aux v n is)
| [] _ h := begin simp_omega, apply dvd_zero, end
| (i::is) n h := 
  begin
    simp_omega, apply dvd_add,
    apply dvd_mul_of_dvd_left (h _ (or.inl rfl)),
    apply dvd_val_aux (forall_mem_of_forall_mem_cons h) 
  end

lemma val_aux_eq_zero {v} : 
  ∀ {is m}, (∀ x : int, x ∈ is → x = 0) → val_aux v m is = 0 
| [] m _ := rfl
| (i::is) m h1 :=
  begin
    simp_omega, rw [h1 _ (or.inl rfl), 
      val_aux_eq_zero (list.forall_mem_of_forall_mem_cons h1)], simp
  end

namespace term

def div (i : int) : term → term 
| ⟨c,cfs⟩ := ⟨c/i, div₁ i cfs⟩ 

def neg : term → term 
| ⟨b,as⟩ := ⟨-b, list.neg as⟩ 

def subscript_digit : char → char 
| '0' := '₀'
| '1' := '₁'
| '2' := '₂'
| '3' := '₃'
| '4' := '₄'
| '5' := '₅'
| '6' := '₆'
| '7' := '₇'
| '8' := '₈'
| '9' := '₉'
| c := c

def subscript_digits (ds : string) : string := 
⟨ds.data.map subscript_digit⟩ 

meta def to_string_monomial (m : nat) (i : int) : string :=
(to_fmt i).to_string ++ "x" ++ subscript_digits (to_fmt m).to_string 

meta def to_string_aux : nat → list int → string 
| m []      := ""
| m [i]     := to_string_monomial m i 
| m (i::is) := to_string_monomial m i ++ " + " ++ to_string_aux (m+1) is

meta def to_string (t : term) : string :=
(to_fmt t.const).to_string ++ " + " ++ to_string_aux 0 t.coeffs

meta instance has_repr : has_repr term := ⟨to_string⟩ 

meta instance has_to_format : has_to_format term := 
⟨λ t, to_string t⟩ 

@[omega] def val (v : nat → int) : term → int 
| ⟨c,cfs⟩ := c + val_aux v 0 cfs

@[omega] def add : term → term → term 
| ⟨c1,cfs1⟩ ⟨c2,cfs2⟩ := ⟨c1+c2, list.add cfs1 cfs2⟩ 

@[omega] def sub : term → term → term 
| ⟨c1,cfs1⟩ ⟨c2,cfs2⟩ := ⟨c1 - c2, list.sub cfs1 cfs2⟩ 

-- lemma sub_const {t1 t2 : term} :
--   (sub t1 t2).const = t1.const - t2.const := rfl
-- 
-- lemma sub_coeffs {t1 t2 : term} :
--   (sub t1 t2).coeffs = list.sub t1.coeffs t2.coeffs := rfl

@[omega] lemma val_sub {v} {t1 t2 : term} :
(sub t1 t2).val v = t1.val v - t2.val v :=
begin 
  cases t1, cases t2,
  simp_omega, ring, 
end

@[omega] lemma val_add {v} {t1 t2 : term} :
(add t1 t2).val v = t1.val v + t2.val v :=
begin 
  cases t1, cases t2,
  simp_omega, ring, 
end

def mul (i : int) (t : term) := 
{t with const := i * t.const, coeffs := i *₁ t.coeffs}

@[omega] lemma val_mul {v i t} :
val v (mul i t) = i * (val v t) := 
begin cases t, simp_omega [mul, mul_add, add_mul] end

def factor : term → option term 
| ⟨c,cfs⟩ := 
  let i : int := ↑(ints.gcd cfs) in
  if i ∣ c 
  then some (div i ⟨c,cfs⟩) 
  else none

def fresh_idx (t : term) : nat := t.coeffs.length

-- #exit
-- lemma val_div {v i} {t : term} :
--   i ∣ t.const → (∀ x ∈ t.coeffs, i ∣ x) → 
--   val v (div i t) = (val v t) / i := 
-- begin
--   intros h1 h2, cases t with c cfs, 
--   simp_omega [div],
-- end


lemma eq_const {v} {t : term} :
  (∀ (x : ℤ), x ∈ t.coeffs → x = 0) → t.val v = t.const :=
begin
  intros h1, cases t with c cfs, simp_omega at *,
  have h3 : val_aux v 0 cfs = 0 := val_aux_eq_zero h1,
  rw [h3, add_zero]
end

end term

def terms.fresh_idx : list term → nat 
| []      := 0
| (t::ts) := nat.max' t.fresh_idx (terms.fresh_idx ts)

@[omega] def canonize : preterm → term 
| (& i)      := ⟨i,[]⟩  
| (i ** n)   := ⟨0,[]{n ↦ i}⟩ 
| (t1 +* t2) := term.add (canonize t1) (canonize t2)


@[omega] lemma val_canonize {v} : ∀ {t}, (canonize t).val v = t.val v 
| (& i)      := by simp_omega
| (i ** n)   := 
  begin 
    simp_omega, apply ite.rec; intro h1,
    { simp only [one_mul, h1] },
    { apply ite.rec; intro h2, 
      { rw h2, simp },
      { rw mul_comm } }
  end
| (t1 +* t2) := by simp_omega [@val_canonize t1, @val_canonize t2]

