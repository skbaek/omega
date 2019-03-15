import .coeffs

--tactic.ring
--.simp_omega
--.int
--.logic
--.valuation
--
-- open list

def term : Type := int × coeffs 

namespace term

def neg : term → term 
| (b,as) := (-b, as.neg) 

def div (i : int) : term → term 
| (b,as) := (b/i, list.div₁ i as) 

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
--
--def subscript_digits (ds : string) : string := 
--⟨ds.data.map subscript_digit⟩  
--
--def to_string_monomial (m : nat) (i : int) : string :=
--i.repr ++ "x" ++ subscript_digits m.repr
--
--def to_string_aux : nat → list int → string 
--| m []      := ""
--| m [i]     := to_string_monomial m i 
--| m (i::is) := to_string_monomial m i ++ " + " ++ to_string_aux (m+1) is
--
--def repr (t : term) : string :=
--t.fst.repr ++ " + " ++ to_string_aux 0 t.snd
--
--instance has_repr : has_repr term := ⟨repr⟩  
--
--meta instance has_to_format : has_to_format term := ⟨λ t, repr t⟩ 

@[omega] def val (v : nat → int) : term → int 
| (b,as) := b + coeffs.val v as

@[omega] def add : term → term → term 
| (c1,cfs1) (c2,cfs2) := (c1+c2, list.add cfs1 cfs2) 

@[omega] def sub : term → term → term 
| (c1,cfs1) (c2,cfs2) := (c1 - c2, list.sub cfs1 cfs2) 

-- lemma sub_const {t1 t2 : term} :
--   (sub t1 t2).const = t1.const - t2.const := rfl
-- 
-- lemma sub_coeffs {t1 t2 : term} :
--   (sub t1 t2).coeffs = list.sub t1.coeffs t2.coeffs := rfl

lemma val_neg {v} {t : term} :
(neg t).val v = - (t.val v) := sorry

lemma val_div {v i} {b as} :
i ∣ b → (∀ x ∈ as, i ∣ x) → 
(div i (b,as)).val v = (val v (b,as)) / i := sorry

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

def mul (i : int) : term → term 
| (b,as) := (i * b, as.map ((*) i))

@[omega] lemma val_mul {v i t} :
val v (mul i t) = i * (val v t) := 
begin 
  cases t, simp_omega [mul, mul_add, add_mul,
  coeffs.val, list.length_map],
end

def fresh_idx (t : term) : nat := t.snd.length

def terms.fresh_idx : list term → nat 
| []      := 0
| (t::ts) := max t.fresh_idx (terms.fresh_idx ts)

#exit
lemma val_eq_of_eq_upto (v w) (t : term) : 
eq_upto t.fresh_idx v w → t.val v = t.val w  :=
begin
  cases t with b as, simp only [val], intro h1,
  apply congr_arg, apply coeffs.val_eq_val_of_eq_upto,
  --rw [zero_add], 
  apply h1
end

-- #exit
-- lemma val_div {v i} {t : term} :
--   i ∣ t.const → (∀ x ∈ t.snd, i ∣ x) → 
--   val v (div i t) = (val v t) / i := 
-- begin
--   intros h1 h2, cases t with c cfs, 
--   simp_omega [div],
-- end

lemma eq_const {v} {t : term} :
  (∀ (x : ℤ), x ∈ t.snd → x = 0) → t.val v = t.fst :=
begin
  intros h1, cases t with c cfs, simp_omega at *,
  have h3 : coeffs.val v cfs = 0 := coeffs.val_eq_zero h1,
  rw [h3, add_zero]
end

end term
