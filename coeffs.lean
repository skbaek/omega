import .simp_omega .list tactic.ring
  .valuation .logic

@[reducible] def coeffs : Type := list int

namespace coeffs

@[omega] def val_btw (v : nat → int) (as : coeffs) (l : nat) : nat → int 
| 0     := 0 
| (o+1) := (val_btw o) + (as.get (l+o) * v (l+o))

def val (v as) : int := val_btw v as 0 as.length

lemma val_btw_eq_of_le {as : coeffs} {v l} : 
  ∀ m, as.length ≤ l + m → 
  val_btw v as l m = val_btw v as l (as.length - l) 
| 0 h1 := 
  begin rw (nat.sub_eq_zero_iff_le.elim_right _), apply h1 end
| (m+1) h1 := 
  begin
    rw le_iff_eq_or_lt at h1, cases h1,
    { rw [h1, add_comm l, nat.add_sub_cancel] },
    { simp only [val_btw], 
      have h2 :  list.length as ≤ l + m, 
      { rw ← nat.lt_succ_iff, apply h1 },
      rw [list.get_eq_zero_of_le _ h2, zero_mul, add_zero],
      apply val_btw_eq_of_le _ h2 } 
  end

lemma val_eq_of_le {as : coeffs} {v k} : 
  as.length ≤ k → val v as = val_btw v as 0 k :=
begin
  intro h1, simp only [val], 
  rw [val_btw_eq_of_le k _], refl, 
  rw zero_add, exact h1
end

--@[omega] def val_under (as : coeffs) (v : nat → int) : nat → int 
--| 0     := 0 
--#exit

-- def val_btw_set {v a m} :
--   ∀ l h, 
--   ((0 ≤ m → m < h → val_under ([]{m ↦ a}) v n = a * v m) ∧   
--    (n ≤ m → val_under ([]{m ↦ a}) v n = 0))
-- | 0 := begin constructor; intro h1, cases h1, refl end  
-- | (n+1) := 
--   begin constructor; intro h1,
--     { rw [nat.lt_succ_iff, le_iff_eq_or_lt] at h1, cases h1, 
--       { simp_omega, rw [← h1, list.get_set,
--           (val_under_set m).right (le_refl _), zero_add] },
--       { simp_omega, rw [list.get_set_eq_of_ne (ne_of_lt h1)], 
--         simp_omega, apply (val_under_set n).left h1 } },
--     { simp_omega, rw list.get_set_eq_of_ne _, 
--       simp_omega, apply (val_under_set n).right, 
--       apply le_trans _ h1, apply nat.le_add_right,
--       apply ne.symm, apply ne_of_lt, 
--       rw ← nat.succ_le_iff, apply h1 }
--   end
-- 
-- @[omega] def val_set {v m a} : 
--   val ([]{m ↦ a}) v = a * v m := 
-- begin
--   simp only [val],
--   apply (val_under_set _ ).left, 
--   rw list.length_set, 
--   apply lt_of_lt_of_le _ (le_max_right _ _),
--   apply lt_add_one,
-- end

lemma val_btw_neg {as v l} : 
  ∀ {o}, val_btw v (list.neg as) l o = -(val_btw v as l o)
| 0 := rfl
| (o+1) := 
  begin
    simp only [val_btw], 
    rw [neg_add, neg_mul_eq_neg_mul],
    apply fun_mono_2, apply val_btw_neg,
    apply fun_mono_2 _ rfl, apply list.get_neg
  end

@[omega] lemma val_neg {as v} :
   val v (list.neg as) = -(val v as) := begin
  simp only [val, list.length_neg],
  apply val_btw_neg
end

lemma val_btw_add {is js v l} : 
  ∀ m, val_btw v (list.add is js) l m = 
  (val_btw v is l m) + (val_btw v js l m) 
| 0 := rfl
| (m+1) := begin simp_omega [val_btw_add m], ring end

@[omega] lemma val_add {v} {is js : coeffs} : 
  val v (list.add is js) = (val v is) + (val v js) :=
begin
  simp only [val],
   rw val_btw_add, apply fun_mono_2;
  apply val_btw_eq_of_le;
  rw [zero_add, list.length_add],
  apply le_max_left, apply le_max_right
end

lemma val_btw_sub {is js v l} : 
  ∀ m, val_btw v (list.sub is js) l m = 
  (val_btw v is l m) - (val_btw v js l m) 
| 0 := rfl
| (m+1) := begin simp_omega [val_btw_sub m], ring end

@[omega] lemma val_sub {v} {is js : coeffs} : 
  val v (list.sub is js) = (val v is) - (val v js) :=
begin
  simp only [val],
   rw val_btw_sub, apply fun_mono_2;
  apply val_btw_eq_of_le;
  rw [zero_add, list.length_sub],
  apply le_max_left, apply le_max_right
end


def val_except (n v as) := 
val_btw v as 0 n + val_btw v as (n+1) (as.length - (n+1))

lemma val_btw_eq_val_btw {v w : nat → int} {as bs : coeffs} {l} :
  ∀ {m}, (∀ x, l ≤ x → x < l + m → v x = w x) → 
    (∀ x, l ≤ x → x < l + m → as.get x = bs.get x) → 
    val_btw v as l m = val_btw w bs l m 
| 0 h1 h2 := rfl
| (m+1) h1 h2 :=
  begin
    simp only [val_btw], 
    have h3 : l + m < l + (m + 1), 
    { rw ← add_assoc, apply lt_add_one },
    apply fun_mono_2,
    apply val_btw_eq_val_btw; intros x h4 h5,
    { apply h1 _ h4 (lt_trans h5 h3) },
    { apply h2 _ h4 (lt_trans h5 h3) },
    rw [h1 _ _ h3, h2 _ _ h3];
    apply nat.le_add_right
  end

lemma val_except_eq_val_except 
  {k : nat} {is js : coeffs} {v w : nat → int} :
  (∀ x ≠ k, v x = w x) → (∀ x ≠ k, is.get x = js.get x) → 
  val_except k v is = val_except k w js :=
begin
  intros h1 h2, simp only [val_except],
  apply fun_mono_2, 
  { apply val_btw_eq_val_btw; intros x h3 h4;
    [ {apply h1}, {apply h2} ]; apply ne_of_lt;
    rw zero_add at h4; apply h4 },
  { repeat { rw ← val_btw_eq_of_le 
      ((max is.length js.length) - (k+1)) }, 
    { apply val_btw_eq_val_btw; intros x h3 h4;
      [ {apply h1}, {apply h2} ]; apply ne.symm;
        apply ne_of_lt; rw nat.lt_iff_add_one_le; exact h3 },
    repeat { rw add_comm, apply le_trans _ (nat.le_sub_add _ _), 
      { apply le_max_right <|> apply le_max_left } } }
end

lemma val_except_update_set {n v as i j} :
  val_except n (v⟨n ↦ i⟩) (as{n ↦ j}) = val_except n v as :=
by rw val_except_eq_val_except update_eq_of_ne list.get_set_eq_of_ne

lemma val_btw_add_val_btw {v as l m} :
  ∀ {n}, val_btw v as l m + val_btw v as (l+m) n = 
  val_btw v as l (m+n) 
| 0 := by simp_omega
| (n+1) :=
  begin
    rw ← add_assoc, simp_omega, rw add_assoc, 
    rw ← @val_btw_add_val_btw n, ring
  end

def val_except_add_eq (n) {v as} :
  (val_except n v as) + ((as.get n) * (v n)) = val v as :=
begin
  simp only [val_except, val],
  by_cases h1 : n + 1 ≤ as.length,
  { have h4 := @val_btw_add_val_btw v as 0 (n+1) (as.length - (n+1)),
    have h5 : n + 1 + (as.length - (n + 1)) = as.length,
    { rw [add_comm, nat.sub_add_cancel h1] },
    rw h5 at h4, apply eq.trans _ h4,
     simp only [val_btw, zero_add], ring },
  { rw not_lt at h1,
    have h2 : (list.length as - (n + 1)) = 0,
    { apply nat.sub_eq_zero_of_le 
      (le_trans h1 (nat.le_add_right _ _)) },
    rw h2, simp only [val_btw, add_zero],  
    have h3 := @val_eq_of_le as v (n+1) _, 
    simp only [val] at h3, rw h3, 
    simp only [val_btw, zero_add],
    apply le_trans h1, apply nat.le_add_right }
end

@[omega] lemma val_btw_map_mul {v i as l m} :
  val_btw v (list.map ((*) i) as) l m = i * val_btw v as l m := sorry

  #exit
@[omega] lemma val_mul₁ {v i is} :
  val v (i *₁ is) = i * val v is :=  sorry

| n     k []      := by simp_omega
| 0     k (i::is) := begin simp_omega, rw add_comm end
| (n+1) k (i::is) := 
  begin
    simp_omega, rw add_assoc, apply congr_arg,
    have h1 := val_except_core_add_eq n (k+1) is,
    have h2 : n + 1 + k = n + (k + 1) :=
      by rw [add_comm k, ← add_assoc],
    rw h2, exact h1
  end

lemma val_except_add_eq (n) {v cs} :
  val_except v n cs + (cs.get n) * (v n) = val v cs := 
by apply val_except_core_add_eq

lemma val_except_core_eq_zero {v} :
#exit
lemma val_btw_mul₁ {v i} :
  ∀ {m is}, val_btw v m (i *₁ is) = i * val_btw v m is 
| m [] := by simp_omega
| m (j::is) := begin simp_omega, rw val_btw_mul₁, ring end 


lemma dvd_val_btw {j} (v) :
  ∀ {is} n, (∀ x ∈ is, j ∣ x) → (j ∣ val_btw v n is)
| [] _ h := begin simp_omega, apply dvd_zero, end
| (i::is) n h := 
  begin
    simp_omega, apply dvd_add,
    apply dvd_mul_of_dvd_left (h _ (or.inl rfl)),
    apply dvd_val_btw _ (list.forall_mem_of_forall_mem_cons h) 
  end

lemma dvd_val {is j v} : (∀ x ∈ is, j ∣ x) → (j ∣ val v is) := 
by apply dvd_val_btw

lemma val_btw_eq_zero {v} : 
  ∀ {is m}, (∀ x : int, x ∈ is → x = 0) → val_btw v m is = 0 
| []      m _  := rfl
| (i::is) m h1 :=
  begin
    simp_omega, rw [h1 _ (or.inl rfl), val_btw_eq_zero 
      (list.forall_mem_of_forall_mem_cons h1)], simp
  end

lemma val_eq_zero {v is} : 
  (∀ x : int, x ∈ is → x = 0) → val v is = 0 :=
by apply val_btw_eq_zero

lemma val_btw_eq_val_btw_of_eq_upto (v w) :
  ∀ k (is : list int), eq_upto (k + is.length) v w → 
  val_btw v k is = val_btw w k is 
| k []      h1 := rfl 
| k (i::is) h1 :=
  begin
    simp only [val_btw], apply fun_mono_2,  
    apply congr_arg, apply h1, apply nat.lt_add_of_pos_right,
    apply nat.succ_pos, apply val_btw_eq_val_btw_of_eq_upto,
    rw [add_assoc, add_comm 1], apply h1 
  end

lemma val_eq_val_of_eq_upto {v w} {is : coeffs} :
  eq_upto is.length v w → val v is = val w is :=
begin
  intro h1, apply val_btw_eq_val_btw_of_eq_upto, 
  rw zero_add, exact h1
end

@[omega] def val_except_core (v : nat → int) : nat → nat → coeffs → int 
| _     _ []      := 0
| 0     k (i::is) := val_btw v (k+1) is
| (n+1) k (i::is) := i * (v k) + val_except_core n (k+1) is

@[omega] lemma val_except_core_nil {v n k} :
  val_except_core v n k [] = 0 :=
begin cases n; refl end

def val_except (v n cs) := val_except_core v n 0 cs

def val_except_core_add_eq (v : nat → int) : 
  ∀ (n k : nat) (cs : list int), 
  ((val_except_core v n k cs) + ((cs.get n) * (v (n+k))) = (val_btw v k cs))
| n     k []      := by simp_omega
| 0     k (i::is) := begin simp_omega, rw add_comm end
| (n+1) k (i::is) := 
  begin
    simp_omega, rw add_assoc, apply congr_arg,
    have h1 := val_except_core_add_eq n (k+1) is,
    have h2 : n + 1 + k = n + (k + 1) :=
      by rw [add_comm k, ← add_assoc],
    rw h2, exact h1
  end

lemma val_except_add_eq (n) {v cs} :
  val_except v n cs + (cs.get n) * (v n) = val v cs := 
by apply val_except_core_add_eq

lemma val_except_core_eq_zero {v} :
  ∀ {n k is}, (∀ x ≠ n, list.get x is = (0 : int)) → val_except_core v n k is = 0
| n k [] h1 := by simp_omega
| 0 k (i::is) h1 :=
  begin 
    simp_omega, apply val_btw_eq_zero,
    intros x h2, cases (list.eq_get_of_mem h2) with m h3,
    rw h3, apply h1 (m+1) (nat.succ_ne_zero _)
  end
| (n+1) k (i::is) h1 :=
  begin
    have h2 : i = 0 := (h1 0 (nat.succ_ne_zero _).symm),
    simp_omega [h2], apply val_except_core_eq_zero,
    intros x h3, apply h1 (x+1) _, simp [h3]
  end

lemma val_btw_eq_val_btw_of_equiv {v} : 
  ∀ {k} {is js : list int}, list.equiv is js → 
  val_btw v k is = val_btw v k js
| k [] [] h1 := rfl 
| k is [] h1 := 
  begin
    simp_omega, apply val_btw_eq_zero, 
    intros i h2, cases (list.eq_get_of_mem h2) with m h3,
    rw h3, have h4 := h1 m, simp only [list.get_nil] at h4,
    exact h4
  end
| k [] js h1 := 
  begin
    simp_omega, apply eq.symm, apply val_btw_eq_zero, 
    intros i h2, cases (list.eq_get_of_mem h2) with m h3,
    rw h3, have h4 := h1 m, simp only [list.get_nil] at h4,
    exact h4.symm
  end
| k (i::is) (j::js) h1 := 
  begin
    simp_omega, have h2 : i = j := (h1 0), rw h2,
    apply congr_arg, apply val_btw_eq_val_btw_of_equiv,
    intros m, apply h1 (m+1)
  end

lemma val_except_core_eq_val_except_core {v w : nat → int} :
  ∀ n k (is js : list int), eq_except (n+k) v w → 
  (∀ x ≠ n, is.get x = js.get x) → 
  val_except_core v n k is = val_except_core w n k js 
| n k is [] h1 h2 := 
  begin
    simp_omega, simp only [list.get_nil] at h2,
    apply val_except_core_eq_zero h2
  end 
| n k [] js h1 h2 := 
  begin
    simp_omega, simp only [list.get_nil] at h2,
    apply eq.symm, apply val_except_core_eq_zero, 
    intros x h3, apply (h2 x h3).symm
  end 
| 0 k (i::is) (j::js) h1 h2 :=  
  begin
    simp_omega, apply val_btw_eq_val_btw_of_equiv _,
  end 
| (n+1) k (i::is) (j::js) h1 h2 := sorry 

#exit
lemma val_except_eq_val_except {n} {v w : nat → int} {cs} : 
  eq_except n v w → val_except n v cs = val_except n w cs := 
begin

end



#exit
def val_btw_wo (n) (v is) := val_btw v 0 is - ((is.get n) * v n)

lemma val_btw_wo_add_eq (n v is) :
  val_btw_wo n v is + ((is.get n) * v n) = val_btw v 0 is :=
begin simp only [val_wo, sub_add_cancel] end
end coeffs