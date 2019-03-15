import .simp_omega .valuation

def coeffs : Type := (nat → int) × nat

namespace coeffs

@[omega] def val_core (v c : nat → int) : nat → int 
| 0     := 0 
| (n+1) := (c n) * (v n) + val_core n

def val (v) (c : coeffs) : int := val_core v c.fst c.snd

def set (m i) : coeffs → coeffs | (f,k) := 
(f ⟨m ↦ i⟩, max k (m+1))

def div (i) : coeffs → coeffs | (f,k) := 
(λ x, (f x) / i, k)

def neg : coeffs → coeffs | (f,k) := 
(λ x, -(f x), k)

def add : coeffs → coeffs → coeffs | (f,k) (g,m) := 
(λ x, f x + g x, max k m)

def sub : coeffs → coeffs → coeffs | (f,k) (g,m) := 
(λ x, f x - g x, max k m)

lemma val_sub {v} (c1 c2 : coeffs) : 
(sub c1 c2).val v = c1.val v - c2.val v :=
begin
  cases c1 with b1 as1, cases c2 with b2 as2,
  simp only [sub],
end




def fa (p : int → Prop) : coeffs → Prop | (f,k) :=
∀ x < k, p (f x)

#exit

def val_core_set {v i} :
  ∀ {m n}, val_core v m ([]{n ↦ i}) = i * v (n + m) 
| 0 0 := by simp_omega 
| 0 (n+1) := begin simp_omega, apply @val_core_set 1 n end
| (m+1) 0 := by simp_omega
| (m+1) (n+1) :=
  begin 
    simp with omega,
    have heq : m + (n + 2) = n + (m + 2) := by ring,
    rw heq, apply @val_core_set (m+2) n, 
  end

@[omega] def val_set {v n i} : 
  val v ([]{n ↦ i}) = i * v (n) := 
by apply val_core_set

lemma val_core_neg {v} : 
  ∀ {m is}, val_core v m (list.neg is) = -(val_core v m is) 
| m []      := by simp_omega
| m (i::is) := begin simp_omega, rw val_core_neg, simp end

@[omega] lemma val_neg {v} : 
  ∀ {is}, val v (list.neg is) = -(val v is) :=
by apply val_core_neg

lemma val_core_add {v} : 
  ∀ {m is js}, val_core v m (list.add is js) = 
  (val_core v m is) + (val_core v m js)
| m []      []      := by simp_omega
| m []      (j::hs) := begin simp_omega end
| m (i::is) []      := begin simp_omega end
| m (i::is) (j::hs) := begin simp_omega, rw val_core_add, ring end

@[omega] lemma val_add {v} {is js : coeffs} : 
  val v (list.add is js) = (val v is) + (val v js) :=
by apply val_core_add

lemma val_core_sub {v} : 
  ∀ {m is js}, val_core v m (list.sub is js) = 
  (val_core v m is) - (val_core v m js)
| m []      []      := by simp_omega
| m []      (j::hs) := begin simp_omega [val_core_neg], ring end
| m (i::is) []      := begin simp_omega end
| m (i::is) (j::hs) := begin simp_omega, rw val_core_sub, ring end

@[omega] lemma val_sub {v} {is js : coeffs} : 
  val v (list.sub is js) = (val v is) - (val v js) :=
by apply val_core_sub

lemma val_core_mul₁ {v i} :
  ∀ {m is}, val_core v m (i *₁ is) = i * val_core v m is 
| m [] := by simp_omega
| m (j::is) := begin simp_omega, rw val_core_mul₁, ring end 

@[omega] lemma val_mul₁ {v i is} :
  val v (i *₁ is) = i * val v is := 
by apply val_core_mul₁

lemma dvd_val_core {j} (v) :
  ∀ {is} n, (∀ x ∈ is, j ∣ x) → (j ∣ val_core v n is)
| [] _ h := begin simp_omega, apply dvd_zero, end
| (i::is) n h := 
  begin
    simp_omega, apply dvd_add,
    apply dvd_mul_of_dvd_left (h _ (or.inl rfl)),
    apply dvd_val_core _ (list.forall_mem_of_forall_mem_cons h) 
  end

lemma dvd_val {is j v} : (∀ x ∈ is, j ∣ x) → (j ∣ val v is) := 
by apply dvd_val_core

lemma val_core_eq_zero {v} : 
  ∀ {is m}, (∀ x : int, x ∈ is → x = 0) → val_core v m is = 0 
| []      m _  := rfl
| (i::is) m h1 :=
  begin
    simp_omega, rw [h1 _ (or.inl rfl), val_core_eq_zero 
      (list.forall_mem_of_forall_mem_cons h1)], simp
  end

lemma val_eq_zero {v is} : 
  (∀ x : int, x ∈ is → x = 0) → val v is = 0 :=
by apply val_core_eq_zero

lemma val_core_eq_val_core_of_eq_upto (v w) :
  ∀ k (is : list int), eq_upto (k + is.length) v w → 
  val_core v k is = val_core w k is 
| k []      h1 := rfl 
| k (i::is) h1 :=
  begin
    simp only [val_core], apply fun_mono_2,  
    apply congr_arg, apply h1, apply nat.lt_add_of_pos_right,
    apply nat.succ_pos, apply val_core_eq_val_core_of_eq_upto,
    rw [add_assoc, add_comm 1], apply h1 
  end

lemma val_eq_val_of_eq_upto {v w} {is : coeffs} :
  eq_upto is.length v w → val v is = val w is :=
begin
  intro h1, apply val_core_eq_val_core_of_eq_upto, 
  rw zero_add, exact h1
end

@[omega] def val_except_core (v : nat → int) : nat → nat → coeffs → int 
| _     _ []      := 0
| 0     k (i::is) := val_core v (k+1) is
| (n+1) k (i::is) := i * (v k) + val_except_core n (k+1) is

@[omega] lemma val_except_core_nil {v n k} :
  val_except_core v n k [] = 0 :=
begin cases n; refl end

def val_except (v n cs) := val_except_core v n 0 cs

def val_except_core_add_eq (v : nat → int) : 
  ∀ (n k : nat) (cs : list int), 
  ((val_except_core v n k cs) + ((cs.get n) * (v (n+k))) = (val_core v k cs))
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
    simp_omega, apply val_core_eq_zero,
    intros x h2, cases (list.eq_get_of_mem h2) with m h3,
    rw h3, apply h1 (m+1) (nat.succ_ne_zero _)
  end
| (n+1) k (i::is) h1 :=
  begin
    have h2 : i = 0 := (h1 0 (nat.succ_ne_zero _).symm),
    simp_omega [h2], apply val_except_core_eq_zero,
    intros x h3, apply h1 (x+1) _, simp [h3]
  end

lemma val_core_eq_val_core_of_equiv {v} : 
  ∀ {k} {is js : list int}, list.equiv is js → 
  val_core v k is = val_core v k js
| k [] [] h1 := rfl 
| k is [] h1 := 
  begin
    simp_omega, apply val_core_eq_zero, 
    intros i h2, cases (list.eq_get_of_mem h2) with m h3,
    rw h3, have h4 := h1 m, simp only [list.get_nil] at h4,
    exact h4
  end
| k [] js h1 := 
  begin
    simp_omega, apply eq.symm, apply val_core_eq_zero, 
    intros i h2, cases (list.eq_get_of_mem h2) with m h3,
    rw h3, have h4 := h1 m, simp only [list.get_nil] at h4,
    exact h4.symm
  end
| k (i::is) (j::js) h1 := 
  begin
    simp_omega, have h2 : i = j := (h1 0), rw h2,
    apply congr_arg, apply val_core_eq_val_core_of_equiv,
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
    simp_omega, apply val_core_eq_val_core_of_equiv _,
  end 
| (n+1) k (i::is) (j::js) h1 h2 := sorry 

#exit
lemma val_except_eq_val_except {n} {v w : nat → int} {cs} : 
  eq_except n v w → val_except n v cs = val_except n w cs := 
begin

end



#exit
def val_core_wo (n) (v is) := val_core v 0 is - ((is.get n) * v n)

lemma val_core_wo_add_eq (n v is) :
  val_core_wo n v is + ((is.get n) * v n) = val_core v 0 is :=
begin simp only [val_wo, sub_add_cancel] end
end coeffs