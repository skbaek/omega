import data.list.basic .nat

import .simp_omega 

variables {α β : Type}

namespace list

@[omega] def set [has_zero α] (i) : list α → ℕ → list α
| (j::is) 0     := i::is
| []      0     := [i] 
| (j::is) (k+1) := j::(set is k) 
| []      (k+1) := 0::(set ([] : list α) k)
notation as `{` m `↦` a `}` := set a as m 

lemma length_set [has_zero α] {a : α} :
  ∀ {m as}, (as{m ↦ a}).length = _root_.max as.length (m+1) 
| 0 [] := rfl
| 0 (a::as) := 
  begin
    rw max_eq_left, refl, 
    simp [nat.le_add_right],
  end
| (m+1) [] := 
  begin
    rw max_eq_right, simp_omega [list.length],
    rw @length_set m, rw max_eq_right, 
    repeat {apply zero_le}
  end
| (m+1) (a::as) := 
  begin
    simp_omega [list.length, nat.max_succ_succ], 
    rw @length_set m, 
  end
  
@[omega] def get [has_zero α] : nat → list α → α  
| _ [] := (0 : α)
| 0 (i::is) := i 
| (n+1) (i::is) := get n is 

@[omega] lemma get_nil [has_zero α] {k} : get k [] = (0 : α) := 
begin cases k; refl end

lemma get_eq_zero_of_le [has_zero α] : 
  ∀ k {as : list α}, as.length ≤ k → get k as = (0 : α) 
| 0 [] h1 := rfl
| 0 (a::as) h1 := by cases h1
| (k+1) [] h1 := rfl
| (k+1) (a::as) h1 := 
  begin
    simp_omega, apply get_eq_zero_of_le k,
    rw ← nat.succ_le_succ_iff, apply h1,
  end

lemma get_set [has_zero α] {a : α} : 
  ∀ {k} {as}, as{k ↦ a}.get k = a
| 0 as := begin cases as; refl end
| (k+1) as :=
  begin cases as; {simp_omega, apply get_set} end

lemma mem_get_of_le [has_zero α] : 
  ∀ {n} {as : list α}, 
  n < as.length → as.get n ∈ as 
| _ [] h1 := by cases h1
| 0 (a::as) _ := or.inl rfl
| (n+1) (a::as) h1 := 
  begin
    simp_omega, apply or.inr,
    apply mem_get_of_le,
    apply nat.lt_of_succ_lt_succ h1,
  end

lemma mem_get_of_ne_zero [has_zero α] : 
  ∀ {n} {as : list α}, 
  as.get n ≠ 0 → as.get n ∈ as 
| _ [] h1 := begin exfalso, apply h1, rw get_nil end
| 0 (a::as) h1 := or.inl rfl 
| (n+1) (a::as) h1 :=
  begin
    simp_omega, 
    apply (or.inr (mem_get_of_ne_zero _)),
    apply h1
  end
  
lemma eq_get_of_mem [has_zero α] {a} : 
  ∀ {as : list α}, a ∈ as → ∃ n, a = (as.get n)
| [] h := by cases h
| (b::as) h :=
  begin
    rw mem_cons_iff at h, cases h,
    { existsi 0, apply h },
    { cases eq_get_of_mem h with n h2,
      existsi (n+1), apply h2 }
  end

lemma forall_val_of_forall_mem [has_zero α] {p : α → Prop} {as : list α} :
  p 0 → (∀ x ∈ as, p x) → (∀ n, p (as.get n)) | h1 h2 n := 
begin
  by_cases h3 : n < as.length,
  { apply h2 _ (mem_get_of_le h3) },
  { rw not_lt at h3,
    rw get_eq_zero_of_le _ h3, apply h1 }
end 

@[omega] def add [has_add α] : list α → list α → list α 
| as1 [] := as1
| [] as2 := as2
| (a1::as1) (a2::as2) := ((a1+a2)::(add as1 as2))

@[omega] lemma nil_add [has_add α] (as : list α) :
add [] as = as := by cases as; refl

@[omega] lemma add_nil [has_add α] (as : list α) :
add as [] = as := by cases as; refl

@[omega] lemma get_add [add_monoid α] : 
  ∀ {k} {is js : list α}, 
  (add is js).get k = (is.get k + js.get k) 
| 0     is      []      := by simp_omega
| 0     []      js      := by simp_omega
| 0     (i::is) (j::js) := by simp_omega
| (k+1) []      js      := by simp_omega
| (k+1) is      []      := by simp_omega
| (k+1) (i::is) (j::js) := by simp_omega [get_add]

lemma length_add [has_add α] : 
  ∀ {is js : list α}, (add is js).length = max is.length js.length 
| [] js := begin simp_omega, rw max_eq_right, apply zero_le end
| is [] := begin simp_omega, rw max_eq_left, apply zero_le end
| (i::is) (j::js) :=
  by simp_omega [list.length,
     nat.max_succ_succ, length_add]

@[omega] def mul₁ [has_mul α] (a) : list α → list α 
| []      := [] 
| (b::as) := a * b::(mul₁ as)

infix `*₁` : 250 := mul₁ 

@[omega] def div₁ [has_div α] (d) : list α → list α 
| []      := [] 
| (a::as) := (a/d)::(div₁ as)



@[omega] def neg [has_neg α] : list α → list α 
| []      := [] 
| (a::as) := -a::(neg as)

@[omega] lemma get_neg [add_group α] : 
  ∀ {k} {as : list α}, as.neg.get k = -(as.get k) 
| _ []          := by simp_omega
| 0 (a::as)     := by simp_omega
| (k+1) (a::as) := begin simp_omega [get_neg] end

@[omega] lemma length_neg [has_neg α] : 
  ∀ as : list α, (as).neg.length = as.length 
| []      := rfl 
| (a::as) := by simp_omega [list.length, length_neg] 

@[omega] def sub [has_neg α] [has_sub α] : list α → list α → list α 
| [] []        := []
| [] (a2::as2) := neg (a2::as2)
| (a1::as1) [] := a1::as1
| (a1::as1) (a2::as2) := (a1-a2)::(sub as1 as2) 

@[omega] lemma sub_nil [has_neg α] [has_sub α] (as : list α) :
sub as [] = as := by cases as; refl

@[omega] lemma nil_sub [has_neg α] [has_sub α] (as : list α) :
sub [] as = as.neg := by cases as; refl

@[omega] lemma get_sub [add_group α] : --[has_zero α] [has_neg α] [has_sub α] : 
  ∀ {k} {is js : list α}, 
  (sub is js).get k = (is.get k - js.get k) 
| 0     is      []      := by simp_omega
| 0     []      js      := by simp_omega
| 0     (i::is) (j::js) := by simp_omega
| (k+1) []      js      := by simp_omega 
| (k+1) is      []      := by simp_omega 
| (k+1) (i::is) (j::js) := by simp_omega [get_sub]

lemma length_sub [has_neg α] [has_sub α] : 
  ∀ {is js : list α}, (sub is js).length = max is.length js.length 
| [] js := begin simp_omega, rw max_eq_right, apply zero_le end
| is [] := begin simp_omega, rw max_eq_left, apply zero_le end
| (i::is) (j::js) :=
  by simp_omega [list.length,
     nat.max_succ_succ, length_sub]


def max [inhabited α] [decidable_linear_order α] : list α → α 
| []           := @inhabited.default α _
| [a]          := a
| (a1::a2::as) := _root_.max a1 (max (a2::as))

def map_with_idx_core (f : nat → α → β) : nat → list α → list β  
| k []      := []
| k (a::as) := f k a::(map_with_idx_core (k+1) as)

def map_with_idx (f : nat → α → β) (as : list α) : list β :=
map_with_idx_core f 0 as

def snoc_if_oob : nat → α → list α → list α 
| m a as := if m < as.length then as else as ++ [a]

local attribute [instance] classical.dec 

lemma not_exists_mem_not {P : α → Prop} {as : list α} :
  ¬ (∃ x ∈ as, ¬ P x) ↔ ∀ x ∈ as, P x := 
begin
  constructor; intro h1,
  { intros x h2, by_contra h3, 
    apply h1, refine ⟨x,h2,h3⟩ },
  { intro h2, cases h2 with x h2,
    cases h2 with h2 h3, apply h3 (h1 _ h2) }
end

lemma forall_mem_cons_of {p : α → Prop} {a : α} {as : list α} :
  p a → (∀ x ∈ as, p x) → (∀ x ∈ (a::as), p x) :=
begin
  intros h1 h2, rw forall_mem_cons,
  constructor; assumption
end

lemma forall_mem_of_subset {p : α → Prop} {as1 as2 : list α} :
  as1 ⊆ as2 → (∀ x ∈ as2, p x) → (∀ x ∈ as1, p x) := 
begin
  intros h1 h2 a h3, apply h2,
  rw subset_def at h1, apply h1 h3
end


def equiv [has_zero α] (l1 l2 : list α) : Prop :=
∀ m, l1.get m = l2.get m

lemma get_set_eq_of_ne [has_zero α] {a : α} : 
  ∀ {as : list α} {k} m, m ≠ k → as{k ↦ a}.get m = as.get m 
| as 0 m h1 := 
  begin
    cases m, contradiction, cases as, simp_omega, refl
  end
| as (k+1) m h1 := 
  begin
    cases as; cases m; simp_omega, 
    { rw get_set_eq_of_ne, simp_omega,
      intro hc, apply h1, simp [hc] },
    { apply get_set_eq_of_ne, intro hc,
      apply h1, simp [hc], }
  end

lemma map_add_map [has_add α] (f g : α → α) :
  ∀ {as : list α}, as.map (λ x, f x + g x) = add (as.map f) (as.map g) 
| []      := rfl
| (a::as) := begin simp_omega [@map_add_map as], constructor; refl end

lemma get_map [has_zero α] [has_zero β] {f : α → β} : 
  ∀ {n} {as : list α}, n < as.length → (as.map f).get n = f (as.get n) 
| _ [] h := by cases h
| 0 (a::as) h := rfl
| (n+1) (a::as) h := 
  begin
    simp only [map, get], apply get_map,
    simp only [length, nat.lt_succ_iff] at h, 
    apply h,
  end

lemma get_map' [has_zero α] [has_zero β] {f : α → β} {n} {as : list α} :
  f 0 = 0 → (as.map f).get n = f (as.get n) :=
begin
  intro h1, by_cases h2 : n < as.length,
  { apply get_map h2 },
  { rw not_lt at h2,
    rw [get_eq_zero_of_le _ h2, get_eq_zero_of_le, h1], 
    rw [length_map], apply h2 }
end

#exit
lemma get_map [has_zero α] [has_zero β] {f : α → β} 
(hf : f 0 = 0) : ∀ {n} {as : list α}, (as.map f).get n = f (as.get n) 
| _ []      := by simp only [map, get_nil, hf]
| n (a::as) := by cases n; simp only [map, get, get_map]

#exit
instance decidable_forall_mem' (p : α → Prop) [h0 : decidable_pred p] :
  ∀ l : list α, decidable (∀ x ∈ l, p x) 
| [] := decidable.is_true (λ x h, by cases h) 
| (a::as) :=
  match h0 a with 
  | (is_true h1) := 
    match decidable_forall_mem' as with 
    | (is_true h2) := 
      is_true (λ x h3, h3.elim (λ h4, @eq.rec _ a p h1 _ h4.symm) (λ h4, h2 _ h4))
    | (is_false h2) := is_false (λ h3, h2 (λ x h5, h3 _ (or.inr h5)))
    end
  | (is_false h1) := 
    is_false (λ h2, h1 (h2 _ (or.inl rfl)))
  end

lemma length_map' (f : α → β) :
  ∀ (l : list α), length (map f l) = length l 
| [] := rfl
| (a::as) := 
  begin
    simp only [map, length], 
    apply congr_arg (λ x, x + 1),
    apply length_map'
  end

#exit



@[omega] lemma get_nil [has_zero α] (k : nat) : nil[k] = (0 : α) := 
begin cases k; refl end

@[omega] lemma get_mul₁ [mul_zero_class α] (a : α) : 
  ∀ k as, (a *₁ as)[k] = a * as[k] 
| _ []          := by simp_omega  
| 0 (a::as)     := by simp_omega
| (k+1) (a::as) := begin simp_omega, apply get_mul₁ end

def equiv [has_zero α] (as1 as2 : list α) : Prop := ∀ k, as1[k] = as2[k]

infix `≃` : 200 := equiv

lemma equiv.symm [has_zero α] {as1 as2 : list α} :
  as1 ≃ as2 → as2 ≃ as1 :=
begin intros h k, rw (h k) end

lemma cons_equiv_cons [has_zero α] (a1 a2 : α) (as1 as2 : list α) : 
  (a1::as1) ≃ (a2::as2) ↔ (a1 = a2 ∧ as1 ≃ as2) :=
begin
  constructor; intro h1,
  { constructor, apply (h1 0), intro k, apply (h1 (k+1)) },
  { intro k, cases k, apply h1.left, apply h1.right }
end

lemma sum_eq_zero_of_equiv_nil [add_monoid α] :
  ∀ {as : list α}, as ≃ nil → sum as = 0 
| [] _ := rfl
| (a::as) h1 := 
  begin
    have h2 : a = 0, apply (h1 0), rw h2, simp,
    apply sum_eq_zero_of_equiv_nil, intro k,
    rw get_nil, apply (h1 (k+1))
  end



lemma get_set [has_zero α] {k m} {b : α} {as} : 
  as{k ↦ b}[m] = if k = m then b else as[m] :=
begin
  by_cases h1 : k = m,
  { rw [h1, get_set_eq_of_eq], rw if_pos rfl },
  { rw if_neg h1, apply get_set_eq_of_ne h1 }
end

lemma set_equiv_self [has_zero α] {k} {a : α} {as} :
  as[k] = a → as{k ↦ a} ≃ as := 
begin
  intros h1 m, rw get_set,
  by_cases h2 : k = m,
  { rw if_pos h2, rw [← h2, h1] },
  { rw if_neg h2 }
end


@[omega] lemma neg_nil [has_neg α] : -([] : list α) = [] := rfl

@[omega] lemma neg_cons [has_neg α] (a : α) (as) : 
  -(a::as) = -a::(-as) := rfl





@[omega] lemma nil_add [has_add α] (as : list α) : [] + as = as := 
begin cases as; refl end

@[omega] lemma add_nil [has_add α] (as : list α) : as + [] = as := 
begin cases as; refl end

@[omega] lemma cons_add_cons [has_add α] (a1 a2 : α) (as1 as2 : list α) : 
  (a1::as1) + (a2::as2) = (a1+a2)::(as1 + as2) := rfl
@[omega] lemma nil_sub [has_neg α] [has_sub α] (as : list α) :
  [] - as = -as := 
begin cases as; refl end

@[omega] lemma sub_nil [has_neg α] [has_add α] [has_sub α] (as : list α) :
  as - [] = as := 
begin cases as; refl end

@[omega] def mul₂ [has_mul α] : list α → list α → list α 
| (a1::as1) (a2::as2) := (a1*a2)::(mul₂ as1 as2) 
| [] as2 := []
| as1 [] := []
infix `*₂` : 250 := mul₂ 

@[omega] lemma nil_mul₂ [has_mul α] (as : list α) : nil *₂ as = nil :=
begin cases as; refl end

@[omega] lemma mul₂_nil [has_mul α] (as : list α) : as *₂ nil = nil :=
begin cases as; refl end

@[omega] lemma cons_sub_cons [has_neg α] [has_sub α] 
  (a1 a2 : α) (as1 as2 : list α) : 
  (a1::as1) - (a2::as2) = (a1 - a2)::(as1 - as2) := rfl


lemma length_mul₁ [has_mul α] (a : α) :
  ∀ as, (a *₁ as).length = as.length 
| [] := rfl
| (b::as) := begin simp_omega, simp only [length, length_mul₁] end

@[omega] def dot_prod [semiring α] : list α → list α → α 
| [] [] := 0 
| [] (_::_) := 0 
| (_::_) [] := 0 
| (a1::as1) (a2::as2) :=
  (a1 * a2) + dot_prod as1 as2
infix `⬝` :=  dot_prod 

lemma dot_prod_eq_sum_mul₂ [semiring α] : 
  ∀ as1 as2 : list α , as1 ⬝ as2 = list.sum (as1 *₂ as2) 
| [] [] := rfl 
| [] (_::_) := rfl 
| (_::_) [] := rfl 
| (a1::as1) (a2::as2) := 
  begin simp_omega, rw dot_prod_eq_sum_mul₂ end

@[omega] lemma nil_dot_prod [semiring α] :
  ∀ {as : list α}, [] ⬝ as = 0  
| [] := rfl
| (a::as) := rfl

@[omega] lemma dot_prod_nil [semiring α] :
  ∀ {as : list α}, as ⬝ [] = 0  
| [] := rfl
| (a::as) := rfl

@[omega] lemma cons_dot_prod_cons [semiring α] {a1 a2 : α} {as1 as2} : 
(a1::as1) ⬝ (a2::as2) = (a1 * a2) + (as1 ⬝ as2) := rfl

lemma dot_prod_cons [semiring α] {a2 : α} {as2} : 
  ∀ as1, as1 ⬝ (a2::as2) = get 0 as1 * a2 + (as1.tail ⬝ as2) 
| [] :=        by simp_omega 
| (a1::as1) := by simp_omega 

lemma dot_prod_def [semiring α] : 
  ∀ as1 as2 : list α, as1 ⬝ as2 = get 0 as1 * get 0 as2 + (as1.tail ⬝ as2.tail)
| [] []               := by simp_omega
| [] (a2::as2)        := by simp_omega
| (a1::as1) []        := by simp_omega
| (a1::as1) (a2::as2) := by simp_omega

@[omega] lemma append_dot_prod_append [semiring α] {as3 as4} : 
  ∀ as1 as2 : list α, as1.length = as2.length → 
  (as1 ++ as3) ⬝ (as2 ++ as4) = as1 ⬝ as2 + as3 ⬝ as4 
| [] [] h     := begin rw nil_dot_prod, simp end
| [] (_::_) h := by cases h
| (_::_) [] h := by cases h
| (a1::as1) (a2::as2) h := 
  begin 
    simp only [cons_append, cons_dot_prod_cons],
    rw append_dot_prod_append, simp, simp at h, exact h
  end

lemma dot_prod_comm [comm_ring α] : 
  ∀ (as1 as2 : list α), as1 ⬝ as2 = as2 ⬝ as1 
| [] [] := rfl
| [] (a2::as2) := rfl
| (a1::as1) [] := rfl
| (a1::as1) (a2::as2) := 
  begin simp_omega, rw [mul_comm, dot_prod_comm] end

@[omega] def neg_dot_prod [ring α] : 
  ∀ {as1 as2 : list α}, (-as1) ⬝ as2 = -(as1 ⬝ as2) 
| [] []     := begin simp_omega, end 
| [] (_::_) := begin simp_omega, end 
| (_::_) [] := begin simp_omega, end 
| (a1::as1) (a2::as2) :=
  begin simp_omega, rw neg_dot_prod, simp end

@[omega] lemma add_dot_prod [semiring α] :
  ∀ (as1 as2 as3 : list α),
    (as1 + as2) ⬝ as3 = (as1 ⬝ as3) + (as2 ⬝ as3)
| [] as2 as3 := by simp_omega
| as1 [] as3 := by simp_omega
| as1 as2 [] := by simp_omega
| (a1::as1) (a2::as2) (a3::as3) := 
  begin simp_omega, rw [add_dot_prod, add_mul, add_assoc], simp end

@[omega] lemma sub_dot_prod [ring α] : ∀ (as1 as2 as3 : list α),
  (as1 - as2) ⬝ as3 = (as1 ⬝ as3) - (as2 ⬝ as3) 
| [] as2 as3 := by simp_omega
| as1 [] as3 := by simp_omega
| as1 as2 [] := by simp_omega
| (a1::as1) (a2::as2) (a3::as3) := 
  begin simp_omega, rw sub_dot_prod, simp [add_mul] end

@[omega] lemma mul₁_dot_prod [semiring α] {a : α} :
  ∀ {as1 as2}, (a *₁ as1) ⬝ as2 = a * (as1 ⬝ as2) 
| [] as2 := begin simp [mul₁ , nil_dot_prod] end
| as1 [] :=  begin simp [mul₁ , dot_prod_nil] end
| (a1::as1) (a2::as2) := 
  begin
    unfold mul₁, repeat {rewrite cons_dot_prod_cons}, 
    have h := @mul₁_dot_prod as1 as2, 
    rewrite h, rewrite mul_add, simp, rewrite mul_assoc
  end

lemma set_nil_dot_prod [semiring α] {i} : 
  ∀ {k : nat} {iv : list α}, (nil {k ↦ i}) ⬝ iv = i * (iv.get k)
| 0 []     := by simp_omega
| 0 (_::_) := by simp_omega
| (k+1) [] := by simp_omega
| (k+1) (i::iv) := 
  begin simp_omega, apply set_nil_dot_prod end

lemma get_mul₂ [semiring α] : 
  ∀ k, ∀ as1 as2 : list α, (as1 *₂ as2)[k] = as1[k] * as2[k] 
| k [] as2 := by simp_omega
| k as1 [] := by simp_omega
| k (a1::as1) (a2::as2) :=
  begin cases k; simp_omega, apply get_mul₂ end

lemma set_mul₂_set [semiring α]  
  {k : nat} {a1 a2 : α} {as1 as2 : list α} : 
  as1{k ↦ a1} *₂ as2{k ↦ a2} ≃ (as1 *₂ as2){k ↦ a1 * a2} :=
begin
  intro m, by_cases h1 : k = m; rw get_mul₂,
  { rw h1, repeat {rw get_set_eq_of_eq} },
  { repeat {rw get_set_eq_of_ne}; try {assumption}, rw get_mul₂ }
end

lemma sum_eq_sum_of_equiv [add_monoid α] :
  ∀ {as1 as2 : list α}, as1 ≃ as2 → sum as1 = sum as2 
| [] as2 h1 := 
  begin simp_omega, rw sum_eq_zero_of_equiv_nil (equiv.symm h1) end
| as1 [] h1 :=
  begin simp_omega, rw sum_eq_zero_of_equiv_nil h1 end
| (a1::as1) (a2::as2) h1 :=
  begin
    simp_omega, rw cons_equiv_cons at h1,
    rw h1.left, rw sum_eq_sum_of_equiv h1.right
  end

lemma set_dot_prod_set [semiring α]  
  {k : nat} {a1 a2 : α} {as1 as2 : list α} : 
  as1[k] * as2[k] = a1 * a2 → 
  as1{k ↦ a1} ⬝ as2{k ↦ a2} = as1 ⬝ as2 := 
begin
  intro h1, rw dot_prod_eq_sum_mul₂,
  apply eq.trans (sum_eq_sum_of_equiv _),
  tactic.rotate 2, apply set_mul₂_set,
  apply eq.trans (sum_eq_sum_of_equiv (set_equiv_self _)),
  rw dot_prod_eq_sum_mul₂, rw get_mul₂, assumption
end


def pref [has_zero α] : nat → list α → list α 
| 0     _       := [] 
| (k+1) []      := 0::(pref k ([] : list α))
| (k+1) (i::is) := i::(pref k is)

def suf : nat → list α → list α 
| _     []      := []
| 0     (i::is) := i::is
| (k+1) (i::is) := suf k is  

end list

@[reducible] def ints := list int

class has_prop_val (α : Type) := (val : ints → α → Prop) 
notation v `⊨` p := has_prop_val.val v p


#exit

lemma map_integrate (f : α → β) (as2) : ∀ k as1,  
  (as1 <<k<< as2).map f = (as1.map f <<k<< as2.map f) 
| 0 as1 := begin simp [integrate] end
| (k+1) [] := begin simp [integrate] end
| (k+1) (a1::as1) := 
  begin simp [integrate], rw map_integrate end

lemma not_exists_mem {P : α → Prop} {as : list α} :
  ¬ (∃ x ∈ as, P x) ↔ ∀ x ∈ as, ¬ P x := 
begin
  constructor; intro h,
  { intros x hx hc, apply h, 
    existsi x, constructor; assumption },
  { intro hc, cases hc with x hx, cases hx,
    apply h x; assumption }
end


local attribute [instance] classical.prop_decidable

lemma not_forall_mem {P : α → Prop} {as : list α} :
  ¬ (∀ x ∈ as, P x) ↔ ∃ x, x ∈ as ∧ ¬ P x := 
begin
  constructor; intro h1, 
  { by_contra h2, apply h1, intros x hx, by_contra h3, 
    apply h2, existsi x, constructor; assumption },
  { intro hc, cases h1 with x hx, exact absurd (hc x hx.left) hx.right }
end

lemma exists_mem_cons {p : α → Prop} {a : α} {as : list α} :
  (∃ x, x ∈ (a::as) ∧ p x) ↔ p a ∨ ∃ x, x ∈ as ∧ p x := 
begin
  constructor; intro h;
  [
    {
      cases h with a2 ha2, cases ha2 with ha2l ha2r,
      cases (eq_or_mem_of_mem_cons ha2l) with ha2l,
      subst ha2l, apply or.inl, assumption,
      apply or.inr, existsi a2, constructor; assumption
    },
    {
      cases h with h h;
      [ 
        { existsi a, constructor, apply or.inl rfl, assumption },
        {
          cases h with a ha, cases ha with ha1 ha2,
          existsi a, apply and.intro (or.inr ha1) ha2
        }
      ]
    }
  ]
end

lemma forall_mem_map_iff {f : α → β} {Q : β → Prop} {as} : 
(∀ b ∈ (map f as), Q b) ↔ (∀ a ∈ as, Q (f a)) := 
begin
  constructor; intro h,
  { intros a ha, 
    apply h, apply mem_map_of_mem _ ha },
  { intros b hb, rw mem_map at hb,
    cases hb with a ha, cases ha with ha1 ha2, 
    subst ha2, apply h _ ha1 }
end

lemma forall_mem_map {f : α → β} {p : β → Prop} {as} : 
(∀ a ∈ as, p (f a)) → (∀ b ∈ (map f as), p b) :=
forall_mem_map_iff.elim_right

lemma filter_map_append {f : α → option β} : 
∀ {as1 as2 : list α}, filter_map f (as1 ++ as2) = (filter_map f as1 ++ filter_map f as2) 
| [] as2 := begin simp [filter_map] end
| (a::as1) as2 :=
  begin 
    simp [filter_map], cases (f a), 
    apply filter_map_append,
    rw (@filter_map_append as1 as2), refl,
  end


def set_head [has_zero α] (a as) : list α := as {0 ↦ a}
notation as `₀↦` a := set_head a as  


@[omega] lemma dhead_set_head [has_zero α] (a1 a2 : α) (as : list α) : 
  dhead a1 (as ₀↦ a2) = a2 :=
begin cases as; refl end

@[omega] lemma tail_set_head [has_zero α] (a : α) :
  ∀ as, (as ₀↦ a).tail = as.tail 
| [] := rfl
| (b::as) := rfl

lemma map_eq_map_of_func_eq (f g : α → β) : 
  (∀ a, f a = g a) → ∀ as, map f as = map g as :=
begin
  intro h, have heq : f = g := 
    function.funext_iff.elim_right h,
  simp [heq]
end


#exit
def append_pair : (list α × list α) → list α  
| (l1,l2) := l1 ++ l2 


def forall_mem (P : α → Prop) (as : list α) := ∀ a ∈ as, P a

lemma forall_mem_filter_of_forall_mem {P Q : α → Prop} [H : decidable_pred Q] 
  {as : list α} (h : ∀ a ∈ as, P a) : ∀ a ∈ (list.filter Q as), P a := 
begin intros a ha, apply h, apply mem_of_mem_filter ha end

lemma forall_mem_filter {P Q : α → Prop} [H : decidable_pred P] {as} : 
(∀ a ∈ (filter P as), Q a) ↔ (∀ a ∈ as, P a → Q a) := 
begin
  constructor; intro h,
  { intros a ha1 ha2, apply h, rw mem_filter, 
    constructor; assumption },
  { intros a ha, rw mem_filter at ha,
    apply h _ ha.left ha.right }
end

def some_true (ps : list Prop) : Prop := ∃ p, p ∈ ps ∧ p

def forsome_mem (P : α → Prop) (as : list α) := ∃ a, a ∈ as ∧ P a

instance forsome_mem.decidable {P : α → Prop} [hd : decidable_pred P] :
  ∀ {as : list α}, decidable (∃ a, a ∈ as ∧ P a) 
| [] := decidable.is_false (by simp)
| (a::as) :=
  begin
    cases (hd a),
      { cases forsome_mem.decidable,
          { apply decidable.is_false, intro hc,
            cases hc with a' hc, cases hc with hc1 hc2,
            cases hc1, subst hc1, apply h hc2, apply h_1, 
            existsi a', constructor; assumption },
          { apply decidable.is_true, 
            rw forsome_mem_cons, apply or.inr h_1 } },
      { apply decidable.is_true, 
        rw forsome_mem_cons, apply or.inl h } 
  end

instance dec_eq_nil : ∀ {as : list α}, decidable (as = []) 
| [] := decidable.is_true rfl 
| (a::as) := decidable.is_false (begin intro h, cases h end)

lemma map_ne_nil_of_ne_nil : 
  ∀ {f : α → β} {as : list α}, as ≠ [] → map f as ≠ [] :=
λ f as, not_imp_not.elim_right eq_nil_of_map_eq_nil

lemma exists_maximum [linear_order β] : 
∀ {bs : list β} (hi : bs ≠ []), ∃ b, b ∈ bs ∧ ∀ b' ∈ bs, b' ≤ b 
| [] hi := begin exfalso, apply hi rfl end
| [b] hi := 
  begin
    existsi b, apply and.intro (or.inl rfl), 
    intros b' hb', cases hb' with hb' hb', 
    subst hb', cases hb',
  end
| (b::b'::bs') hi := 
  begin
    cases (@exists_maximum (b'::bs') _) with x hx;
    [{}, { exact_dec_trivial }], cases hx with hx1 hx2,
    apply @classical.by_cases (b ≤ x); intro hle,
    { existsi x, apply and.intro (or.inr hx1), 
      intros bl hbl, rewrite mem_cons_iff at hbl, 
      cases hbl with hbl hbl, subst hbl, apply hle, 
      apply hx2 _ hbl },
    { existsi b, apply and.intro (or.inl rfl),
      intros bl hbl, rewrite mem_cons_iff at hbl, 
      cases hbl with hbl hbl, subst hbl, 
      apply le_trans, apply hx2 _ hbl, 
      apply le_of_not_le hle }
  end

def converse_linear_order (h : linear_order α) : linear_order α := 
{
  le := ge,
  le_refl := le_refl,
  le_trans := @ge_trans _ _,
  le_antisymm := λ a b h1 h2, le_antisymm h2 h1,
  le_total := λ a b, or.symm (le_total a b)
}

lemma exists_minimum [h : linear_order β] : 
∀ {bs : list β} (hi : bs ≠ []), ∃ b, b ∈ bs ∧ ∀ b' ∈ bs, b' ≥ b :=  
@exists_maximum _ (converse_linear_order h)

def map_neg [has_neg α] (as : list α) : list α :=
list.map (λ x, -x) as


lemma of_mem_repeat {k m : nat} :
∀ {n}, k ∈ repeat m n → k = m 
| 0 h := by cases h
| (n+1) h :=
  begin
    simp [repeat] at h, cases h, assumption,
    apply eq_of_mem_repeat h
  end

lemma one_mul₁  [monoid α] :
∀ (as : list α), mul₁ 1 as = as 
| [] := rfl
| (a::as) := begin simp [mul₁ ], apply map_id end


def add₂ [has_add α] : list α → list α → list α 
| (a1::as1) (a2::as2) := (a1+a2)::(add₂ as1 as2) 
| [] as2 := as2
| as1 [] := as1

def sub₂ [has_neg α] [has_add α] [has_sub α] : list α → list α → list α 
| (a1::as1) (a2::as2) := (a1-a2)::(sub₂ as1 as2) 
| as1 [] := as1
| [] as2 := map_neg as2

lemma nil_add₂ [semiring α] (as : list α) :
add₂ [] as = as := 
begin cases as; refl end

lemma add₂_nil [semiring α] (as : list α) :
add₂ as [] = as := 
begin cases as; refl end

lemma nil_sub₂ [has_neg α] [has_add α] [has_sub α] (as : list α) :
sub₂ [] as = map_neg as := 
begin cases as; refl end

lemma sub₂_nil [has_neg α] [has_add α] [has_sub α] (as : list α) :
sub₂ as [] = as := 
begin cases as; refl end

-- | (a::as) := 
--   begin
--     unfold add₂, unfold list.zip_pad,
--     unfold list.map, simp, 
--     have h := nil_add₂ as,
--     unfold add₂ at h, rewrite h
--   end
-- 
-- lemma add₂_nil [semiring α] :
--   ∀ (as : list α), add₂ as [] = as 
-- | [] := rfl
-- | (a::as) := 
--   begin
--     unfold add₂, unfold list.zip_pad, 
--     simp, have h := add₂_nil as, 
--     unfold add₂ at h, rewrite h 
--   end
-- 
-- lemma cons_add₂_cons [semiring α] (a1 a2 : α) (as1 as2) :
-- add₂ (a1::as1) (a2::as2) = (a1 + a2)::(add₂ as1 as2) := 
-- begin unfold add₂, unfold list.zip_pad, simp end
-- 
-- def map_add₂_eq [semiring α] [semiring β] 
--   {f : α → β} (hf : ∀ a1 a2, f (a1 + a2) = f a1 + f a2) :
-- ∀ (as1 as2 : list α), map f (add₂ as1 as2) = add₂ (map f as1) (map f as2) 
-- | [] [] := rfl
-- | [] (a2::as2) := begin simp [nil_add₂, map] end
-- | (a1::as1) [] := begin simp [add₂_nil, map] end
-- | (a1::as1) (a2::as2) := 
--   begin
--     simp [cons_add₂_cons], constructor,
--     apply hf, apply map_add₂_eq
--   end

-- def map_sub₂_eq [semiring α] [has_neg α] [semiring β] [has_neg β]
--   {f : α → β} (hf1 : ∀ a1 a2, f (a1 + a2) = f a1 + f a2) (hf2 : ∀ a, f (-a) = - f a):
-- ∀ (as1 as2 : list α), map f (sub₂ as1 as2) = sub₂ (map f as1) (map f as2) :=
-- begin
--   intros as1 as2, simp [sub₂], rw (map_add₂_eq hf1), simp [map_neg],
--   have hrw : (f ∘ has_neg.neg) = (has_neg.neg ∘ f) := funext hf2, rw hrw 
-- end


lemma forall_mem_iff_forall_mem {P Q : α → Prop} {as : list α} : 
(∀ a, P a ↔ Q a) → ((∀ a ∈ as, P a) ↔ (∀ a ∈ as, Q a)) := 
begin
  intro heq, constructor; intros h a ha,
  rw ← heq, apply h _ ha, rw heq, apply h _ ha
end

end list
