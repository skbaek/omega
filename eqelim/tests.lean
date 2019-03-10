import .main 

open tactic

lemma false_of_empty_consts :
  ¬(true ∧ true) → false :=
begin intro h1, apply h1, exact_dec_trivial end

meta def intro_all : tactic unit :=
intros >> pexpr.apply ``(classical.by_contradiction _) >> 
intro_fresh >> skip

run_cmd mk_simp_attr `connectives
attribute [connectives] 
  classical.not_not
  classical.not_and_distrib
  classical.imp_iff_not_or
  classical.iff_iff
  not_or_distrib

lemma int.not_eq {i j : int} :
  ¬i = j ↔ (i + 1 ≤ j ∨ j + 1 ≤ i) :=
begin
  rw [le_antisymm_iff, classical.not_and_distrib,
    not_le, int.lt_iff_add_one_le,
    not_le, int.lt_iff_add_one_le, or.comm],
end

run_cmd mk_simp_attr `sugar
attribute [sugar] 
  not_le not_lt 
  int.not_eq
  int.lt_iff_add_one_le
  zero_add add_zero
  zero_mul mul_zero
  or_false false_or
  and_true true_and
  ne ge gt mul_add add_mul 
  mul_comm sub_eq_neg_add

--meta def desugar := `[try {simp only with sugar at *}]

local attribute [inline] interaction_monad_orelse

meta def omega_decomp : tactic unit 
| s := ((split_and <|> split_or) !; omega_decomp | 
  (trace_state >> omega_core)) s

meta def omega : tactic unit :=
do intro_all,
   `[try {simp only with connectives at *}],
   `[try {simp only with sugar at *}],
   pexpr.apply ``(false_of_empty_consts _),
   omega_decomp

set_option profiler true

example {x y z w v : int} : 100 = x → x = y → y = z → z = w → w = v → v = 100 := by omega

example : ∀ x : int, (x = 5 ∨ x = 7) → 2 < x := by omega
example : ∀ x : int, x ≤ -x → x ≤ 0 := by omega
example : ∀ x y : int, (x ≤ 5 ∧ y ≤ 3) → x + y ≤ 8 := by omega 
example (x y z : int) : x < y → y < z → x < z := by omega 
example (x y z : int) : x - y ≤ x - z → z ≤ y := by omega
example : ∀ x : int, (x = -5 ∨ x = 7) → ¬x = 0 := by omega 
example : ∀ x : int, 31 * x > 0 → x > 0 := by omega 
example : ∀ x y : int, (-x - y < x - y) → (x - y < x + y) → (x > 0 ∧ y > 0) := by omega 
example (x : int) : (x ≥ -1 ∧ x ≤ 1) → (x = -1 ∨ x = 0 ∨ x = 1):= by omega 
example (x : int) : 5 * x = 5 → x = 1 := by omega 
example : ∀ x y z : int, x = y → y = z → x = z := by omega 
example : ∀ x : int, x < 349 ∨ x > 123 := by omega 
example : ∀ x y : int, x ≤ 3 * y → 3 * x ≤ 9 * y := by omega 
example : ∀ x : int, (x < 43 ∧ x > 513) → ¬x = x := by omega 
example (x y z w : int) : x ≤ y → y ≤ z → z ≤ w → x ≤ w := by omega