import .main

meta def ex01 : expr := `(∀ {x y z w v : int}, 100 = x → x = y → y = z → z = w → w = v → v = 100)
meta def ex02 : expr := `(∀ x : int, (x = 5 ∨ x = 7) → 2 < x)
meta def ex03 : expr := `(∀ x : int, x ≤ -x → x ≤ 0)
meta def ex04 : expr := `(∀ x y : int, (x ≤ 5 ∧ y ≤ 3) → x + y ≤ 8 )
meta def ex05 : expr := `(∀ (x y z : int), x < y → y < z → x < z )
meta def ex06 : expr := `(∀ (x y z : int), x - y ≤ x - z → z ≤ y)
meta def ex07 : expr := `(∀ x : int, (x = -5 ∨ x = 7) → ¬x = 0 )
meta def ex08 : expr := `(∀ x : int, 31 * x > 0 → x > 0 )
meta def ex09 : expr := `(∀ x y : int, (-x - y < x - y) → (x - y < x + y) → (x > 0 ∧ y > 0))
meta def ex10 : expr := `(∀ (x : int), (x ≥ -1 ∧ x ≤ 1) → (x = -1 ∨ x = 0 ∨ x = 1))
meta def ex11 : expr := `(∀ (x : int), 5 * x = 5 → x = 1 )
meta def ex12 : expr := `(∀ x y z w v : int, x = y → y = z → x = z )
meta def ex13 : expr := `(∀ x : int, x < 349 ∨ x > 123 )
meta def ex14 : expr := `(∀ x y : int, x ≤ 3 * y → 3 * x ≤ 9 * y )
meta def ex15 : expr := `(∀ x : int, (x < 43 ∧ x > 513) → ¬x = x )
meta def ex16 : expr := `(∀ (x y z w : int), x ≤ y → y ≤ z → z ≤ w → x ≤ w)

meta def ex17 : expr := `(forall (x : nat),  31 * x > 0 → x > 0)
meta def ex18 : expr := `(forall (x y : nat),  (x ≤ 5 ∧ y ≤ 3) → x + y ≤ 8)
meta def ex19 : expr := `(forall (x y z y : nat),  ¬(2 * x + 1 = 2 * y))
meta def ex20 : expr := `(forall (x y : nat),  x > 0 → x + y > 0)
meta def ex21 : expr := `(forall (x : nat),  x < 349 ∨ x > 123)
meta def ex22 : expr := `(forall (x y : nat),  x ≤ 3 * y → 3 * x ≤ 9 * y)
meta def ex23 : expr := `(forall (x y z : nat), (x ≤ y) → (z > y) → (x - z = 0))
meta def ex24 : expr := `(forall (x y z : nat), x - 5 > 122 → y ≤ 127 → y < x)

open tactic

meta def batch_test (slv : tactic unit) : nat → list expr → tactic unit 
| _ [] := tactic.triv
| idx (exp::exps) :=
  ((do gs ← tactic.get_goals,
       g ← tactic.mk_meta_var exp,
       tactic.set_goals (g::gs), slv) 
    <|> (trace (("Failed ex " : format) ++ format.of_nat idx) >> skip))
    >> batch_test (idx+1) exps

meta def int.tests : list expr := 
[ex01,ex02,ex03,ex04,ex05,ex06,ex07,ex08,ex09,ex10,
 ex11,ex12,ex13,ex14,ex15,ex16]

meta def nat.tests : list expr := 
[ex17,ex18,ex19,ex20,ex21,ex22,ex23,ex24]

meta def tests : list expr := int.tests ++ nat.tests

set_option profiler true

example : true := 
by do batch_test omega 0 tests