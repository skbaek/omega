import .main

example (x : nat) :  31 * x > 0 → x > 0 := by nat.omega
example (x y : nat) :  (x ≤ 5 ∧ y ≤ 3) → x + y ≤ 8 := by nat.omega
example (x y : nat) :  ¬(2 * x + 1 = 2 * y) := by nat.omega
example (x y : nat) :  x > 0 → x + y > 0 := by nat.omega
example (x : nat) :  x < 349 ∨ x > 123 := by nat.omega
example (x y : nat) :  x ≤ 3 * y → 3 * x ≤ 9 * y := by nat.omega
example (x y z : nat) : (x ≤ y) → (z > y) → (x - z = 0) := by nat.omega