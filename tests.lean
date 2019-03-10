import .main

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