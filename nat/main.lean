import order.basic data.nat.basic ..nat
  ..logic .rev .reify .dnf ..discharge

open tactic

namespace nat

run_cmd mk_simp_attr `sugar_nat 
attribute [sugar_nat] 
  not_le not_lt
  lt_iff_add_one_le
  succ_eq_add_one
  or_false false_or
  and_true true_and
  ge gt mul_add add_mul 
  mul_comm classical.iff_iff
  classical.imp_iff_not_or

meta def desugar := `[try {simp only with sugar_nat}]

lemma uniclo_of_unsat_clausify {p : form} :
  polytopes.unsat (dnf (¬* p)) → p.uniclo := 
begin
  intro h1, 
  apply uniclo_of_valid,
  apply valid_of_unsat_not,
  apply unsat_of_unsat_dnf,
  assumption,
end

meta def clausify : tactic unit := 
pexpr.apply ``(uniclo_of_unsat_clausify _) >> skip

meta def omega : tactic unit :=
do rev, desugar, reify, 
   clausify, discharge


#exit
example (x : nat) : 0 < (31 * x) → 0 < x :=
begin
  omega,
end

end nat

#exit


example (x : nat) :  31 * x > 0 → x > 0 := 
begin
  nat.omega,
end

#exit
example (x : nat) :  31 * x > 0 → x > 0 := by cooper
example (x y : nat) :  (x ≤ 5 ∧ y ≤ 3) → x + y ≤ 8 := by cooper
example (x : nat) : (3 ∣ x ∧ 4 ∣ x) → 12 ∣ x := by cooper 
example (x y : nat) :  ¬(2 * x + 1 = 2 * y) := by cooper
example (x y : nat) :  x + 2 = y → ∃ z : nat, z + 1 = y := by cooper
example (x y : nat) :  x > 0 → x + y > 0 := by cooper
example : ∃ x y : nat, 7 * x = 5 * y := by cooper
example : ∃ x y : nat, 5 * x + 3 * y = 11 := by cooper
example (x : nat) :  x < 349 ∨ x > 123 := by cooper
example (x : nat) :  ∃ y : nat, x = 2 * y ∨ x = (2 * y) + 1 := by cooper
example (x y : nat) :  x ≤ 3 * y → 3 * x ≤ 9 * y := by cooper