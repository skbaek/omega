import .int.main  .nat.main

#exit
import .rev .reify .dnf .scalar .is_lia

open tactic

run_cmd mk_simp_attr `sugar_int 
attribute [sugar_int] 
  not_le not_lt
  int.lt_iff_add_one_le
  or_false false_or
  and_true true_and
  ge gt mul_add add_mul 
  mul_comm sub_eq_add_neg
  classical.imp_iff_not_or
  classical.iff_iff

meta def desugar := `[try {simp only with sugar_int}]

meta def get_polytope : tactic polytope :=
do `(polytope.unsat %%tsx) ← target, 
   ts ← eval_expr polytope tsx,
   return ts

meta def discharge_clause : tactic unit :=
do ks ← get_polytope >>= scalar.search, 
   pexpr.apply ``(scalar.unsat_of_unsat_comb %%`(ks) _), 
   pexpr.apply ``(trivial), skip

meta def discharge_clauses : tactic unit :=
( pexpr.apply ``(@list.forall_mem_nil (list term) polytope.unsat) >> skip) <|> 
( do pexpr.apply ``(@list.forall_mem_cons_of (list term) polytope.unsat _ _ _ _), 
     discharge_clause, discharge_clauses)

lemma uniclo_of_unsat_clausify {p : form} :
  polytopes.unsat (dnf (¬*p)) → p.uniclo := 
begin
  intro h1, 
  apply uniclo_of_valid,
  apply valid_of_unsat_not,
  apply form_unsat_of_polytopes_unsat,
  assumption,
end

meta def clausify : tactic unit := 
pexpr.apply ``(uniclo_of_unsat_clausify _) >> skip

meta def omega_int : tactic unit :=
do rev_int, desugar, 
   trace_target,
   reify, clausify, 
   discharge_clauses

meta def omega : tactic unit := 
monad.cond is_lia_goal omega_int failed

example (x : int) : 0 ≤ (31 * x) → 0 ≤ x :=
begin
  omega,
end
