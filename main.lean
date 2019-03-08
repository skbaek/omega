import .rev .reify .dnf .search 

open tactic

run_cmd mk_simp_attr `sugar 
attribute [sugar] 
  not_le not_lt
  int.lt_iff_add_one_le
  or_false false_or
  and_true true_and
  ge gt mul_add add_mul 
  mul_comm sub_eq_neg_add
  classical.imp_iff_not_or
  classical.iff_iff

meta def desugar := `[try {simp only with sugar at *}]

meta def set_goal_to_false : tactic unit :=
do gx ← target,
   match gx with 
   | `(false)        := skip
   | `(¬ %%px)       := intro_fresh >> skip
   | `(%%px → false) := intro_fresh >> skip
   | _         := 
     apply `(@classical.by_contradiction %%gx) >> 
     intro_fresh >> skip
   end

meta def get_polytope : tactic polytope :=
do `(polytope.unsat %%tsx) ← target, 
   ts ← eval_expr polytope tsx,
   return ts

meta def discharge_clause : tactic unit :=
do p ← get_polytope >>= search, 
   to_expr ``(unsat_of_correct %%`(p) _) >>= apply,
   to_expr ``(trivial) >>= apply,
   skip 

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
to_expr ``(uniclo_of_unsat_clausify _) >>= apply >> skip

meta def omega : tactic unit :=
do rev, 
   desugar, 
   reify, 
   clausify, 
   discharge_clauses,
   skip

example (x y : int) (h1 : x ≤ 5 ∧ y > 3) : x - y < 8 := 
by omega 