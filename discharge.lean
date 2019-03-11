import .polytope .scalar .tactic

open tactic 

meta def get_polytope : tactic polytope :=
do `(polytope.unsat %%tsx) ← target, 
   ts ← eval_expr polytope tsx,
   return ts

meta def discharge_aux : tactic unit :=
do ks ← get_polytope >>= search, 
   pexpr.apply ``(unsat_of_unsat_comb %%`(ks) _), 
  pexpr.apply ``(trivial), 
  skip

meta def discharge : tactic unit :=
( pexpr.apply ``(@list.forall_mem_nil (list term) polytope.unsat) >> skip) <|> 
( do pexpr.apply ``(@list.forall_mem_cons_of (list term) polytope.unsat _ _ _ _), 
     discharge_aux, discharge)
