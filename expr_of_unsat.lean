import .scalar

open int tactic 

meta def expr_of_neg : int → tactic expr 
| (of_nat _) := failed
| -[1+ m] := return `(neg_succ_lt_zero %%`(m))

lemma zero_eq_zero : (0 : int) = 0 := rfl

meta def expr_of_forall_mem_eq_zero : list int → tactic expr 
| [] := return `(forall_mem_nil_eq_zero).to_expr
| (i::is) :=
  do x ← expr_of_forall_mem_eq_zero is,
     to_expr ``(forall_mem_cons_eq_zero 0 %%`(is) zero_eq_zero %%x)

meta def expr_of_unsat_comb (ks : list nat) (p : polytope) : tactic expr :=  
let ⟨b,as⟩ := comb p ks in 
do x1 ← expr_of_neg b,
   x2 ← expr_of_forall_mem_eq_zero as, 
   to_expr ``(unsat_comb'_of %%`(p) %%`(ks) %%x1 %%x2)

meta def expr_of_unsat (p : polytope) : tactic expr := 
do ks ← search p, 
   x ← expr_of_unsat_comb ks p,
   to_expr ``(unsat_of_unsat_comb' %%`(p) %%`(ks) %%x)

/- Given a (ps : list polytope), return the 
   expr of a term (t : polytopes.unsat ps)  -/
meta def expr_of_unsats : list polytope → tactic expr 
| [] := return `(polytopes.unsat_nil)
| (p::ps) := 
  do x ← expr_of_unsat p,
     xs ← expr_of_unsats ps,
     to_expr ``(polytopes.unsat_cons %%`(p) %%`(ps) %%x %%xs)
