import .scalar .clause .eqelim

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

meta def expr_of_unsat_comb (ks : list nat) (p : list term) : tactic expr :=  
let ⟨b,as⟩ := comb p ks in 
do x1 ← expr_of_neg b,
   x2 ← expr_of_forall_mem_eq_zero as, 
   to_expr ``(unsat_comb_of %%`(p) %%`(ks) %%x1 %%x2)

/- Given a (([],les) : clause), return the 
   expr of a term (t : clause.unsat ([],les)). -/
meta def expr_of_unsat_ef : clause → tactic expr 
| ((_::_), _) := failed  
| ([], les) := 
  do ks ← search les, 
     x ← expr_of_unsat_comb ks les,
     return `(unsat_of_unsat_comb %%`(ks) %%`(les) %%x)

/- Given a (c : clause), return the 
   expr of a term (t : clause.unsat c)  -/
meta def expr_of_unsat (c : clause) : tactic expr := 
do ee ← find_ees c, 
   x ← expr_of_unsat_ef (conc ee c), 
   return `(unsat_of_unsat_conc %%`(ee) %%`(c) %%x)

/- Given a (cs : list clause), return the 
   expr of a term (t : clauses.unsat cs)  -/
meta def expr_of_unsats : list clause → tactic expr 
| [] := return `(clauses.unsat_nil)
| (p::ps) := 
  do x ← expr_of_unsat p,
     xs ← expr_of_unsats ps,
     to_expr ``(clauses.unsat_cons %%`(p) %%`(ps) %%x %%xs)
