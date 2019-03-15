import algebra.group order.basic ..logic 
  .rev .form .dnf .reify ..expr_of_unsat

namespace int

open tactic

run_cmd mk_simp_attr `sugar
attribute [sugar] 
  not_le not_lt
  int.lt_iff_add_one_le
  or_false false_or
  and_true true_and
  ge gt mul_add add_mul 
  mul_comm sub_eq_add_neg
  classical.imp_iff_not_or
  classical.iff_iff

meta def desugar := `[try {simp only with sugar}]

lemma uniclo_of_unsat_clausify (p : form) :
  clauses.unsat (dnf (¬*p)) → p.uniclo | h1 := 
begin
  apply uniclo_of_valid,
  apply valid_of_unsat_not,
  apply unsat_of_clauses_unsat,
  exact h1 
end

/- Given a p : form, return the expr of a term t : p.uniclo -/
meta def expr_of_uniclo (p : form) : tactic expr :=  
do x ← expr_of_unsats (dnf (¬*p)), 
   return `(uniclo_of_unsat_clausify %%`(p) %%x)

meta def expr_of_lia : tactic expr :=
target >>= to_form >>= expr_of_uniclo 

meta def omega : tactic unit := 
do rev, desugar, 
   expr_of_lia >>= apply,
   skip

end int
