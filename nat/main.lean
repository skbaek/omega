import order.basic ..nat ..logic .neg_elim 
  .reify .rev .sub_elim .dnf ..expr_of_unsat

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

lemma uniclo_of_unsat_neg_elim_not (p : form) :
  (neg_elim (¬* p)).unsat → p.uniclo :=  
begin
  intro h1, apply uniclo_of_valid,
  apply valid_of_unsat_not, intro h2, apply h1,
  apply form.sat_of_implies_of_sat implies_neg_elim h2,
end

axiom any (p : Prop) : p 

meta def expr_of_any (px : expr) : tactic expr := to_expr ``(any %%px)

meta def expr_of_neg_free (p : form) : tactic expr := 
expr_of_any `(form.neg_free %%`(p))

meta def expr_of_sub_free (p : form) : tactic expr := 
expr_of_any `(form.sub_free %%`(p))

/- Given a p : form, return the expr of a term t : p.unsat,
   where p is subtraction- and negation-free. -/
meta def expr_of_unsat_sf (p : form) : tactic expr :=  
do x ← expr_of_neg_free p,
   y ← expr_of_sub_free p,
   z ← expr_of_unsats (dnf p),
   return `(unsat_of_unsat_dnf %%`(p) %%x %%y %%z)

/- Given a p : form, return the expr of a term t : p.unsat,
   where p is negation-free. -/
meta def expr_of_unsat_nf : form → tactic expr | p := 
match p.sub_terms with 
| none         := expr_of_unsat_sf p
| (some (t,s)) := 
  do x ← expr_of_unsat_nf (sub_elim t s p), 
     return `(unsat_of_unsat_sub_elim %%`(t) %%`(s) %%`(p) %%x)
end

/- Given a p : form, return the expr of a term t : p.uniclo -/
meta def expr_of_uniclo (p : form) : tactic expr := 
do trace (neg_elim $ ¬* p),
   x ← expr_of_unsat_nf (neg_elim (¬*p)), 
   to_expr ``(uniclo_of_unsat_neg_elim_not %%`(p) %%x)

meta def expr_of_lna : tactic expr :=
target >>= to_form >>= expr_of_uniclo 

meta def omega : tactic unit :=
rev >> desugar >> expr_of_lna >>= apply >> skip

end nat