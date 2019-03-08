open tactic

meta def intro_fresh : tactic expr := 
do n ← get_unused_name, intro n

meta def pexpr.apply (x : pexpr) : tactic (list (name × expr)) :=
to_expr x >>= apply


