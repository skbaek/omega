import ..tactic

open tactic

namespace int

meta def is_form_aux : expr → bool 
| `(¬ %% p)               := is_form_aux p
| `(%% p ∨ %%q)           := is_form_aux p && is_form_aux q
| `(%% p ∧ %%q)           := is_form_aux p && is_form_aux q
| `(@eq int _ _)          := true
| `(@has_le.le int _ _ _) := true
| _                       := false

meta def is_form (x : expr) : tactic bool :=
do tx ← infer_type x,
   return $ is_form_aux tx

meta def is_term (x : expr) : tactic bool :=
do tx ← infer_type x, 
   return $ `(int).to_expr = tx

meta def rev : tactic unit :=
do revert_cond_all is_form,
   revert_cond_all is_term

end int