import ..tactic

open expr tactic

namespace nat

meta def is_form_aux : expr → bool 
| `(¬ %% p)               := is_form_aux p
| `(%% p ∨ %%q)           := is_form_aux p && is_form_aux q
| `(%% p ∧ %%q)           := is_form_aux p && is_form_aux q
| `(@eq nat _ _)          := true
| `(@has_le.le nat _ _ _) := true
| _                       := false
    
meta def is_form (x : expr) : tactic bool :=
do tx ← infer_type x,
   return $ is_form_aux tx

meta def is_term (x : expr) : tactic bool :=
do tx ← infer_type x, 
   return $ `(nat).to_expr = tx

meta def rev : tactic unit :=
do revert_cond_all is_form,
   revert_cond_all is_term

end nat

-- meta def rev_hyps : tactic unit :=
-- revert_cond_all is_hyp >> skip
-- 
-- meta def has_type (tx x : expr) : tactic bool := 
-- do sx ← infer_type x, return (sx = tx)
-- 
-- meta def is_func_type (dx : expr) : expr → bool 
-- | `(%%x → %%y) := (x = dx) && (is_func_type y)
-- | x            := x = dx
-- meta def is_pred_type (dx : expr) : expr → bool 
-- | `(%%x → %%y) := (x = dx) && (is_pred_type y)
-- | x            := x = `(Prop)
-- 
-- meta def is_func (dx x : expr) : tactic bool :=
-- do y ← infer_type x, return $ is_func_type dx y
-- 
-- meta def is_pred (dx x : expr) : tactic bool :=
-- do y ← infer_type x,
--    return $ is_pred_type dx y
-- 
-- meta def is_int_term (x : expr) : tactic bool :=
-- do tx ← infer_type x, 
--    return $ `(int).to_expr = tx

--meta def is_eq (x : expr) : tactic bool :=
--do `(_ = _) ← infer_type x | return ff,
--   return tt
--
--meta def is_le (x : expr) : tactic bool :=
--do `(_ ≤ _) ← infer_type x | return ff,
--   return tt