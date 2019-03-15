import .tactic

open tactic

meta def is_hyp (x : expr) : tactic bool :=
infer_type x >>= is_prop

meta def is_int (x : expr) : tactic bool :=
if x = `(int) then return tt
else if x = `(nat) then return ff
     else failed

meta def is_lia_form : expr → tactic bool
| `(true)  := failed
| `(false) := failed
| `(¬ %%px)      := is_lia_form px
| `(%%px ∨ %%qx) := is_lia_form px <|> is_lia_form qx
| `(%%px ∧ %%qx) := is_lia_form px <|> is_lia_form qx
| `(%%px ↔ %%qx) := is_lia_form px <|> is_lia_form qx
| `(%%(expr.pi _ _ px qx)) := 
  (monad.cond 
    (if expr.has_var px then return tt else is_prop px)
    (is_lia_form px) (is_int px)) <|> 
  (is_lia_form qx)
| `(@Exists %%dx _) := is_int dx
| `(@has_lt.lt %%dx %%h _ _) := is_int dx
| `(@has_le.le %%dx %%h _ _) := is_int dx
| `(@eq %%dx _ _) := is_int dx
| `(@ge %%dx %%h _ _) := is_int dx
| `(@gt %%dx %%h _ _) := is_int dx
| `(@ne %%dx _ _) := is_int dx
| _ := fail "Domain is not ℤ or ℕ"
  
meta def is_lia_goal_aux : list expr → tactic bool 
| []      := failed 
| (x::xs) := is_lia_form x <|> is_lia_goal_aux xs

meta def is_lia_goal : tactic bool :=
do gx ← target,
   hxs ← local_context >>= monad.filter is_hyp,
   is_lia_goal_aux (gx::hxs)