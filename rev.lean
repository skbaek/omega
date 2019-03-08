import .tactic

open expr tactic

meta def revert_cond (t : expr → tactic bool) (x : expr) : tactic unit :=
mcond (t x) (revert x >> skip) skip 

meta def revert_cond_all (t : expr → tactic bool) : tactic unit :=
do hs ← local_context, mmap (revert_cond t) hs, skip

meta def is_hyp (x : expr) : tactic bool :=
infer_type x >>= is_prop

meta def rev_hyps : tactic unit :=
revert_cond_all is_hyp >> skip

meta def has_type (tx x : expr) : tactic bool := 
do sx ← infer_type x, return (sx = tx)

meta def is_func_type (dx : expr) : expr → bool 
| `(%%x → %%y) := (x = dx) && (is_func_type y)
| x            := x = dx
meta def is_pred_type (dx : expr) : expr → bool 
| `(%%x → %%y) := (x = dx) && (is_pred_type y)
| x            := x = `(Prop)

meta def is_func (dx x : expr) : tactic bool :=
do y ← infer_type x, return $ is_func_type dx y

meta def is_pred (dx x : expr) : tactic bool :=
do y ← infer_type x,
   return $ is_pred_type dx y

meta def is_int (x : expr) : tactic bool :=
do tx ← infer_type x, 
   return $ `(int).to_expr = tx

meta def is_eq (x : expr) : tactic bool :=
do `(_ = _) ← infer_type x | return ff,
   return tt

meta def is_le (x : expr) : tactic bool :=
do `(_ ≤ _) ← infer_type x | return ff,
   return tt
    
meta def rev : tactic unit :=
do revert_cond_all is_hyp,
   revert_cond_all is_int
