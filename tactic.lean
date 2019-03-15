open tactic

meta def revert_cond (t : expr → tactic bool) (x : expr) : tactic unit :=
mcond (t x) (revert x >> skip) skip 

meta def revert_cond_all (t : expr → tactic bool) : tactic unit :=
do hs ← local_context, mmap (revert_cond t) hs, skip
