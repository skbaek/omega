import .is_lia .int.main .nat.main

meta def omega : tactic unit := 
monad.cond is_lia_goal int.omega nat.omega 


