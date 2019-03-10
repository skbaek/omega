/- I'm going to define my own wrapper monad around `tactic`. 
Maybe this is a bad idea. But it will give me practice with typeclasses in Lean so it won't be a waste of time -/
import .ee
open tactic expr 
universe u


#exit
| (eq::eqs) les := 
  do (n,eq') ← factor eq,
     failed
  -- match eq.factor with 
  -- | none := failed
  -- | some (n,eq') :=  
  --   do e ← elim_eq eq' eqs les, 
  --      return (ee.factor ↑n e)
  -- end

    

end ee