import .form .tactic .logic

open expr tactic

open tactic 

meta def preterm.reify : expr → tactic preterm 
| (expr.var k) := return (preterm.var 1 k)
| `(-%%(expr.var k)) := return (preterm.var (-1 : int) k)
| `(%%(expr.var k) * %%zx) := 
  do z ← eval_expr int zx, 
     return (preterm.var z k)
| `(%%t1x + %%t2x) := 
  do t1 ← preterm.reify t1x, 
     t2 ← preterm.reify t2x, 
     return (preterm.add t1 t2)
| zx := 
  do z ← eval_expr int zx,
     return (preterm.cst z)

meta def form.reify : expr → tactic form 
| `(%%tx1 = %%tx2) := 
  do t1 ← preterm.reify tx1, 
     t2 ← preterm.reify tx2, 
     return (t1 =* t2)
| `(%%tx1 ≤ %%tx2) := 
  do t1 ← preterm.reify tx1, 
     t2 ← preterm.reify tx2, 
     return (t1 ≤* t2)
| `(¬ %%px) := do p ← form.reify px, return (¬* p)
| `(%%px ∨ %%qx) := 
  do p ← form.reify px, 
     q ← form.reify qx, 
     return (p ∨* q)
| `(%%px ∧ %%qx) := 
  do p ← form.reify px, 
     q ← form.reify qx, 
     return (p ∧* q)
| `(_ → %%px) := form.reify px
| _ := failed


meta def reify : tactic unit :=
do gx ← target,
   p ← form.reify gx, 
   x ← to_expr ``(form.uniclo %%`(p)),
   to_expr ``(imp_of_imp %%x) >>= apply, 
   intro_fresh >>= apply,
   skip

#exit



















































meta def get_eq : expr → tactic ((preterm × preterm) × expr) 
| `((%%tx1 = %%tx2) → %%x) := 
  do t1 ← preterm.reify tx1, 
     t2 ← preterm.reify tx2,
     return ((t1,t2),x)
| _ := failed

meta def get_le : expr → tactic ((preterm × preterm) × expr) 
| `((%%tx1 ≤ %%tx2) → %%x) := 
  do t1 ← preterm.reify tx1, 
     t2 ← preterm.reify tx2,
     return ((t1,t2),x)
| _ := failed

meta def remove_quant : expr → tactic expr 
| (pi _ _ x y) :=
  monad.cond 
   (if x.has_var then return true else is_prop x)
   failed
   (return y)
| _ := failed

meta def get_prelincons_2 : expr → tactic prelincons 
| `(false) := return []
| x := 
  do (le,y) ← get_le x, 
     les ← get_prelincons_2 (y.lower_vars 1 1),
     return (le::les)

meta def get_prelincons_1 :
   expr → tactic (prelincons × prelincons) 
| x :=
  (do (eq,y) ← get_eq x, 
      (eqs,les) ← get_prelincons_1 (y.lower_vars 1 1),
      return (eq::eqs,les)) <|>
  (do les ← get_prelincons_2 x, return ([],les))

meta def get_prelincons_0 : expr → tactic (prelincons × prelincons) 
| x := (remove_quant x >>= get_prelincons_0) <|> (get_prelincons_1 x)

