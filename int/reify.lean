import .form 
..tactic --.logic

open expr tactic

namespace int

meta def to_preterm : expr → tactic preterm 
| (expr.var k) := return (preterm.var 1 k)
| `(-%%(expr.var k)) := return (preterm.var (-1 : int) k)
| `(%%(expr.var k) * %%zx) := 
  do z ← eval_expr int zx, 
     return (preterm.var z k)
| `(%%t1x + %%t2x) := 
  do t1 ← to_preterm t1x, 
     t2 ← to_preterm t2x, 
     return (preterm.add t1 t2)
| zx := 
  do z ← eval_expr int zx,
     return (preterm.cst z)

meta def to_form : expr → tactic form 
| `(%%tx1 = %%tx2) := 
  do t1 ← to_preterm tx1, 
     t2 ← to_preterm tx2, 
     return (t1 =* t2)
| `(%%tx1 ≤ %%tx2) := 
  do t1 ← to_preterm tx1, 
     t2 ← to_preterm tx2, 
     return (t1 ≤* t2)
| `(¬ %%px) := do p ← to_form px, return (¬* p)
| `(%%px ∨ %%qx) := 
  do p ← to_form px, 
     q ← to_form qx, 
     return (p ∨* q)
| `(%%px ∧ %%qx) := 
  do p ← to_form px, 
     q ← to_form qx, 
     return (p ∧* q)
| `(_ → %%px) := to_form px
| _ := failed

meta def reify : tactic unit :=
do gx ← target,
   p ← to_form gx, 
   x ← to_expr ``(form.uniclo %%`(p)),
   to_expr ``(imp_of_imp %%x) >>= apply, 
   intro_fresh >>= apply,
   skip

end int