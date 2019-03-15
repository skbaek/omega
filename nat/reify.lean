import .form ..tactic

open expr tactic

namespace nat

meta def to_preterm : expr → tactic preterm 
| (expr.var k) := return (preterm.var 1 k)
| `(%%(expr.var k) * %%mx) := 
  do m ← eval_expr nat mx, 
     return (preterm.var m k)
| `(%%t1x + %%t2x) := 
  do t1 ← to_preterm t1x, 
     t2 ← to_preterm t2x, 
     return (preterm.add t1 t2)
| `(%%t1x - %%t2x) := 
  do t1 ← to_preterm t1x, 
     t2 ← to_preterm t2x, 
     return (preterm.sub t1 t2)
| mx := 
  do m ← eval_expr nat mx,
     return (preterm.cst m)

meta def to_form_core : expr → tactic form 
| `(%%tx1 = %%tx2) := 
  do t1 ← to_preterm tx1, 
     t2 ← to_preterm tx2, 
     return (t1 =* t2)
| `(%%tx1 ≤ %%tx2) := 
  do t1 ← to_preterm tx1, 
     t2 ← to_preterm tx2, 
     return (t1 ≤* t2)
| `(¬ %%px) := do p ← to_form_core px, return (¬* p)
| `(%%px ∨ %%qx) := 
  do p ← to_form_core px, 
     q ← to_form_core qx, 
     return (p ∨* q)
| `(%%px ∧ %%qx) := 
  do p ← to_form_core px, 
     q ← to_form_core qx, 
     return (p ∧* q)
| `(_ → %%px) := to_form_core px
| _ := failed

meta def to_form : nat → expr → tactic (form × nat) 
| m `(_ → %%px) := to_form (m+1) px
| m x := do p ← to_form_core x, return (p,m)

end nat