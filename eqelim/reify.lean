import .univ_close ..logic ..preterm

open tactic

meta def get_preterm : expr → tactic preterm 
| (expr.var k) := return (preterm.var 1 k)
| `(-%%(expr.var k)) := return (preterm.var (-1 : int) k)
| `(%%(expr.var k) * %%zx) := 
  do z ← eval_expr int zx, 
     return (preterm.var z k)
| `(%%t1x + %%t2x) := 
  do t1 ← get_preterm t1x, 
     t2 ← get_preterm t2x, 
     return (preterm.add t1 t2)
| zx := 
  do z ← eval_expr int zx,
     return (preterm.cst z)

def preatom := preterm × preterm
def preclause := (list preatom) × (list preatom)

meta def get_eq_preatoms : expr → tactic (list preatom) 
| `((@eq int %%tx %%sx) ∧ %%px) := 
  do t ← get_preterm tx,
     s ← get_preterm sx,
     eqs ← get_eq_preatoms px,
     return ((t,s)::eqs)
| `(true) := return ([] : list preatom)
| _ := failed
    
meta def get_le_preatoms : expr → tactic (list preatom) 
| `((@has_le.le int _ %%tx %%sx) ∧ %%px) := 
  do t ← get_preterm tx,
     s ← get_preterm sx,
     eqs ← get_le_preatoms px,
     return ((t,s)::eqs)
| `(true) := return ([] : list preatom)
| _ := failed
    
meta def get_preatoms : nat → expr → tactic (nat × list preatom × list preatom) 
| m `(¬(%%px ∧ %%qx)) := 
  do eqs ← get_eq_preatoms px,
     les ← get_le_preatoms qx,
    return (m,eqs,les)
| m `(_ → %%px) := get_preatoms (m+1) px
| _ _ := failed


def assign_zero (i) (v : nat → int) : nat → int 
| 0     := i
| (m+1) := v m


def eqs_hold (v : nat → int) : list preatom → Prop 
| []           := true 
| ((t,s)::eqs) := (t.val v = s.val v) ∧ (eqs_hold eqs)

def les_hold (v : nat → int) : list preatom → Prop 
| []           := true 
| ((t,s)::les) := (t.val v ≤ s.val v) ∧ (les_hold les)

@[reducible] def uniclo (eqs les : list preatom) : nat → (nat → int) → Prop 
| 0     v := ¬(eqs_hold v eqs ∧ les_hold v les)
| (k+1) v := ∀ i : int, uniclo k (assign_zero i v) 


meta def reify : tactic unit :=
do gx ← target,
   (m,eqs,les) ← get_preatoms 0 gx,
   to_expr ``(imp_of_imp (uniclo %%`(eqs) %%`(les) %%`(m) (λ _, 0)) (λ h, h) _) >>= apply, 
   skip




#exit
open expr tactic

open tactic 

meta def get_preterm : expr → tactic preterm 
| (expr.var k) := return (preterm.var 1 k)
| `(-%%(expr.var k)) := return (preterm.var (-1 : int) k)
| `(%%(expr.var k) * %%zx) := 
  do z ← eval_expr int zx, 
     return (preterm.var z k)
| `(%%t1x + %%t2x) := 
  do t1 ← get_preterm t1x, 
     t2 ← get_preterm t2x, 
     return (preterm.add t1 t2)
| zx := 
  do z ← eval_expr int zx,
     return (preterm.cst z)

     #exit

meta def form.reify : expr → tactic form 
| `(%%tx1 = %%tx2) := 
  do t1 ← get_preterm tx1, 
     t2 ← get_preterm tx2, 
     return (t1 =* t2)
| `(%%tx1 ≤ %%tx2) := 
  do t1 ← get_preterm tx1, 
     t2 ← get_preterm tx2, 
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
  do t1 ← get_preterm tx1, 
     t2 ← get_preterm tx2,
     return ((t1,t2),x)
| _ := failed

meta def get_le : expr → tactic ((preterm × preterm) × expr) 
| `((%%tx1 ≤ %%tx2) → %%x) := 
  do t1 ← get_preterm tx1, 
     t2 ← get_preterm tx2,
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

