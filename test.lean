import .int
import tactic.norm_num
import order.basic


#check int.add_lt_iff_lt_sub

#exit

meta def lt_proof (i j : int) : tactic expr :=

| -[1+ m] 0 := return `(neg_succ_lt_zero %%`(m))
| _ _ := failed

#exit

example : (-5 : int) < 0 := by do 
x ← lt_proof (-5) 0,
    trace "hello",
    apply x

#exit
meta def prove_lt' (simp : expr → tactic (expr × expr)) : instance_cache → int → int → tactic (instance_cache × expr)
| c -[1+ m] -[1+ n] := do
  (c, p) ← prove_lt' c e₁ e₂,
  (c, p) ← c.mk_app ``neg_lt_neg [e₁, e₂, p],
  return (c, p)
| c `(- %%e₁) `(has_zero.zero _) := do
  trace 1,
  (c, p) ← prove_pos c e₁,
  trace 1,
  (c, p) ← c.mk_app ``neg_neg_of_pos [e₁, p],
  return (c, p)
| c `(- %%e₁) e₂ := do
  trace 2,
  (c, p₁) ← prove_pos c e₁,
  (c, me₁) ← c.mk_app ``has_neg.neg [e₁],
  (c, p₁) ← c.mk_app ``neg_neg_of_pos [e₁, p₁],
  (c, p₂) ← prove_pos c e₂,
  (c, z) ← c.mk_app ``has_zero.zero [],
  (c, p) ← c.mk_app ``lt_trans [me₁, z, e₂, p₁, p₂],
  return (c, p)
| c `(has_zero.zero _) e₂ := prove_pos c e₂
| c e₁ e₂ := do
  trace 3,
  n₁ ← e₁.to_rat, 
  trace 4,
  n₂ ← e₂.to_rat,
  d ← expr.of_rat c.α (n₂ - n₁),
  (c, e₃) ← c.mk_app ``has_add.add [e₁, d],
  (e₂', p) ← norm_num e₃,
  guard (e₂' =ₐ e₂),
  (c, p') ← prove_pos c d,
  (c, p) ← c.mk_app ``norm_num.lt_add_of_pos_helper [e₁, d, e₂, p, p'],
  return (c, p)

#exit


meta def prove_lt_int (i j : int) : tactic expr := 
do intx ← tactic.mk_instance_cache `(int),
   trace 0,
   (c,x) ← prove_lt' derive intx `(i).to_expr `(j).to_expr,
   return x
